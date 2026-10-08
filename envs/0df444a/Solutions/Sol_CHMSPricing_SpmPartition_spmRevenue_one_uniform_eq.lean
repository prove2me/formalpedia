-- Prove2me | solution 1 for CHMSPricing.SpmPartition.spmRevenue_one_uniform_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:50:26.169909+00:00
-- url     : https://prove2.me/submissions/5848bd0b-5b55-4ead-9d68-9d7f2ad5ac19

import Mathlib
import Definitions.Def_CHMSPricing_SpmPartition_ValueDist
import Definitions.Def_CHMSPricing_SpmPartition_SetSystem
import Definitions.Def_CHMSPricing_SpmPartition_Spm



namespace CHMSPricing.SpmPartition

open MeasureTheory Set

namespace SpmAux

variable (D : ValueDist)

lemma f_intOn : IntegrableOn D.f (Icc D.lo D.hi) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le D.lo_lt_hi.le).1 D.f_intervalIntegrable

lemma setInt_f : ∫ x in Icc D.lo D.hi, D.f x = 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le D.lo_lt_hi.le,
    D.f_integral]

lemma law_univ : D.law univ = 1 := by
  rw [ValueDist.law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (f_intOn D), setInt_f]
  · simp
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (D.f_pos x hx).le

instance law_prob : IsProbabilityMeasure D.law := ⟨law_univ D⟩

lemma law_ac : D.law ≪ volume.restrict (Icc D.lo D.hi) := withDensity_absolutelyContinuous _ _

lemma law_singleton (t : ℝ) : D.law {t} = 0 :=
  law_ac D (Measure.restrict_le_self.absolutelyContinuous (by simp))

lemma law_Iio (x : ℝ) : (D.law (Iio x)).toReal = D.cdf x := by
  rw [ValueDist.cdf, measure_congr (Iio_ae_eq_Iic' (law_singleton D x))]

lemma law_Ici (x : ℝ) : (D.law (Ici x)).toReal = 1 - D.cdf x := by
  rw [ValueDist.cdf, ← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, measure_congr (Iio_ae_eq_Iic' (law_singleton D x))]
  simp

end SpmAux

variable {n : ℕ}

instance prior_prob' {ι : Type*} [Fintype ι] (D : ι → ValueDist) : IsProbabilityMeasure (prior D) := by
  unfold prior; infer_instance

/-- characterization of the served set for the 1-uniform matroid -/
lemma served_one (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (m : ℕ) (hm : m ≤ n) :
    spmServedBefore (uniformSystem (Fin n) 1) σ p v m =
      (Finset.univ.filter (fun k : Fin n => k.val < m ∧ (∀ j, j < k → v (σ j) < p (σ j)) ∧
        p (σ k) ≤ v (σ k))).map σ.toEmbedding := by
  induction m with
  | zero => simp [spmServedBefore]
  | succ m ih =>
    have hmn : m < n := hm
    have ih := ih hmn.le
    have htake : (List.finRange n).take (m+1) = (List.finRange n).take m ++ [⟨m, hmn⟩] := by
      rw [List.take_add_one]
      congr 1
      simp [hmn]
    unfold spmServedBefore at ih ⊢
    rw [htake, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    set S := (Finset.univ.filter (fun k : Fin n => k.val < m ∧ (∀ j, j < k → v (σ j) < p (σ j)) ∧
        p (σ k) ≤ v (σ k))).map σ.toEmbedding with hS
    unfold spmStep
    ext x
    by_cases hE : ∀ j : Fin n, j < ⟨m, hmn⟩ → v (σ j) < p (σ j)
    · have hSe : S = ∅ := by
        rw [hS, Finset.map_eq_empty, Finset.filter_eq_empty_iff]
        rintro k - ⟨hk, -, hk2⟩
        have := hE k (Fin.mk_lt_mk.2 hk |> fun h => by simpa using h)
        linarith
      rw [hSe]
      split_ifs with hacc'
      · have hacc := hacc'.2
        simp only [Finset.mem_insert, Finset.notMem_empty, or_false, Finset.mem_map_equiv, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · rintro rfl
          refine ⟨by simp, fun j hj => hE j (by simpa using hj), by simpa using hacc⟩
        · rintro ⟨h1, h2, h3⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
          · have := hE (σ.symm x) (by exact h)
            simp at this h3; linarith
          · have : σ.symm x = ⟨m, hmn⟩ := Fin.ext h
            rw [← this]; simp
      · have hacc : ¬ p (σ ⟨m, hmn⟩) ≤ v (σ ⟨m, hmn⟩) := fun h =>
          hacc' ⟨by simp [uniformSystem], h⟩
        simp only [Finset.notMem_empty, false_iff, Finset.mem_map_equiv, Finset.mem_filter,
          Finset.mem_univ, true_and, not_and]
        intro h1 h2 h3
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
        · have := hE (σ.symm x) (by exact h)
          simp at this h3; linarith
        · have : σ.symm x = ⟨m, hmn⟩ := Fin.ext h
          rw [this] at h3; exact hacc h3
    · push_neg at hE
      obtain ⟨j0, hj0, hj0'⟩ := hE
      have hj0m : j0.val < m := hj0
      -- S is nonempty, so inserting a new element exceeds capacity
      have hnot : ¬ ((uniformSystem (Fin n) 1).Feasible (insert (σ ⟨m, hmn⟩) S) ∧
          p (σ ⟨m, hmn⟩) ≤ v (σ ⟨m, hmn⟩)) := by
        rintro ⟨hc, -⟩
        change (insert (σ ⟨m, hmn⟩) S).card ≤ 1 at hc
        -- find the first accepted index
        classical
        let T := Finset.univ.filter (fun k : Fin n => p (σ k) ≤ v (σ k))
        have hT : T.Nonempty := ⟨j0, by simp [T, hj0']⟩
        let k0 := T.min' hT
        have hk0T : k0 ∈ T := T.min'_mem hT
        have hk0le : k0 ≤ j0 := T.min'_le j0 (by simp [T, hj0'])
        have hk0S : σ k0 ∈ S := by
          rw [hS, Finset.mem_map_equiv]
          simp only [Equiv.symm_apply_apply, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨lt_of_le_of_lt (Fin.le_def.1 hk0le) hj0m, fun j hj => ?_, by simpa [T] using hk0T⟩
          by_contra hc'
          push_neg at hc'
          have := T.min'_le j (by simp [T, hc'])
          exact absurd hj (not_lt.2 this)
        have hne : σ ⟨m, hmn⟩ ≠ σ k0 := by
          intro h
          have := σ.injective h
          have : k0.val = m := by rw [← this]
          omega
        have : ({σ ⟨m, hmn⟩, σ k0} : Finset (Fin n)) ⊆ insert (σ ⟨m, hmn⟩) S := by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem hk0S
        have := Finset.card_le_card this
        rw [Finset.card_pair hne] at this
        omega
      rw [if_neg hnot]
      simp only [hS, Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨Nat.lt_succ_of_lt h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨?_, h2, h3⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
        · exact h
        · exfalso
          have := h2 j0 (by rw [Fin.lt_def, h]; exact hj0m)
          linarith

lemma mem_served_one (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (k : Fin n) :
    σ k ∈ spmServed (uniformSystem (Fin n) 1) σ p v ↔
      (∀ j, j < k → v (σ j) < p (σ j)) ∧ p (σ k) ≤ v (σ k) := by
  rw [spmServed, served_one σ p v n le_rfl, Finset.mem_map_equiv]
  simp

lemma served_set_eq (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (k : Fin n) :
    {v : Fin n → ℝ | σ k ∈ spmServed (uniformSystem (Fin n) 1) σ p v} =
      univ.pi (fun i => if σ.symm i < k then Iio (p i) else if σ.symm i = k then Ici (p i)
        else univ) := by
  ext v
  simp only [mem_setOf_eq, mem_served_one, mem_pi, mem_univ, true_implies]
  constructor
  · rintro ⟨h1, h2⟩ i
    split_ifs with ha hb
    · have := h1 _ ha; simpa using this
    · rw [← hb] at h2; simpa using h2
    · trivial
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have := h (σ j); simp only [Equiv.symm_apply_apply, if_pos hj] at this; exact this
    · have := h (σ k); simp only [Equiv.symm_apply_apply, lt_irrefl, if_false, if_true] at this
      exact this

theorem spm1_core (D : Fin n → ValueDist)
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) :
    spmRevenue D (uniformSystem (Fin n) 1) σ p =
      ∑ k : Fin n, oneUnitOfferProb (fun j => 1 - (D (σ j)).cdf (p (σ j))) k *
        p (σ k) * (1 - (D (σ k)).cdf (p (σ k))) := by
  have hprob : ∀ k : Fin n, (prior D {v | σ k ∈ spmServed (uniformSystem (Fin n) 1) σ p v}).toReal
      = oneUnitOfferProb (fun j => 1 - (D (σ j)).cdf (p (σ j))) k *
        (1 - (D (σ k)).cdf (p (σ k))) := by
    intro k
    rw [served_set_eq, prior, Measure.pi_pi, ENNReal.toReal_prod,
      ← Equiv.prod_comp σ]
    simp only [Equiv.symm_apply_apply]
    have : ∀ j : Fin n, ((D (σ j)).law (if j < k then Iio (p (σ j)) else if j = k then
        Ici (p (σ j)) else univ)).toReal = if j < k then (D (σ j)).cdf (p (σ j)) else
        if j = k then 1 - (D (σ j)).cdf (p (σ j)) else 1 := by
      intro j
      split_ifs
      · exact SpmAux.law_Iio _ _
      · exact SpmAux.law_Ici _ _
      · simp
    simp_rw [this]
    rw [Finset.prod_ite, oneUnitOfferProb]
    congr 1
    · refine Finset.prod_congr rfl (fun j _ => by ring)
    · rw [Finset.prod_ite_eq']
      simp
  have hsum : ∀ v : Fin n → ℝ, ∑ i ∈ spmServed (uniformSystem (Fin n) 1) σ p v, p i =
      ∑ k : Fin n, {v | σ k ∈ spmServed (uniformSystem (Fin n) 1) σ p v}.indicator
        (fun _ => p (σ k)) v := by
    intro v
    have hA : spmServed (uniformSystem (Fin n) 1) σ p v =
        Finset.univ.filter (· ∈ spmServed (uniformSystem (Fin n) 1) σ p v) := by ext; simp
    rw [hA, Finset.sum_filter, ← Equiv.sum_comp σ]
    simp [Set.indicator]
  have hmeas : ∀ k : Fin n,
      MeasurableSet {v : Fin n → ℝ | σ k ∈ spmServed (uniformSystem (Fin n) 1) σ p v} := by
    intro k
    rw [served_set_eq]
    refine MeasurableSet.univ_pi (fun i => ?_)
    split_ifs
    · exact measurableSet_Iio
    · exact measurableSet_Ici
    · exact MeasurableSet.univ
  unfold spmRevenue
  simp_rw [hsum]
  rw [integral_finset_sum _ (fun k _ => (integrable_const _).indicator (hmeas k))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_indicator_const _ (hmeas k), measureReal_def, smul_eq_mul, hprob]
  ring

end CHMSPricing.SpmPartition

open CHMSPricing.SpmPartition


theorem solution {n : ℕ} (D : Fin n → ValueDist)
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) :
    spmRevenue D (uniformSystem (Fin n) 1) σ p =
      ∑ k : Fin n, oneUnitOfferProb (fun j => 1 - (D (σ j)).cdf (p (σ j))) k *
        p (σ k) * (1 - (D (σ k)).cdf (p (σ k))) := by
  exact spm1_core D σ p
