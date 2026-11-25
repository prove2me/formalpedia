-- Prove2me | solution 1 for CorrelatedRounding.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-25T20:18:29.881857+00:00
-- url     : https://prove2.me/submissions/1ca8420f-7774-4320-941e-e4f07b5479dd

import Mathlib
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_y
import Definitions.Def_CorrelatedRounding_clock
import Definitions.Def_CorrelatedRounding_IsAlg1Output
import Definitions.Def_CorrelatedRounding_IsAlg1Draw
import Theorems.Thm_CorrelatedRounding_dilation_claim

open MeasureTheory ProbabilityTheory

namespace CRLemma1

open Set

lemma expMeasure_Ici_le {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    expMeasure r (Ici x) ≤ ENNReal.ofReal (Real.exp (-(r * x))) := by
  have := isProbabilityMeasure_expMeasure hr
  have hsing : expMeasure r {x} = 0 :=
    (withDensity_absolutelyContinuous _ _) (Real.volume_singleton)
  have hIoi : expMeasure r (Ioi x) = ENNReal.ofReal (Real.exp (-(r * x))) := by
    rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf,
      cdf_expMeasure_eq hr, if_pos hx, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (by
        have : Real.exp (-(r * x)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        linarith)]
    congr 1; ring
  calc expMeasure r (Ici x) ≤ expMeasure r (Ioi x ∪ {x}) := by
        apply measure_mono; intro t ht
        rcases eq_or_lt_of_le (show x ≤ t from ht) with h | h
        · right; exact h.symm
        · left; exact h
    _ ≤ expMeasure r (Ioi x) + expMeasure r {x} := measure_union_le _ _
    _ = _ := by rw [hsing, add_zero, hIoi]

/-- Competing exponentials: upper bound on the probability that `X k` is a minimum. -/
lemma competing_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Ω → ℝ} {r : ι → ℝ}
    (hind : iIndepFun X μ) (hlaw : ∀ j, HasLaw (X j) (expMeasure (r j)) μ)
    (hr : ∀ j, 0 < r j) (hsum : ∑ j, r j = 1) (k : ι) :
    μ {ω | ∀ j, X k ω ≤ X j ω} ≤ ENNReal.ofReal (r k) := by
  classical
  set T : Finset ι := Finset.univ.erase k with hT
  have hmeas : ∀ j, AEMeasurable (X j) μ := fun j => (hlaw j).aemeasurable
  have hInd0 := hind.indepFun_finset₀ {k} T (by simp [T]) hmeas
  let Y : Ω → (T → ℝ) := fun ω j => X j ω
  have hIndXY : IndepFun (X k) Y μ := by
    have := hInd0.comp
      (_mγ := inferInstance) (_mγ' := inferInstance)
      (φ := fun v : ({k} : Finset ι) → ℝ => v ⟨k, Finset.mem_singleton_self k⟩) (ψ := id)
      (by fun_prop) measurable_id
    exact this
  have hY : AEMeasurable Y μ := aemeasurable_pi_lambda _ (fun j => hmeas j)
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map (hmeas k) hY).1 hIndXY
  set B : Set (ℝ × (T → ℝ)) := {p | ∀ j : T, p.1 ≤ p.2 j} with hBdef
  have hB : MeasurableSet B := by
    have : B = ⋂ j : T, {p : ℝ × (T → ℝ) | p.1 ≤ p.2 j} := by ext p; simp [B]
    rw [this]
    exact MeasurableSet.iInter (fun j =>
      measurableSet_le measurable_fst ((measurable_pi_apply j).comp measurable_snd))
  have hset : {ω | ∀ j, X k ω ≤ X j ω} = (fun ω => (X k ω, Y ω)) ⁻¹' B := by
    ext ω
    simp only [Set.mem_preimage, B, Y]
    constructor
    · intro h j; exact h j
    · intro h j
      by_cases hj : j = k
      · subst hj; exact le_rfl
      · exact h ⟨j, by simp [T, hj]⟩
  have hXYm : AEMeasurable (fun ω => (X k ω, Y ω)) μ := (hmeas k).prodMk hY
  rw [hset, ← Measure.map_apply_of_aemeasurable hXYm hB, hmap, (hlaw k).map_eq, Measure.prod_apply hB]
  have hslice : ∀ x, 0 ≤ x →
      (μ.map Y) (Prod.mk x ⁻¹' B) ≤ ENNReal.ofReal (Real.exp (-((1 - r k) * x))) := by
    intro x hx
    have hS : MeasurableSet {v : T → ℝ | ∀ j, x ≤ v j} := by
      have : {v : T → ℝ | ∀ j, x ≤ v j} = ⋂ j : T, {v | x ≤ v j} := by ext v; simp
      rw [this]
      exact MeasurableSet.iInter (fun j => measurableSet_le measurable_const (measurable_pi_apply j))
    have hpre : Prod.mk x ⁻¹' B = {v : T → ℝ | ∀ j, x ≤ v j} := rfl
    rw [hpre, Measure.map_apply_of_aemeasurable hY hS]
    have h1 : Y ⁻¹' {v : T → ℝ | ∀ j, x ≤ v j} = ⋂ j ∈ T, X j ⁻¹' Ici x := by
      ext ω; simp [Y]
    rw [h1, hind.measure_inter_preimage_eq_mul T (fun j _ => measurableSet_Ici)]
    calc ∏ j ∈ T, μ (X j ⁻¹' Ici x) = ∏ j ∈ T, expMeasure (r j) (Ici x) := by
          refine Finset.prod_congr rfl (fun j _ => ?_)
          rw [← (hlaw j).map_eq, Measure.map_apply_of_aemeasurable (hmeas j) measurableSet_Ici]
      _ ≤ ∏ j ∈ T, ENNReal.ofReal (Real.exp (-(r j * x))) :=
          Finset.prod_le_prod' (fun j _ => expMeasure_Ici_le (hr j) hx)
      _ = ENNReal.ofReal (Real.exp (-((1 - r k) * x))) := by
          rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le), ← Real.exp_sum]
          have : ∑ j ∈ T, r j = 1 - r k := by
            rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]; ring
          rw [Finset.sum_neg_distrib, ← Finset.sum_mul, this]
  have hg : Measurable (fun x => (μ.map Y) (Prod.mk x ⁻¹' B)) :=
    measurable_measure_prodMk_left hB
  show ∫⁻ x, _ ∂(volume.withDensity (gammaPDF 1 (r k))) ≤ _
  rw [lintegral_withDensity_eq_lintegral_mul _
    (show Measurable (gammaPDF 1 (r k)) from (measurable_exponentialPDFReal (r k)).ennreal_ofReal) hg]
  calc ∫⁻ x, (gammaPDF 1 (r k) * fun x => (μ.map Y) (Prod.mk x ⁻¹' B)) x
        ≤ ∫⁻ x, ENNReal.ofReal (r k) * exponentialPDF 1 x := by
        refine lintegral_mono (fun x => ?_)
        simp only [Pi.mul_apply]
        rw [show gammaPDF 1 (r k) x = exponentialPDF (r k) x from rfl]
        rcases lt_or_ge x 0 with hx | hx
        · rw [exponentialPDF_of_neg hx, zero_mul]; simp
        · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx]
          calc _ ≤ ENNReal.ofReal (r k * Real.exp (-(r k * x))) *
                ENNReal.ofReal (Real.exp (-((1 - r k) * x))) := mul_le_mul_right (hslice x hx) _
            _ = _ := by
              rw [← ENNReal.ofReal_mul (by have := hr k; positivity),
                ← ENNReal.ofReal_mul (hr k).le, mul_assoc, ← Real.exp_add, one_mul]
              congr 3; ring
    _ = ENNReal.ofReal (r k) := by
        rw [lintegral_const_mul _
          (show Measurable (exponentialPDF 1) from (measurable_exponentialPDFReal 1).ennreal_ofReal),
          lintegral_exponentialPDF_eq_one one_pos, mul_one]

end CRLemma1

open CorrelatedRounding in
theorem solution {q K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {u : Fin K → Fin q → ℝ} (hu : IsInstance u) {E : Fin K → Ω → ℝ}
    (hE : IsAlg1Draw u μ E) {Z : Ω → Fin q → Fin K}
    (hZ : ∀ᵐ ω ∂μ, IsAlg1Output u (fun k => E k ω) (Z ω)) (i : Fin q) (k : Fin K) :
    μ {ω | Z ω i = k} = ENNReal.ofReal (u k i) := by
  classical
  set bad := {ω | ¬ IsAlg1Output u (fun k => E k ω) (Z ω)} with hbad
  have hbad0 : μ bad = 0 := ae_iff.1 hZ
  obtain ⟨hind, hlaw⟩ := dilation_claim hu hE i
  -- upper bound for every k
  have upper : ∀ k, μ {ω | Z ω i = k} ≤ ENNReal.ofReal (u k i) := by
    intro k
    rcases eq_or_lt_of_le (hu.1 k i) with h0 | hpos
    · -- u k i = 0
      have hex : ∃ j, u j i ≠ 0 := by
        by_contra hc
        push Not at hc
        have := hu.2 i
        simp [hc] at this
      obtain ⟨j, hj⟩ := hex
      have hsub : {ω | Z ω i = k} ⊆ bad := by
        intro ω hω hgood
        have h := hgood i j
        have hω' : Z ω i = k := hω
        rw [hω'] at h
        unfold clock at h
        rw [if_pos h0.symm, if_neg hj] at h
        exact absurd h (not_le.2 (EReal.coe_lt_top _))
      exact (measure_mono hsub).trans (by rw [hbad0]; simp)
    · let X : {k : Fin K // 0 < u k i} → Ω → ℝ := fun j ω => y u j / u j i * E j ω
      have hsum : ∑ j : {k : Fin K // 0 < u k i}, u j i = 1 := by
        rw [← hu.2 i, ← Finset.sum_subtype (Finset.univ.filter (fun k => 0 < u k i))
          (by simp) (fun k => u k i)]
        exact Finset.sum_filter_of_ne (fun x _ hx => lt_of_le_of_ne (hu.1 x i) (Ne.symm hx))
      have hsub : {ω | Z ω i = k} ⊆ bad ∪ {ω | ∀ j, X ⟨k, hpos⟩ ω ≤ X j ω} := by
        intro ω hω
        by_cases hgood : IsAlg1Output u (fun k => E k ω) (Z ω)
        · right
          intro j
          have h := hgood i j.1
          have hω' : Z ω i = k := hω
          rw [hω'] at h
          simp only [clock, if_neg hpos.ne', if_neg j.2.ne'] at h
          exact EReal.coe_le_coe_iff.1 h
        · left; exact hgood
      calc μ {ω | Z ω i = k} ≤ μ (bad ∪ {ω | ∀ j, X ⟨k, hpos⟩ ω ≤ X j ω}) := measure_mono hsub
        _ ≤ μ bad + μ {ω | ∀ j, X ⟨k, hpos⟩ ω ≤ X j ω} := measure_union_le _ _
        _ = μ {ω | ∀ j, X ⟨k, hpos⟩ ω ≤ X j ω} := by rw [hbad0, zero_add]
        _ ≤ ENNReal.ofReal (u k i) :=
          CRLemma1.competing_le (X := X) (r := fun j => u j.1 i) hind hlaw (fun j => j.2) hsum ⟨k, hpos⟩
  -- lower bound by summing
  have htot : (1 : ENNReal) ≤ ∑ k, μ {ω | Z ω i = k} := by
    rw [← measure_univ (μ := μ)]
    calc μ Set.univ = μ (⋃ k, {ω | Z ω i = k}) := by
          congr 1; ext ω; simp
      _ ≤ _ := measure_iUnion_fintype_le _ _
  have hsumu : ∑ k, ENNReal.ofReal (u k i) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hu.1 k i), hu.2 i, ENNReal.ofReal_one]
  refine le_antisymm (upper k) ?_
  by_contra hlt
  push Not at hlt
  have : ∑ k, μ {ω | Z ω i = k} < ∑ k, ENNReal.ofReal (u k i) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    exact ENNReal.add_lt_add_of_lt_of_le
      (ne_top_of_le_ne_top ENNReal.one_ne_top
        ((Finset.sum_le_sum (fun j _ => upper j)).trans
          (by rw [← hsumu]; exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _))))
      hlt (Finset.sum_le_sum (fun j _ => upper j))
  rw [hsumu] at this
  exact absurd htot (not_le.2 this)
