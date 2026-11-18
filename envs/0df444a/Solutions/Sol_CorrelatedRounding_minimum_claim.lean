-- Prove2me | solution 1 for CorrelatedRounding.minimum_claim
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T21:23:15.918232+00:00
-- url     : https://prove2.me/submissions/0d621f2b-a004-464a-bf62-7958e3529f79

import Mathlib
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_y
import Definitions.Def_CorrelatedRounding_clock
import Definitions.Def_CorrelatedRounding_IsAlg1Output
import Definitions.Def_CorrelatedRounding_IsAlg1Draw

open MeasureTheory ProbabilityTheory

namespace MinAux
open CorrelatedRounding

lemma y_ge {q K : ℕ} (u : Fin K → Fin q → ℝ) (k : Fin K) (i : Fin q) : u k i ≤ y u k :=
  le_ciSup (Set.finite_range _).bddAbove i

lemma exp_scale (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    (expMeasure r).map (fun x => c * x) = expMeasure (r / c) := by
  haveI := isProbabilityMeasure_expMeasure hr
  haveI := isProbabilityMeasure_expMeasure (div_pos hr hc)
  haveI : IsProbabilityMeasure ((expMeasure r).map (fun x => c * x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine Measure.ext_of_Iic _ _ (fun a => ?_)
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  have hpre : (fun x => c * x) ⁻¹' Set.Iic a = Set.Iic (a / c) := by
    ext x; simp only [Set.mem_preimage, Set.mem_Iic]; rw [le_div_iff₀ hc, mul_comm]
  rw [hpre, ← ofReal_cdf, ← ofReal_cdf, cdf_expMeasure_eq hr, cdf_expMeasure_eq (div_pos hr hc)]
  congr 1
  by_cases ha : 0 ≤ a
  · rw [if_pos (div_nonneg ha hc.le), if_pos ha]
    congr 3; field_simp
  · rw [if_neg (not_le.mpr (div_neg_of_neg_of_pos (not_le.mp ha) hc)), if_neg ha]

lemma dil {q K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {u : Fin K → Fin q → ℝ} (hu : IsInstance u) {E : Fin K → Ω → ℝ}
    (hE : IsAlg1Draw u μ E) (i : Fin q) :
    iIndepFun (fun (k : {k : Fin K // 0 < u k i}) (ω : Ω) => y u k / u k i * E k ω) μ ∧
      ∀ k : {k : Fin K // 0 < u k i},
        HasLaw (fun ω => y u k / u k i * E k ω) (expMeasure (u k i)) μ := by
  obtain ⟨hind, hlaw⟩ := hE
  constructor
  · have h1 := hind.precomp (g := fun k : {k : Fin K // 0 < u k i} => (k : Fin K))
      Subtype.val_injective
    exact h1.comp (fun k (x : ℝ) => y u k / u k i * x) (fun k => by fun_prop)
  · intro k
    have hyk : 0 < y u k := lt_of_lt_of_le k.2 (y_ge u k i)
    obtain ⟨hm, hmap⟩ := hlaw k hyk
    refine ⟨(measurable_const.mul measurable_id).comp_aemeasurable hm, ?_⟩
    have : (fun ω => y u k / u k i * E k ω) = (fun x => y u k / u k i * x) ∘ E k := rfl
    rw [this, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hm, hmap,
      exp_scale _ _ hyk (div_pos hyk k.2)]
    congr 1
    field_simp

lemma exp_Ioi (r a : ℝ) (hr : 0 < r) :
    expMeasure r (Set.Ioi a) = ENNReal.ofReal (if 0 ≤ a then Real.exp (-(r * a)) else 1) := by
  haveI := isProbabilityMeasure_expMeasure hr
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf, cdf_expMeasure_eq hr]
  split_ifs with ha
  · have he : 0 ≤ Real.exp (-(r * a)) := (Real.exp_pos _).le
    have he1 : Real.exp (-(r * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [ENNReal.ofReal_sub 1 he, ENNReal.ofReal_one]
    exact ENNReal.sub_sub_cancel ENNReal.one_ne_top (by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal he1)
  · simp

lemma exp_Ici (r t : ℝ) : expMeasure r (Set.Ici t) = expMeasure r (Set.Ioi t) := by
  apply le_antisymm
  · have hs : expMeasure r {t} = 0 := by
      unfold expMeasure gammaMeasure
      exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)
    calc expMeasure r (Set.Ici t) ≤ expMeasure r (Set.Ioi t ∪ {t}) := by
          apply measure_mono; intro x hx
          rcases eq_or_lt_of_le (Set.mem_Ici.mp hx) with h | h
          · right; exact h.symm
          · left; exact h
      _ ≤ expMeasure r (Set.Ioi t) + expMeasure r {t} := measure_union_le _ _
      _ = expMeasure r (Set.Ioi t) := by rw [hs, add_zero]
  · exact measure_mono Set.Ioi_subset_Ici_self

end MinAux

open CorrelatedRounding in
theorem solution {q K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {u : Fin K → Fin q → ℝ} (hu : IsInstance u) {E : Fin K → Ω → ℝ}
    (hE : IsAlg1Draw u μ E) (i : Fin q) :
    HasLaw (fun ω => ⨅ k : {k : Fin K // 0 < u k i}, y u k / u k i * E k ω) (expMeasure 1) μ ∧
      ∀ t : ℝ, 0 ≤ t →
        μ {ω | ∀ k, (t : EReal) ≤ clock u (fun k' => E k' ω) k i} =
          ENNReal.ofReal (Real.exp (-t)) := by
  classical
  obtain ⟨hind, hlaw⟩ := MinAux.dil hu hE i
  set Z : {k : Fin K // 0 < u k i} → Ω → ℝ := fun k ω => y u k / u k i * E k ω with hZ
  have hsum : ∑ k : {k : Fin K // 0 < u k i}, u k i = 1 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun k => 0 < u k i)) (p := fun k => 0 < u k i)
      (fun x => by simp) (fun k => u k i), Finset.sum_filter, ← hu.2 i]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs with h
    · rfl
    · exact (le_antisymm (not_lt.mp h) (hu.1 k i)).symm
  have hne : Nonempty {k : Fin K // 0 < u k i} := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  have hprod : ∀ a : ℝ, 0 ≤ a →
      ∏ k : {k : Fin K // 0 < u k i}, ENNReal.ofReal (Real.exp (-(u k i * a))) =
        ENNReal.ofReal (Real.exp (-a)) := by
    intro a ha
    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum]
    congr 2
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hsum, one_mul]
  have hind' := hind.measure_inter_preimage_eq_mul
  -- tails
  have tailIoi : ∀ a : ℝ, μ {ω | ∀ k, a < Z k ω} =
      ∏ k : {k : Fin K // 0 < u k i}, expMeasure (u k i) (Set.Ioi a) := by
    intro a
    have e : {ω | ∀ k, a < Z k ω} = ⋂ k ∈ (Finset.univ : Finset {k : Fin K // 0 < u k i}),
        Z k ⁻¹' Set.Ioi a := by ext ω; simp
    rw [e, hind' Finset.univ (fun _ _ => measurableSet_Ioi)]
    apply Finset.prod_congr rfl
    intro k _
    rw [← (hlaw k).map_eq, Measure.map_apply_of_aemeasurable (hlaw k).aemeasurable measurableSet_Ioi]
  have tailIci : ∀ a : ℝ, μ {ω | ∀ k, a ≤ Z k ω} =
      ∏ k : {k : Fin K // 0 < u k i}, expMeasure (u k i) (Set.Ici a) := by
    intro a
    have e : {ω | ∀ k, a ≤ Z k ω} = ⋂ k ∈ (Finset.univ : Finset {k : Fin K // 0 < u k i}),
        Z k ⁻¹' Set.Ici a := by ext ω; simp
    rw [e, hind' Finset.univ (fun _ _ => measurableSet_Ici)]
    apply Finset.prod_congr rfl
    intro k _
    rw [← (hlaw k).map_eq, Measure.map_apply_of_aemeasurable (hlaw k).aemeasurable measurableSet_Ici]
  have hmin : AEMeasurable (fun ω => ⨅ k, Z k ω) μ := AEMeasurable.iInf (fun k => (hlaw k).aemeasurable)
  constructor
  · refine ⟨hmin, ?_⟩
    haveI := Measure.isProbabilityMeasure_map (μ := μ) hmin
    haveI := isProbabilityMeasure_expMeasure (r := 1) one_pos
    have hIoi : ∀ a, (μ.map (fun ω => ⨅ k, Z k ω)) (Set.Ioi a) = expMeasure 1 (Set.Ioi a) := by
      intro a
      rw [Measure.map_apply_of_aemeasurable hmin measurableSet_Ioi]
      have e : (fun ω => ⨅ k, Z k ω) ⁻¹' Set.Ioi a = {ω | ∀ k, a < Z k ω} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq]
        constructor
        · intro h k
          exact lt_of_lt_of_le h (ciInf_le (Set.finite_range _).bddBelow k)
        · intro h
          obtain ⟨k0, hk0⟩ := exists_eq_ciInf_of_finite (f := fun k => Z k ω)
          rw [← hk0]; exact h k0
      rw [e, tailIoi, MinAux.exp_Ioi 1 a one_pos]
      simp_rw [fun k : {k : Fin K // 0 < u k i} => MinAux.exp_Ioi (u k i) a k.2]
      by_cases ha : 0 ≤ a
      · simp only [if_pos ha, one_mul]; exact hprod a ha
      · simp [if_neg ha]
    refine Measure.ext_of_Iic _ _ (fun a => ?_)
    rw [← Set.compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,
      prob_compl_eq_one_sub measurableSet_Ioi, hIoi]
  · intro t ht
    have e : {ω | ∀ k, (t : EReal) ≤ clock u (fun k' => E k' ω) k i} = {ω | ∀ k, t ≤ Z k ω} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h k
        have := h k.1
        unfold clock at this
        rw [if_neg (ne_of_gt k.2)] at this
        exact EReal.coe_le_coe_iff.mp this
      · intro h k
        unfold clock
        split_ifs with h0
        · exact le_top
        · have hk : 0 < u k i := lt_of_le_of_ne (hu.1 k i) (Ne.symm h0)
          exact EReal.coe_le_coe_iff.mpr (h ⟨k, hk⟩)
    rw [e, tailIci]
    simp_rw [MinAux.exp_Ici]
    simp_rw [fun k : {k : Fin K // 0 < u k i} => MinAux.exp_Ioi (u k i) t k.2, if_pos ht]
    exact hprod t ht
