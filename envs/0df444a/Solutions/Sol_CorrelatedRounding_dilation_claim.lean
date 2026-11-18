-- Prove2me | solution 1 for CorrelatedRounding.dilation_claim
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T21:20:49.001242+00:00
-- url     : https://prove2.me/submissions/581c49bd-4f73-4d1d-8a05-92b22e27e575

import Mathlib
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_y
import Definitions.Def_CorrelatedRounding_clock
import Definitions.Def_CorrelatedRounding_IsAlg1Output
import Definitions.Def_CorrelatedRounding_IsAlg1Draw

open MeasureTheory ProbabilityTheory

namespace DilAux
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

end DilAux

open CorrelatedRounding in
theorem solution {q K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
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
    have hyk : 0 < y u k := lt_of_lt_of_le k.2 (DilAux.y_ge u k i)
    obtain ⟨hm, hmap⟩ := hlaw k hyk
    refine ⟨(measurable_const.mul measurable_id).comp_aemeasurable hm, ?_⟩
    have : (fun ω => y u k / u k i * E k ω) = (fun x => y u k / u k i * x) ∘ E k := rfl
    rw [this, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hm, hmap,
      DilAux.exp_scale _ _ hyk (div_pos hyk k.2)]
    congr 1
    field_simp
