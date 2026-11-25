-- Prove2me | solution 1 for Formalism.DivisionValues.descent_cm_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:12:06.802861+00:00
-- url     : https://prove2.me/submissions/bc5c8c86-310a-4f94-80e7-226fae5612d3

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_mem_cmMax_iff_twist
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_exists_reduced
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_embSpan_span
import Theorems.Thm_Formalism_HN_twist


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open RationalHermitianForm
open ConjugateWeightGram
namespace Formalism.DivisionValues
theorem _root_.solution : DescentCM := by
  intro K _ _ _ n Z hZ
  classical
  obtain ⟨d, z, f, hli, hspan, hz⟩ := exists_reduced Z
  refine ⟨d, z, hli, hspan, fun a i => ?_⟩
  rw [mem_cmMax_iff_twist]
  intro σ
  set τ := twist σ with hτ

  have hmem : (fun i => σ (z a i) : Fin n → ℂ) ∈ embSpan τ Z := by
    rw [hτ, ← hZ σ]
    exact Submodule.subset_span ⟨z a, by rw [← hspan]; exact Submodule.subset_span ⟨a, rfl⟩, rfl⟩
  rw [← hspan, embSpan_span] at hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  have hcoef : ∀ k, c k = if a = k then 1 else 0 := by
    intro k
    have := congrFun hc (f k)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hz, apply_ite τ, apply_ite σ, map_one,
      map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact this
  have := congrFun hc i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcoef, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
  exact this
end Formalism.DivisionValues
