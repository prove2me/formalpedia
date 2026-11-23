-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.extSpan_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:54.688266+00:00
-- url     : https://prove2.me/submissions/c0d517d4-847e-4e58-aee3-578efac01b16

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_P2M_Formalism_DivisionValues_FinitelyNonzeroLinear_map_mulVec__22fb7428e0b1
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_mem_extSpan

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
open Formalism.DivisionValues.FinitelyNonzeroLinear
variable {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω)
variable {j}
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution {n : ℕ} (Z : Submodule K (Fin n → K)) (e : Matrix (Fin n) (Fin n) K)
    (h1 : ∀ x, e *ᵥ x ∈ Z) (h2 : ∀ z ∈ Z, e *ᵥ z = z) :
    extSpan j Z = LinearMap.range (e.map j).mulVecLin := by
  apply le_antisymm
  · unfold extSpan
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_range]
    exact ⟨fun i => j (z i), by rw [Matrix.mulVecLin_apply, map_mulVec', h2 z hz]⟩
  · rintro _ ⟨y, rfl⟩
    have hcol : ∀ k, (fun i => j (e i k)) ∈ extSpan j Z := fun k => by
      have hz := h1 (Pi.single k 1)
      rw [Matrix.mulVec_single_one] at hz
      exact mem_extSpan hz
    have hy : (e.map j).mulVecLin y = ∑ k, y k • (fun i => j (e i k)) := by
      funext i
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hy]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hcol k)
end Formalism.DivisionValues.FinitelyNonzeroLinear
