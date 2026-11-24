-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gram_matrix_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:54.613001+00:00
-- url     : https://prove2.me/submissions/398d17da-7f14-4cbd-935e-bc1179f0e42f

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductPlacesInequalitySq
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LocalIntegralStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure nonZeroDivisors
set_option linter.all false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Matrix Polynomial
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : GramNondeg := by
  intro K V ι _ _ _ _ _ σ B v hdet
  have right : ∀ c : ι → K, (∀ j, B (v j) (∑ i, c i • v i) = 0) → c = 0 := by
    intro c hc
    have h1 : (Matrix.of fun i j => B (v i) (v j)).mulVec (fun i => σ (c i)) = 0 := by
      funext j
      have hj := hc j
      rw [map_sum] at hj
      simp only [LinearMap.map_smulₛₗ, smul_eq_mul] at hj
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
      rw [← hj]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hdet h1
    funext i
    have h3 := congrFun h2 i
    simp only [Pi.zero_apply] at h3
    exact (map_eq_zero σ).1 h3
  have left : ∀ c : ι → K, (∀ j, B (∑ i, c i • v i) (v j) = 0) → c = 0 := by
    intro c hc
    have h1 : Matrix.vecMul c (Matrix.of fun i j => B (v i) (v j)) = 0 := by
      funext j
      have hj := hc j
      rw [map_sum, LinearMap.sum_apply] at hj
      simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul] at hj
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
      exact hj
    exact Matrix.eq_zero_of_vecMul_eq_zero hdet h1
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg0 := right g (fun j => by rw [hg, map_zero])
    intro i
    exact congrFun hg0 i
  refine ⟨hli, finrank_span_eq_card hli, ?_, ?_⟩
  · intro x hx hB
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    have hc := right c (fun j => hB (v j) (Submodule.subset_span ⟨j, rfl⟩))
    simp [hc]
  · intro x hx hB
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    have hc := left c (fun j => hB (v j) (Submodule.subset_span ⟨j, rfl⟩))
    simp [hc]
end Formalism.HermitianLatticeCounting.P
