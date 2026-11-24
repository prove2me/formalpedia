-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.lengthBaseChangeLocal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:48:54.535155+00:00
-- url     : https://prove2.me/submissions/1e0d1dfe-317c-43b0-b414-eae371eff89e

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_LengthBaseChangeLocal
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_LengthBaseChangeAlt_length_baseChange_eq_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module TensorProduct
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : LengthBaseChangeLocal := by
  intro O O₁ Q _ _ _ _ _ _ _ _ _ ϖ ϖ₁ u ε hϖ hϖ₁ hu hQ
  have hinj : Function.Injective (algebraMap O O₁) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨k, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    rw [map_mul, map_pow, hu] at hx
    rcases mul_eq_zero.1 hx with h | h
    · exact ((v.isUnit.map (algebraMap O O₁)).ne_zero) h
    · exact (pow_ne_zero _ (mul_ne_zero u.ne_zero (pow_ne_zero _ hϖ₁.ne_zero))) h
  have : Module.IsTorsionFree O O₁ := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  have : Module.Flat O O₁ := inferInstance
  rw [Module.length_ne_top_iff] at hQ
  refine LengthBaseChangeAlt.length_baseChange_eq_mul (ε : ℕ∞) ?_ Q hQ
  intro S _ _ hS
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hS
  obtain rfl := IsLocalRing.eq_maximalIdeal hm
  rw [(TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl O₁ O₁) e).length_eq,
    ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot O₁
      (IsLocalRing.maximalIdeal O)).toLinearEquiv.length_eq,
    hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hu]
  change Ring.ord O₁ _ = _
  rw [Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ₁]
  simp
end Formalism.LatticeBaseChangeAlt
