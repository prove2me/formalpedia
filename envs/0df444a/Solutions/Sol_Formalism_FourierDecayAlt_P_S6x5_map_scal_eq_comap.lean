-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x5.map_scal_eq_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:42.889023+00:00
-- url     : https://prove2.me/submissions/87e27a91-8706-44d5-bb96-44d95222aa9f

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_scalInv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x5
open Module MeasureTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace Formalism.FourierDecayAlt.P.S6x5
theorem _root_.solution (c : ℝ) (hc : c ≠ 0) (L : Submodule ℤ V) :
    L.map (scal V c) = ZLattice.comap ℝ L (scalInv V c hc).toLinearMap := by
  ext x
  simp only [Submodule.mem_map, ZLattice.comap, Submodule.mem_comap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : (scalInv V c hc) (c • y) = y := by rw [scalInv_apply, smul_smul, inv_mul_cancel₀ hc, one_smul]
    show (scalInv V c hc) (c • y) ∈ L
    rw [this]; exact hy
  · intro hx
    refine ⟨_, hx, ?_⟩
    show c • (scalInv V c hc) x = x
    rw [scalInv_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]
end Formalism.FourierDecayAlt.P.S6x5
