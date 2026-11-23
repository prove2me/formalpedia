-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz8.cmRing_idempotent_unitRatio_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:34.035943+00:00
-- url     : https://prove2.me/submissions/5e0b2b47-6886-43be-95cb-6a16e5ca8838

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.Sz Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Sz8
namespace Formalism.FourierDecayAlt.P.Sz8
theorem _root_.solution (f : ℕ) (hf : 1 ≤ f) (Ct Z Th : ℝ) (hCt : 1 ≤ Ct) (hZ : 0 ≤ Z) (hTh : 0 < Th)
    (h : (Th ^ f)⁻¹ ≤ Ct * Z ^ f) : Th⁻¹ ≤ Ct * Z := by
  have hTh' : 0 < Th⁻¹ := inv_pos.mpr hTh
  have hf0 : f ≠ 0 := by omega
  have hCtf : Ct ≤ Ct ^ f := by
    calc Ct = Ct ^ 1 := (pow_one Ct).symm
      _ ≤ Ct ^ f := pow_le_pow_right₀ hCt hf
  have hZf : 0 ≤ Z ^ f := pow_nonneg hZ f
  have key : Th⁻¹ ^ f ≤ (Ct * Z) ^ f := by
    rw [inv_pow, mul_pow]
    calc (Th ^ f)⁻¹ ≤ Ct * Z ^ f := h
      _ ≤ Ct ^ f * Z ^ f := mul_le_mul_of_nonneg_right hCtf hZf
  exact (pow_le_pow_iff_left₀ hTh'.le (mul_nonneg (by linarith) hZ) hf0).mp key
end Formalism.FourierDecayAlt.P.Sz8
