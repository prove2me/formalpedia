-- Prove2me | solution 1 for Formalism.L2.Th1.A.bridgeLaw_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:50:26.701252+00:00
-- url     : https://prove2.me/submissions/4288f314-9c09-45a8-b5bf-58867814f9b2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementJ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeJ
import Theorems.Thm_Formalism_L2_Th1_A_Bridge_integral_of_coeff
import Theorems.Thm_Formalism_L2_Th1_A_Bridge_integral_of_mvCoeff
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_fglChord
import Theorems.Thm_Formalism_L2_Th1_A_iSerSpec
import Theorems.Thm_Formalism_L2_Th1_A_logNeg
import Theorems.Thm_Formalism_L2_Th1_A_logSpec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Bridge
namespace Formalism.L2.Th1.A
theorem _root_.solution (hM : CoeffMem.{0}) (hFL : FglLog.{0}) (hHS : HalfSpec.{0})
    (hHL : HalfLog.{0, 0}) : BridgeLaw := by
  intro K _ _ _ W hW
  obtain ⟨-, -, -, -, -, hi, hF, -, hh, -, -⟩ :=
    hM K W (Formalism.G.unitBall K) hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2
  obtain ⟨hl0, hl1, -, -⟩ := logSpec K W
  refine ⟨⟨(fglChord K W).2.2.2.2.1, integral_of_mvCoeff hF, hl0, hl1, ?_⟩,
    ⟨(iSerSpec K W).1, integral_of_coeff hi, (logNeg K W).1⟩, fun h2 => ?_⟩
  · unfold Formalism.InvariantFactorPaths.G7.cob Formalism.InvariantFactorPaths.G7.at1
    rw [(hFL K W).1]
    ring
  · have hu : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr two_ne_zero
    refine ⟨(hHS K W hu).1, integral_of_coeff (hh ⟨2⁻¹, ?_, mul_inv_cancel₀ two_ne_zero⟩), ?_⟩
    · change ‖(2 : K)⁻¹‖ ≤ 1
      rw [norm_inv, h2, inv_one]
    · have key := hHL.1 K W
      have h21 : (C (2 : K)⁻¹ : K⟦X⟧) * 2 = 1 := by
        rw [← map_ofNat (C : K →+* K⟦X⟧) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
      calc (logSer W).subst (halfSer W)
          = (C (2 : K)⁻¹ * 2) * (logSer W).subst (halfSer W) := by rw [h21, one_mul]
        _ = C (2 : K)⁻¹ * (2 * (logSer W).subst (halfSer W)) := by ring
        _ = C (2 : K)⁻¹ * logSer W := by rw [key]
end Formalism.L2.Th1.A
