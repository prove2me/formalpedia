-- Prove2me | solution 1 for Formalism.L2.Th1.A.bridgeTwo_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:20:20.537801+00:00
-- url     : https://prove2.me/submissions/2d6d629d-2819-4e0c-9e86-088fbe8631df

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementJ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeJ
import Theorems.Thm_Formalism_L2_Th1_A_Bridge_integral_of_coeff
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_natCast
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Bridge
namespace Formalism.L2.Th1.A
theorem _root_.solution (hM : CoeffMem.{0}) (hT : TInZ.{0}) (hZ : TwoTorsionZ.{0}) : BridgeTwo := by
  unfold BridgeTwo
  intro K _ _ _ W xT yT heq h2y
  obtain ⟨_, _, _, _, hdvd, h2c, _, hder, _, _, _⟩ := hZ K W xT yT heq h2y
  have hT' := hT K W xT
  have hD : constantCoeff (1 + X ^ 2 * wpReg W - C (xT + W.b₂ / 12) * X ^ 2 : K⟦X⟧) ≠ 0 := by
    simp
  have h3 : (C (3 : K) : K⟦X⟧) = 3 := by
    rw [show (3 : K) = ((3 : ℕ) : K) by norm_num, map_natCast]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · unfold Formalism.L2.Th1.B.wOf
    calc (tS W xT).subst (expSer W)
        = (tS W xT).subst (expSer W) * ((1 + X ^ 2 * wpReg W - C (xT + W.b₂ / 12) * X ^ 2)
          * (1 + X ^ 2 * wpReg W - C (xT + W.b₂ / 12) * X ^ 2)⁻¹) := by
          rw [PowerSeries.mul_inv_cancel _ hD, mul_one]
      _ = ((tS W xT).subst (expSer W) * (1 + X ^ 2 * wpReg W - C (xT + W.b₂ / 12) * X ^ 2))
          * (1 + X ^ 2 * wpReg W - C (xT + W.b₂ / 12) * X ^ 2)⁻¹ := by ring
      _ = X ^ 2 * (1 + X ^ 2 * wpReg W - C (xT + W.b₂ / 12) * X ^ 2)⁻¹ := by rw [hT']
  · unfold Formalism.L2.Th1.B.IsW
    obtain ⟨q, hq⟩ := hdvd
    refine ⟨?_, h2c, ?_⟩
    · rw [hq]
      simp
    · show (PowerSeries.derivative K ((tS W xT).subst (expSer W))) ^ 2 = _
      rw [hder, map_mul, h3]
      ring
  · intro hI hx
    apply Bridge.integral_of_coeff
    exact (hM K W (Formalism.G.unitBall K) hI.1 hI.2.1 hI.2.2.1 hI.2.2.2.1 hI.2.2.2.2).2.2.2.2.2.2.2.2.2.1 xT hx
end Formalism.L2.Th1.A
