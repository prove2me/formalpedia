-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.compB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:20.039225+00:00
-- url     : https://prove2.me/submissions/91002cec-e2fa-4c53-a4f1-d23d22edfaf4

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_comm_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_comm_nab
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_xC_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_shift_x_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_lowering_constant_eq_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_weighted_sum_difference_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_mul_assoc_commute_middle
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_absCombo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (hSc : SSScalar) (hSh : SSShift) (hN : NabSS) (hR : RhoUp) (P : Par) (u v : ℂ) (l : ℕ)
    (hl : l ∈ Icc 1 (P.k - 1)) :
    (ggA P * xA P u * l0A P u) * (SS P l * kap P fun π => xEx P {l} π v) +
      (SS P l * kap P fun π => xEx P {l} π u) * (ggA P * xA P v * l0A P v) =
    (ggA P * xA P v * l0A P v) * (SS P l * kap P fun π => xEx P {l} π u) +
      (SS P l * kap P fun π => xEx P {l} π v) * (ggA P * xA P u * l0A P u) := by
  have hNS := (hN P l hl).1
  have hbS : (zbA P * ggiA P) * SS P l = SS P l * (zbA P * ggiA P) :=
    ((hSc P l zbP).mul_right (hSc P l (ggiP P.TT))).eq.symm
  have hSG : SS P l * ggA P = ggA P * SS P l := (hSc P l (ggP P.TT)).eq
  have cE : ∀ w : ℂ, Commute (kap P fun π => xEx P {l} π w) (nabA P) ∧
      Commute (kap P fun π => xEx P {l} π w) (zbA P * ggiA P) ∧
      (kap P fun π => xEx P {l} π w) * ggA P = ggA P * kap P fun π => xEx P {l} π w := fun w =>
    ⟨kap_comm_nab P _, (kap_comm_sc P _ _).mul_right (kap_comm_sc P _ _), (kap_comm_sc P _ _).eq⟩
  rw [lowering_constant_eq_shift, lowering_constant_eq_shift,
    weighted_sum_difference_identity _ _ _ _ _ _ _ hNS hbS (shift_x_identity hSh hR P l hl u) hSG (cE v).1 (cE v).2.1,
    weighted_sum_difference_identity _ _ _ _ _ _ _ hNS hbS (shift_x_identity hSh hR P l hl v) hSG (cE u).1 (cE u).2.1,
    mul_assoc_commute_middle _ _ _ _ _ (cE u).2.2, mul_assoc_commute_middle _ _ _ _ _ (cE v).2.2, ← mul_add, ← mul_add]
  refine congrArg (fun t => SS P l * ggA P * t) ?_
  unfold xA
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  apply absCombo
  · funext π
    simp only [Pi.add_apply, Pi.mul_apply]
    rw [xC_eq P π u l hl, xC_eq P π v l hl]; ring
  · funext π
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [xC_eq P π u l hl, xC_eq P π v l hl]; ring
end Formalism.FourierDecayAlt.P.Mx7
