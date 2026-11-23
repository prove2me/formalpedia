-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.compC_off
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:02.659806+00:00
-- url     : https://prove2.me/submissions/60f63875-65b9-4dd8-8a39-1abb1e46a1ec

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_xEx_pair
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Mx7_xEx_pair__9b8c59969b7c
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_sh_pair
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_TT_eq

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
theorem _root_.solution (hSh : SSShift) (hC : SSComm) (hR : RhoUp) (P : Par) (hP : P.OK) (u v : ℂ) (l j : ℕ)
    (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    ((SS P l * kap P fun π => xEx P {l} π u) * (SS P j * kap P fun π => xEx P {j} π v) -
      (SS P l * kap P fun π => xEx P {l} π v) * (SS P j * kap P fun π => xEx P {j} π u)) +
    ((SS P j * kap P fun π => xEx P {j} π u) * (SS P l * kap P fun π => xEx P {l} π v) -
      (SS P j * kap P fun π => xEx P {j} π v) * (SS P l * kap P fun π => xEx P {l} π u)) = 0 := by
  rw [TT_eq P l j _ _ _ (sh_pair hSh hR P l j hj hjl u), TT_eq P l j _ _ _ (sh_pair hSh hR P l j hj hjl v),
    TT_eq P j l _ _ _ (sh_pair hSh hR P j l hl (Ne.symm hjl) u),
    TT_eq P j l _ _ _ (sh_pair hSh hR P j l hl (Ne.symm hjl) v), ← mul_sub, ← mul_sub, ← map_sub, ← map_sub]
  have h12 : ((fun π => xEx P {l, j} π u * (u + 1 + (rho P π j : ℂ))) * fun π => xEx P {j} π v) -
      ((fun π => xEx P {l, j} π v * (v + 1 + (rho P π j : ℂ))) * fun π => xEx P {j} π u) =
      -((fun π => ((rho P π j - rho P π l + 1 : ℝ) : ℂ)) *
        fun π => (u - v) * (xEx P {l, j} π u * xEx P {l, j} π v)) := by
    funext π
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]
    rw [xEx_pair' P π v l j hl hjl, xEx_pair' P π u l j hl hjl]
    push_cast; ring
  have h34 : ((fun π => xEx P {j, l} π u * (u + 1 + (rho P π l : ℂ))) * fun π => xEx P {l} π v) -
      ((fun π => xEx P {j, l} π v * (v + 1 + (rho P π l : ℂ))) * fun π => xEx P {l} π u) =
      (fun π => ((rho P π j - rho P π l - 1 : ℝ) : ℂ)) *
        fun π => (u - v) * (xEx P {l, j} π u * xEx P {l, j} π v) := by
    funext π
    simp only [Pi.sub_apply, Pi.mul_apply]
    rw [xEx_pair P π v l j hj hjl, xEx_pair P π u l j hj hjl, Finset.pair_comm j l]
    push_cast; ring
  rw [h12, h34, map_neg, map_mul, map_mul, ← mul_assoc (SS P j * SS P l), hC P hP l hl j hj hjl, mul_neg,
    mul_assoc (SS P l * SS P j), neg_add_cancel]
end Formalism.FourierDecayAlt.P.Mx7
