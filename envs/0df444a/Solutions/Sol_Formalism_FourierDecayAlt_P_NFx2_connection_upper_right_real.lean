-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.connection_upper_right_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:35:13.743562+00:00
-- url     : https://prove2.me/submissions/38ba3519-c269-4a06-9050-aad1484647c6

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_H_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_lower_left_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_lower_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_star_xA
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_star_kx
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_upper_right_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_star_lowering
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_coordinate_commute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS) {Y : ℂ} (hY : star Y = Y) :
    QQ Y 0 1 = (Q.NFData.QQ (⟨sc_LL h hF, κ, SS⟩ : Q.NFData P A) Y) 0 1 := by
  rw [← H_herm h hY 1 0, connection_lower_left_eq h hF hR Y, connection_lower_left_entry, connection_upper_right_entry, star_add, star_sum]
  congr 1
  · rw [star_mul, star_mul, sc_star_xA h hY, sc_sGG h, connection_star_lowering h hF hY]
    have hx : L0.GGi * xA κ Y * L0.GG = xA κ Y := by
      show L0.GGi * κ (fun ρ => M.xC P ρ Y) * L0.GG = κ (fun ρ => M.xC P ρ Y)
      rw [← sc_kc h _ (sc_mGGi L0), mul_assoc, L0.GGi_GG, mul_one]
    calc L0.GG * (sc_LL h hF).m0 Y * L0.GGi * (xA κ Y * L0.GG)
        = L0.GG * (sc_LL h hF).m0 Y * (L0.GGi * xA κ Y * L0.GG) := by noncomm_ring
      _ = L0.GG * xA κ Y * (sc_LL h hF).m0 Y := by rw [hx, mul_assoc, ← connection_coordinate_commute h hF, ← mul_assoc]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [star_mul, sc_star_kx h hY]
end Formalism.FourierDecayAlt.P.NFx2
