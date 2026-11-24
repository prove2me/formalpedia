-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_kxl_sss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:21:21.910091+00:00
-- url     : https://prove2.me/submissions/b8b6af62-73bf-40c3-89b5-7e3521418ab2

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_raises
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_xEx_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_hsh_same

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (l : ℕ) (Y : ℂ) :
    κ (fun ρ => M.xEx P {l} ρ Y) * star (SS l) = star (SS l) * κ (fun ρ => M.xEx P {l} ρ Y) := by
  have h := sn_raises hc l (fun ρ => star (M.xEx P {l} ρ Y)) (fun ρ => star (M.xEx P {l} ρ Y))
    (fun ρ ρ' h => by rw [sn_xEx_up h, sn_hsh_same])
  have h2 := congrArg star h
  rw [star_mul, star_mul, show star (κ _) = _ from hc.1 _] at h2
  simp only [star_star] at h2
  exact h2.symm
end Formalism.FourierDecayAlt.P.NFx2
