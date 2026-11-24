-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.ss_pj_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:43:58.037174+00:00
-- url     : https://prove2.me/submissions/c045791a-7682-4411-834c-28fe1f1fdb36

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_up_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_up_left

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (κ : (M.Ty P → ℂ) →ₐ[ℂ] A)
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution {SS : ℕ → A} (hR : Raises κ SS) {l : ℕ} {ρ ρ' : M.Ty P} (h : M.Up P l ρ ρ') :
    proj κ ρ' * SS l = SS l * proj κ ρ := by
  refine hR l _ _ fun a b hab => ?_
  by_cases ha : a = ρ
  · subst ha; have := up_right P hab h; subst this; simp
  · have hb : b ≠ ρ' := fun hb => ha (up_left P hab (hb ▸ h))
    simp [ha, hb]
end Formalism.FourierDecayAlt.P.NFx2
