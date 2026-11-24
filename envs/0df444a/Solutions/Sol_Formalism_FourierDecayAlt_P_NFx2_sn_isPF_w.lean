-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_isPF_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:21:09.483721+00:00
-- url     : https://prove2.me/submissions/6507f5f6-fed7-4d4d-be4f-e51259f3bbd9

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_kap_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_cpoly
import Theorems.Thm_UpperTheory_Reformulated_B_IsPFSum_isPF_sum


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
theorem _root_.solution : IsPF fun Y => κ (fun ρ => M.wC P ρ Y) := by
  have e : (fun Y => κ (fun ρ => M.wC P ρ Y)) = fun Y => ∑ ρ, (M.wNum P ρ /ₘ M.coordinatePolynomial P ρ).eval Y • proj κ ρ :=
    funext fun Y => kap_eq κ _
  rw [e]
  exact isPF_sum _ fun ρ _ => isPF_cpoly _ _
end Formalism.FourierDecayAlt.P.NFx2
