-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_isPF_prod_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:42:23.907973+00:00
-- url     : https://prove2.me/submissions/82e3c413-de1d-4454-a4ad-5184bbe18eca

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_smul_fun
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_prod_eval

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
theorem _root_.solution (s : Finset ℕ) (c : ℕ → ℂ) {f : ℂ → A} (hf : IsPF f) :
    IsPF fun Y => (∏ i ∈ s, (Y + c i)) • f Y := by
  have e : (fun Y => (∏ i ∈ s, (Y + c i)) • f Y) = fun Y => (∏ i ∈ s, (X + C (c i))).eval Y • f Y :=
    funext fun Y => by rw [sn_prod_eval]
  rw [e]; exact isPF_smul_fun _ hf
end Formalism.FourierDecayAlt.P.NFx2
