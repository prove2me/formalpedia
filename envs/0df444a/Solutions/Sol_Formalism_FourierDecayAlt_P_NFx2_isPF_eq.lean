-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.isPF_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:21:48.312269+00:00
-- url     : https://prove2.me/submissions/84db3e99-de07-4ee9-8f33-b28d5fe94e0f

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_zero

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
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution {f g : ℂ → A} (hf : IsPF f) (hg : IsPF g) {S : Set ℂ} (hS : S.Infinite)
    (h0 : ∀ Y ∈ S, f Y = g Y) : ∀ Y, f Y = g Y := by
  have := isPF_zero (isPF_sub hf hg) hS (fun Y hY => by simp [h0 Y hY])
  intro Y; exact sub_eq_zero.mp (this Y)
end Formalism.FourierDecayAlt.P.NFx2
