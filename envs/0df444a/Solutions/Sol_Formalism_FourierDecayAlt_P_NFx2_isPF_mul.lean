-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.isPF_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:13:44.822119+00:00
-- url     : https://prove2.me/submissions/fc840409-213b-4766-8743-6a79dcfeb923

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq

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
theorem _root_.solution {f g : ℂ → A} (hf : IsPF f) (hg : IsPF g) : IsPF fun Y => f Y * g Y := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  refine ⟨p * q, fun Y => ?_⟩
  show f Y * g Y = _
  rw [hp, hq, ev, ev, ev, eval₂_mul_noncomm]
  intro k; exact (Algebra.commutes Y _).symm
end Formalism.FourierDecayAlt.P.NFx2
