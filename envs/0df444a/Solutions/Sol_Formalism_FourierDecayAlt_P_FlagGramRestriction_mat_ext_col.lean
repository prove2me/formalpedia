-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FlagGramRestriction.mat_ext_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:49:44.402437+00:00
-- url     : https://prove2.me/submissions/c3c654a6-ee08-4447-ac1f-e6586f2a7664

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FlagGramRestriction
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FlagGramRestriction
theorem _root_.solution {n : ℕ} {ι : Type*} (A B : Matrix (Fin n) ι ℂ) (h : ∀ j, (fun a => A a j) = fun a => B a j) :
    A = B := by
  ext a j; exact congrFun (h j) a
end Formalism.FourierDecayAlt.P.FlagGramRestriction
