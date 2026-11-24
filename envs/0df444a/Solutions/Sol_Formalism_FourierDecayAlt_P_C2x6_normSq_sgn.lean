-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x6.normSq_sgn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:15:43.12157+00:00
-- url     : https://prove2.me/submissions/20d4c1e8-c608-4c85-b146-527690f0e076

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x6
open C2x5
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x6
theorem _root_.solution (i : Fin (2 * r + k + 1)) : Complex.normSq (GBasic.sgn k r i) = 1 := by
  unfold GBasic.sgn
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.C2x6
