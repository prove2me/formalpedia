-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FlagGramRestriction.col_V_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:49:47.820109+00:00
-- url     : https://prove2.me/submissions/7a683956-06c4-4356-b66a-2936f2fd06fc

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
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (Φ : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    (fun a => (gnB k r z z' γ * Φ) a j) = ∑ i, Φ i j • gramVec k r z z' γ i := by
  funext a; simp [gnB, Matrix.mul_apply, Finset.sum_apply, mul_comm]
end Formalism.FourierDecayAlt.P.FlagGramRestriction
