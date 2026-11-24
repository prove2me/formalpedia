-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.cont_Gf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:13.63306+00:00
-- url     : https://prove2.me/submissions/78c816c7-22b5-4b49-8f1e-e6dd872c180c

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_cont_Dmin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.Ux8
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous (Gf k r z z') := by
  have h1 := Complex.continuous_normSq.comp (cont_Dmin k r z z' (Fin.last (r + 1)))
  have h2 := Complex.continuous_normSq.comp (cont_Dmin k r z z' ⟨r, by omega⟩)
  unfold Gf
  exact h1.sub (continuous_const.mul h2)
end Formalism.FourierDecayAlt.P.Ux8
