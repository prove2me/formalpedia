-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.det_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:16:05.846502+00:00
-- url     : https://prove2.me/submissions/b0c9289b-81be-4766-bb51-24788eb5c95c

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution {p : ℕ} (u : G.UT p → ℂ) : (G.upper u).det = 1 := by
  have h : (G.upper u).BlockTriangular id := by
    intro i j hij
    simp only [id] at hij
    simp [G.upper, G.strictUpper, ne_of_gt hij, not_lt.mpr (le_of_lt hij)]
  rw [Matrix.det_of_isUpperTriangular h]
  simp [G.upper, G.strictUpper]
end Formalism.FourierDecayAlt.P.Ux6
