-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.admissible_of_unit_words
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:14:29.69464+00:00
-- url     : https://prove2.me/submissions/9e095d6e-f5bd-4e26-a4a3-01b823b1b0fc

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolynomialBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfUnitWords

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution {k r i : ℕ} {u v : List (Mat k r)} (h : C6.UnitWords k r u v i) : admitted i (wL u ++ wR v) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨u, v, h1, h2, h3.le, rfl⟩
end Formalism.FourierDecayAlt.P
