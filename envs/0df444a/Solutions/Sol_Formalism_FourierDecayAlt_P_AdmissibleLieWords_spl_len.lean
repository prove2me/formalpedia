-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.spl_len
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:54:03.876813+00:00
-- url     : https://prove2.me/submissions/48101be1-c845-47dd-80d8-e62a8f8d2192

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {w w₁ w₂ : List (Bool × Mat k r)} (h : Spl w w₁ w₂) : w₁.length + w₂.length = w.length := by
  obtain ⟨-, -, hp⟩ := h
  rw [← List.length_append]
  exact hp.length_eq
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
