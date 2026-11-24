-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.meas_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:24:26.319198+00:00
-- url     : https://prove2.me/submissions/004ee665-dd03-4214-9967-16e5a4d2b780

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_gram_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
variable {Q : Type} [Fintype Q] [DecidableEq Q]
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (G₀ : (Q → Q → ℂ) → ℝ≥0∞) (hG : Measurable G₀) :
    Measurable fun X : Q → Q → ℂ => G₀ (gram X) := by
  have h : Measurable (fun X : Q → Q → ℂ => fun i j => gram X i j) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => (gram_cont.matrix_elem i j).measurable
  exact hG.comp h
end Formalism.FourierDecayAlt.P.HermitianFormFactor
