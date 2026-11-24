-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.meas_gram_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:40:43.461697+00:00
-- url     : https://prove2.me/submissions/1fe4dd53-1319-476d-9b08-0fcb5e1293cf

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
theorem _root_.solution (G₀ : (Q → Q → ℂ) → ℝ≥0∞) (hG : Measurable G₀) (C : Matrix Q Q ℂ) :
    Measurable fun X : Q → Q → ℂ => G₀ (gram X - C) := by
  have h : Measurable (fun X : Q → Q → ℂ => fun i j => gram X i j - C i j) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      (gram_cont.matrix_elem i j).measurable.sub_const (C i j)
  exact hG.comp h
end Formalism.FourierDecayAlt.P.HermitianFormFactor
