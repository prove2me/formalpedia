-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.thetaBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:03:09.530074+00:00
-- url     : https://prove2.me/submissions/4f0ad632-5924-4f6c-b3f5-5aab0d529371

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_thetaForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution : ThetaBound := by
  intro hC σ ε hσ hε p x hx
  unfold ld
  have : (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => (1 + ε * Real.exp (-u)) ^ (-σ) := by
    funext u; exact thetaForm ε σ hε u
  rw [this]
  have h := hC σ ε hσ hε p (Real.log x)
  rwa [← thetaForm ε σ hε (Real.log x), Real.exp_log hx] at h
end Formalism.FourierDecayAlt.P.LEx1
