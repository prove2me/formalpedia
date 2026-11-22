-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.thetaSmooth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:04:43.798813+00:00
-- url     : https://prove2.me/submissions/f7f731b4-027b-4356-aa6c-43b4d82b0c64

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_thetaForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : ThetaSmooth := by
  intro ε σ hε
  unfold SmoothLog
  have : (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => (1 + ε * Real.exp (-u)) ^ (-σ) := by
    funext u; exact thetaForm ε σ hε u
  rw [this]
  refine ContDiff.rpow_const_of_ne ?_ ?_
  · exact contDiff_const.add (contDiff_const.mul (Real.contDiff_exp.comp contDiff_neg))
  · intro u; positivity
end Formalism.FourierDecayAlt.P.LEx2
