-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.Fk_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:47.229428+00:00
-- url     : https://prove2.me/submissions/0fc86060-30af-4d74-a49b-de8747e742b3

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit

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
theorem _root_.solution (k : ℕ) (s : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fk k s) := by
  unfold Fk
  refine (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul ?_
  refine ContDiff.rpow_const_of_ne ?_ ?_
  · exact contDiff_const.add (Real.contDiff_exp.comp contDiff_neg)
  · intro u; positivity
end Formalism.FourierDecayAlt.P.LEx2
