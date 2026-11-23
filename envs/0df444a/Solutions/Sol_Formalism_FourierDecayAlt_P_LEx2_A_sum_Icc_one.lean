-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.A.sum_Icc_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:33.444106+00:00
-- url     : https://prove2.me/submissions/4f6bd090-8409-485b-90e7-90c93450fd73

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2 Formalism.FourierDecayAlt.P.LEx2.A
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx2.A
theorem _root_.solution (f : ℕ → ℝ) (R : ℕ) : ∑ p ∈ Icc 1 R, f p = ∑ i ∈ range R, f (i + 1) := by
  induction R with
  | zero => simp
  | succ R ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
end Formalism.FourierDecayAlt.P.LEx2.A
