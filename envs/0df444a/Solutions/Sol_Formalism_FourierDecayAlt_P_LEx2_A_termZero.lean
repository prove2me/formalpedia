-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.A.termZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:37.034181+00:00
-- url     : https://prove2.me/submissions/27bc92c0-ec8a-47b6-b1f2-174c1ba91ada

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_A_ds_zero

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
theorem _root_.solution : TermZero := by
  intro B S ε σ Y
  unfold Step.term Step.En
  rw [ds_zero]
  simp only [Nat.factorial_zero, Nat.cast_one, div_one]
  rw [← integral_complex_ofReal]
  congr 1
  funext ω
  have hG := B.G_pos ω
  simp only [ld, iteratedDeriv_zero, Real.exp_log hG, pr, LE.sq]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.LEx2.A
