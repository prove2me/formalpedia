-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.character_exists_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:38:05.229106+00:00
-- url     : https://prove2.me/submissions/ba06d893-c35d-4a3c-affc-9b1203ce00b1

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.ChiExists := by
  let f : ContDiffBump (1 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  refine ⟨f.normed MeasureTheory.volume, f.contDiff_normed, ?_, f.integral_normed⟩
  rw [f.tsupport_normed_eq]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq] at hx
  change |x - 1| ≤ 1 / 4 at hx
  have := abs_le.mp hx
  constructor <;> linarith [this.1, this.2]
end Formalism.FourierDecayAlt.P
