-- Prove2me | solution 1 for Formalism.L2.SG.CovariantRepresentation.map_mul_right_eq_modular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:14.971679+00:00
-- url     : https://prove2.me/submissions/55bb2f18-d069-4953-a25b-897692ea1e84

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.CovariantRepresentation
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
namespace Formalism.L2.SG.CovariantRepresentation
theorem _root_.solution (μ : Measure H) [IsHaarMeasure μ] (g : H) :
    μ.map (· * g) = ((modularCharacterFun g : ℝ≥0) : ℝ≥0∞) • μ := by
  rw [← ENNReal.smul_def, modularCharacterFun_eq_haarScalarFactor μ g]
  exact isMulLeftInvariant_eq_smul (μ.map (· * g)) μ
end Formalism.L2.SG.CovariantRepresentation
