-- Prove2me | solution 1 for FourierJacobi.Measure.shellCollisionProbability_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:10.25583+00:00
-- url     : https://prove2.me/submissions/998124f9-3400-473a-94bc-c334d27b22e1

import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Theorems.Thm_FourierJacobi_Measure_residueCardinality_one_lt


set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.jointCollision_t2Space
namespace FourierJacobi.Measure
theorem _root_.solution (c : ℕ) : 0 ≤ shellCollisionProbability K c := by
  have hq : (2 : ℝ) ≤ residueCardinality K := by
    exact_mod_cast (show 2 ≤ residueCardinality K by have := residueCardinality_one_lt K; omega)
  unfold shellCollisionProbability
  split_ifs
  · exact div_nonneg (sub_nonneg.mpr hq) (by linarith)
  · exact zpow_nonneg (by linarith) _
end FourierJacobi.Measure
