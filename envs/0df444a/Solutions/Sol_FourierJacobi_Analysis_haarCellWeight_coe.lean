-- Prove2me | solution 1 for FourierJacobi.Analysis.haarCellWeight_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:00.284574+00:00
-- url     : https://prove2.me/submissions/84604d3b-b0ba-4afb-8aab-e892205f99f2

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Definitions.Def_FourierJacobi_Analysis_HaarCellMass

set_option autoImplicit false
noncomputable section
open MeasureTheory
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Measure FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Analysis
theorem _root_.solution (r j h : ℤ) (c : ℕ) :
    (haarCellWeight K r j h c : ℂ) = collisionWeight (residueCardinality K : ℂ) r j h c := by
  unfold haarCellWeight collisionWeight shellCollisionProbability collisionProbability
  split_ifs <;> push_cast <;> rfl
end FourierJacobi.Analysis
