-- Prove2me | solution 1 for FourierJacobi.Analysis.haarLatticeCell_subset_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:49.881832+00:00
-- url     : https://prove2.me/submissions/3557531b-9be4-4695-9598-ebf789b740df

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
theorem _root_.solution (r : ℤ) (z : K) (k j h : ℤ) (c : ℕ) :
    haarLatticeCell K r z (k,j,h,c) ⊆
      unitValuationShell K k ×ˢ (integerShell K j ×ˢ integerShell K h) := by
  intro p hp
  exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
end FourierJacobi.Analysis
