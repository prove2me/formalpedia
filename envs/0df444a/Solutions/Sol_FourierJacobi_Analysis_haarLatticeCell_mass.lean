-- Prove2me | solution 1 for FourierJacobi.Analysis.haarLatticeCell_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:52:46.572065+00:00
-- url     : https://prove2.me/submissions/d32d276b-52cb-49d5-b6e2-dc4dad8538d4

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Definitions.Def_FourierJacobi_Analysis_HaarCellMass
import Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_measure_ne_top
import Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_real_mass

set_option autoImplicit false
noncomputable section
open MeasureTheory
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Measure FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Analysis.haarCellMass_t2Space
attribute [local instance] FourierJacobi.Analysis.haarCellMass_secondCountable
attribute [local instance] FourierJacobi.Analysis.haarCellMass_unitsBorel
attribute [local instance] FourierJacobi.Analysis.haarCellMass_additiveSigmaFinite
namespace FourierJacobi.Analysis
theorem _root_.solution (r : ℤ) (z : K) (hz : CentralRepresentative K r z)
    (i : LatticeIndex) :
    paperCoreMeasure K (haarLatticeCell K r z i) =
      ENNReal.ofReal ((1 - (residueCardinality K : ℝ)⁻¹) ^ 3 *
        ((residueCardinality K : ℝ) ^ (-i.2.1) *
          (residueCardinality K : ℝ) ^ (-i.2.2.1)) *
            haarCellWeight K r i.2.1 i.2.2.1 i.2.2.2) := by
  rw [← haarLatticeCell_real_mass K r z hz i]
  exact (ENNReal.ofReal_toReal (haarLatticeCell_measure_ne_top K r z i)).symm
end FourierJacobi.Analysis
