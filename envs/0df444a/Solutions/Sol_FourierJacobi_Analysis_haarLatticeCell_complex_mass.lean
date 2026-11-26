-- Prove2me | solution 1 for FourierJacobi.Analysis.haarLatticeCell_complex_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:52:45.839945+00:00
-- url     : https://prove2.me/submissions/5ba57324-823c-4923-aa0b-c2cb3b4b3d39

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Definitions.Def_FourierJacobi_Analysis_HaarCellMass
import Theorems.Thm_FourierJacobi_Analysis_haarCellWeight_coe
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
    (((paperCoreMeasure K).real (haarLatticeCell K r z i) : ℝ) : ℂ) =
      (1 - (residueCardinality K : ℂ)⁻¹) ^ 3 *
        ((residueCardinality K : ℂ) ^ (-i.2.1) *
          (residueCardinality K : ℂ) ^ (-i.2.2.1)) *
            collisionWeight (residueCardinality K : ℂ) r i.2.1 i.2.2.1 i.2.2.2 := by
  rw [haarLatticeCell_real_mass K r z hz i]
  push_cast
  rw [haarCellWeight_coe]
end FourierJacobi.Analysis
