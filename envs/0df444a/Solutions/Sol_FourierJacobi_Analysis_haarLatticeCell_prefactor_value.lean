-- Prove2me | solution 1 for FourierJacobi.Analysis.haarLatticeCell_prefactor_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:53:56.253961+00:00
-- url     : https://prove2.me/submissions/dd8d591c-a5b0-4abe-868b-beeb6d034921

import Definitions.Def_FourierJacobi_Analysis_HaarCellValue
import Definitions.Def_FourierJacobi_Analysis_HaarCellMass
import Definitions.Def_FourierJacobi_Analysis_HaarCellMaster
import Theorems.Thm_FourierJacobi_Analysis_prefactor_cellScalarMass_haarCellValue
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_one
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_two
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_zero
import Theorems.Thm_FourierJacobi_Analysis_coreScaleExponent_coe
import Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_complex_mass
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Analysis.coreCentral_one
attribute [local simp] FourierJacobi.Analysis.coreCentral_two
attribute [local simp] FourierJacobi.Analysis.coreCentral_zero
attribute [local simp] FourierJacobi.Analysis.coreScaleExponent_coe
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero
attribute [local simp] FourierJacobi.Valuations.actualEntryInteger_coe
attribute [local simp] FourierJacobi.Valuations.actualMinorInteger_coe
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
namespace FourierJacobi.Analysis
theorem _root_.solution
    (hq : 1 < (FourierJacobi.Measure.residueCardinality K : ℝ))
    (a b d : ℂ) (T : ℝ) (hT : T ≠ 0) (r : Fin 3) (z : K)
    (hz : CentralRepresentative K (r.val : ℤ) z) (i : LatticeIndex) :
    coreIntegralPrefactor (FourierJacobi.Measure.residueCardinality K : ℝ) r *
        (((paperCoreMeasure K).real (haarLatticeCell K (r.val : ℤ) z i) : ℝ) : ℂ) *
        haarCellValue (FourierJacobi.Measure.residueCardinality K : ℝ) a b d T
          (r.val : ℤ) i =
      ∑ w : Fin 8,
        (weylWeights (inverseSqrt (FourierJacobi.Measure.residueCardinality K : ℝ) : ℂ)
          a b w / paperC (FourierJacobi.Measure.residueCardinality K : ℝ)) *
        masterTerm (FourierJacobi.Measure.residueCardinality K : ℂ)
          (inverseSqrt (FourierJacobi.Measure.residueCardinality K : ℝ) : ℂ)
          d (weylU a b w) (weylV a b w) (T : ℂ) (r.val : ℤ) i := by
  rw [haarLatticeCell_complex_mass K (r.val : ℤ) z hz i]
  simpa only [haarCellScalarMass, Complex.ofReal_natCast] using
    prefactor_cellScalarMass_haarCellValue (FourierJacobi.Measure.residueCardinality K : ℝ)
      hq a b d T hT r i
end FourierJacobi.Analysis
