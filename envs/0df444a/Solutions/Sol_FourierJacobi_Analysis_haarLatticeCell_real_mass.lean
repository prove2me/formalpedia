-- Prove2me | solution 1 for FourierJacobi.Analysis.haarLatticeCell_real_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:34.868992+00:00
-- url     : https://prove2.me/submissions/3ad34cf6-2bce-4cef-8f91-7e6f67dfd962

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Definitions.Def_FourierJacobi_Analysis_HaarCellMass
import Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_eq_off
import Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_eq_collision
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_one
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_two
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_zero
import Theorems.Thm_FourierJacobi_Analysis_coreScaleExponent_coe
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_integerShell
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_prod_sourceJointCollisionDepth
import Theorems.Thm_FourierJacobi_Measure_paperMultiplicativeHaar_real_unitValuationShell
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
    (paperCoreMeasure K).real (haarLatticeCell K r z i) =
      (1 - (residueCardinality K : ℝ)⁻¹) ^ 3 *
        ((residueCardinality K : ℝ) ^ (-i.2.1) *
          (residueCardinality K : ℝ) ^ (-i.2.2.1)) *
            haarCellWeight K r i.2.1 i.2.2.1 i.2.2.2 := by
  rcases i with ⟨k,j,h,c⟩
  by_cases he : r = 0 ∨ 2 * h ≠ j - r
  · rw [haarLatticeCell_eq_off K r z k j h c he]
    by_cases hc : c = 0
    · rw [if_pos hc]
      simp only [paperCoreMeasure, measureReal_prod_prod, paperMultiplicativeHaar_real_unitValuationShell,
        additiveHaar_real_integerShell, haarCellWeight, he, if_true, hc, mul_one]
      ring
    · simp only [measureReal_empty, haarCellWeight, he, if_true, hc,
        if_false, mul_zero]
  · have hr : r ≠ 0 := fun hr => he (Or.inl hr)
    have hlocus : 2 * h = j + (-r) := by
      have hh : 2 * h = j - r := Classical.not_not.mp (fun hh => he (Or.inr hh))
      omega
    have hzr : localFieldValuation K z = ((-r : ℤ) : WithTop ℤ) := by
      rcases hz with ⟨hr',_⟩ | ⟨_,hz'⟩
      · exact (hr hr').elim
      · exact hz'
    rw [haarLatticeCell_eq_collision K r z k j h c he]
    simp only [paperCoreMeasure, measureReal_prod_prod, paperMultiplicativeHaar_real_unitValuationShell]
    rw [additiveHaar_real_prod_sourceJointCollisionDepth K z j h (-r) c hzr hlocus]
    simp only [haarCellWeight, he, if_false]
    ring
end FourierJacobi.Analysis
