-- Prove2me | solution 1 for FourierJacobi.Measure.unitConditionalMass_unitCenteredTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:47.835897+00:00
-- url     : https://prove2.me/submissions/27bd50a9-8e9c-4b5b-b274-51ca296c2b2b

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Theorems.Thm_FourierJacobi_Measure_residueCardinality_one_lt
import Theorems.Thm_FourierJacobi_Measure_unitConditionalMass_of_subset
import Theorems.Thm_FourierJacobi_Measure_unitCenteredTail_subset_units
import Theorems.Thm_FourierJacobi_Measure_integersHaar_unitCenteredTail
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel
open scoped ENNReal NNReal
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.localField_t2Space
variable [MeasurableSpace K] [BorelSpace K]
namespace FourierJacobi.Measure
theorem _root_.solution (a : 𝒪[K]ˣ) (n : ℕ) :
    unitConditionalMass K (unitCenteredTail K a (n + 1)) =
      (residueCardinality K : ℝ)⁻¹ ^ n / (residueCardinality K - 1) := by
  have hq : (1 : ℝ) < residueCardinality K := by
    exact_mod_cast residueCardinality_one_lt K
  rw [unitConditionalMass_of_subset _ _
    (unitCenteredTail_subset_units K a (Nat.succ_pos n))]
  have hv : (integersHaar K).real (unitCenteredTail K a (n + 1)) =
      (residueCardinality K : ℝ)⁻¹ ^ (n + 1) := by
    simp [measureReal_def, integersHaar_unitCenteredTail]
  rw [hv, pow_succ]
  field_simp
end FourierJacobi.Measure
