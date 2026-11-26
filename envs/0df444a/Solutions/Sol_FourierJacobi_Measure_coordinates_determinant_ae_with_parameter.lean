-- Prove2me | solution 1 for FourierJacobi.Measure.coordinates_determinant_ae_with_parameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:44:50.614398+00:00
-- url     : https://prove2.me/submissions/f989c0ed-94e1-483c-99f4-e30004f1c4c5

import Mathlib.NumberTheory.LocalField.Basic
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Measure_NullSets
import Theorems.Thm_FourierJacobi_Measure_coordinates_determinant_ae
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open FourierJacobi FourierJacobi.Measure
variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [SecondCountableTopology K]
  [T2Space K] [MeasurableSpace K] [BorelSpace K]
  (μ ν : MeasureTheory.Measure K) [NullSingletonClass ν]
variable [NullSingletonClass μ]
namespace FourierJacobi.Measure
theorem _root_.solution {A : Type*} [MeasurableSpace A]
    (ρ : MeasureTheory.Measure A) (z : K) :
    ∀ᵐ p : A × (K × K) ∂ρ.prod (μ.prod ν),
      p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧ p.2.2 ^ 2 - p.2.1 * z ≠ 0 := by
  have h := coordinates_determinant_ae μ ν z
  rw [ae_iff] at h ⊢
  have he : {p : A × (K × K) |
    ¬ (p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧ p.2.2 ^ 2 - p.2.1 * z ≠ 0)} =
    univ ×ˢ {p : K × K |
    ¬ (p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ^ 2 - p.1 * z ≠ 0)} := by ext; simp
  rw [he]
  apply le_antisymm _ bot_le
  exact (MeasureTheory.Measure.prod_prod_le _ _).trans_eq (by rw [h, mul_zero]; rfl)
end FourierJacobi.Measure
