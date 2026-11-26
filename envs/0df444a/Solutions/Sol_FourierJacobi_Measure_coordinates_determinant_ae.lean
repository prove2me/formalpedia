-- Prove2me | solution 1 for FourierJacobi.Measure.coordinates_determinant_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:13.545806+00:00
-- url     : https://prove2.me/submissions/2b4424ad-0e1a-4dfb-86e6-c6ce149a775e

import Mathlib.NumberTheory.LocalField.Basic
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Measure_NullSets
import Theorems.Thm_FourierJacobi_Measure_determinant_zero_null
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
theorem _root_.solution (z : K) :
    ∀ᵐ p : K × K ∂μ.prod ν, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ^ 2 - p.1 * z ≠ 0 := by
  have hx : (μ.prod ν) {p : K × K | p.1 = 0} = 0 := by
    have he : {p : K × K | p.1 = 0} = ({0} : Set K) ×ˢ univ := by ext; simp
    rw [he]
    apply le_antisymm _ bot_le
    exact (MeasureTheory.Measure.prod_prod_le _ _).trans (by simp)
  have hy : (μ.prod ν) {p : K × K | p.2 = 0} = 0 := by
    have he : {p : K × K | p.2 = 0} = univ ×ˢ ({0} : Set K) := by ext; simp
    rw [he]
    apply le_antisymm _ bot_le
    exact (MeasureTheory.Measure.prod_prod_le _ _).trans (by simp)
  have hd := determinant_zero_null μ ν z
  have hx' : ∀ᵐ p : K × K ∂μ.prod ν, p.1 ≠ 0 := by simpa [ae_iff] using hx
  have hy' : ∀ᵐ p : K × K ∂μ.prod ν, p.2 ≠ 0 := by simpa [ae_iff] using hy
  have hd' : ∀ᵐ p : K × K ∂μ.prod ν, p.2 ^ 2 - p.1 * z ≠ 0 := by simpa [ae_iff] using hd
  filter_upwards [hx', hy', hd'] with p hp hq hd
  exact ⟨hp, hq, hd⟩
end FourierJacobi.Measure
