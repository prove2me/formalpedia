-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_noneligible_cash_atom_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:45:25.474267+00:00
-- url     : https://prove2.me/submissions/b0994093-eb5f-4066-ab78-57432652f6b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_atom_vanishes_outside_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The exact source Cash term vanishes outside the effective payment indices. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (q a : ℝ)
    (hnot : a ∉ Icc (0 : ℝ) (T : ℝ) ∨
      a ∉ paymentTimes (ruinTime X x D ω)) :
    (if a ∈ paymentTimes (ruinTime X x D ω) then
      ENNReal.ofReal (Real.exp (-(q * a))) else 0) *
      μatom {a} = 0 := by
  rcases hnot with hout | hpayment
  · have hzero :=
      avram_p4_f_assembly_original_cash_atom_vanishes_outside_horizon
        D ω T μatom μdiffuse hsplit a hout
    simp [hzero]
  · simp [hpayment]
