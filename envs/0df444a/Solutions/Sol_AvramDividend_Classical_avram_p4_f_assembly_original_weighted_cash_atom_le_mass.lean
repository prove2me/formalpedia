-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_weighted_cash_atom_le_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:53:58.567598+00:00
-- url     : https://prove2.me/submissions/30f982bc-72c3-484b-b343-65005a993f51

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_discount_of_nonnegative_time_le_one
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_atom_vanishes_outside_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Actual Cash discount atoms are bounded by source singleton mass on every index. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (q : ℝ) (hq : 0 ≤ q) (A : Set ℝ) :
    ∀ a : A,
      (if a.1 ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) * μatom {a.1} ≤ μatom {a.1} := by
  intro a
  by_cases hin : a.1 ∈ Icc (0 : ℝ) (T : ℝ)
  · have hf := avram_p4_f_assembly_original_cash_discount_of_nonnegative_time_le_one
      (ruinTime X x D ω) q a.1 hq hin.1
    calc
      (if a.1 ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) * μatom {a.1} ≤
          1 * μatom {a.1} := by
        gcongr
        all_goals exact hf
      _ = μatom {a.1} := one_mul _
  · have hzero :=
      avram_p4_f_assembly_original_cash_atom_vanishes_outside_horizon
        D ω T μatom μdiffuse hsplit a.1 hin
    simp [hzero]
