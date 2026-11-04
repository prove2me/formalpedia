-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_cash_weighted_atom_tsum_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:05:56.504714+00:00
-- url     : https://prove2.me/submissions/c892d9b8-2c40-45d7-8f1c-88f87e61aa22

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_cash_atom_total
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_weighted_cash_atom_le_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The true source Cash atom tsum is finite from its original horizon mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (A : Set ℝ) (hA : A.Countable)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (htotal : ((dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ))) Set.univ =
        ENNReal.ofReal (rightLimit D T ω))
    (q : ℝ) (hq : 0 ≤ q) :
    (∑' a : A, (if a.1 ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) * μatom {a.1}) ≠ ⊤ := by
  have hfinite : ((dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ))) Set.univ ≠ ⊤ := by
    rw [htotal]
    exact ENNReal.ofReal_ne_top
  have hmass :=
    avram_p4_f_assembly_original_finite_cash_atom_total
      D ω T A hA μatom μdiffuse hsplit hfinite
  have hdom :=
    avram_p4_f_assembly_original_weighted_cash_atom_le_mass
      X x D ω T μatom μdiffuse hsplit q hq A
  exact (lt_of_le_of_lt (ENNReal.tsum_le_tsum hdom)
    (lt_top_iff_ne_top.mpr hmass)).ne
