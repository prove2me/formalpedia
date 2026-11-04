-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_cash_real_atomic_series
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:13:58.3081+00:00
-- url     : https://prove2.me/submissions/e4201529-23a1-4026-af49-0ea1ed396cd9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_weighted_atom_tsum_ne_top
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_real_atom_tsum_of_finite_total
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Source Cash has an actual summable real atomic series. -/
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
    Summable (fun a : A => ((if a.1 ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) * μatom {a.1}).toReal) ∧
    (∑' a : A, (if a.1 ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) * μatom {a.1}).toReal =
      ∑' a : A, ((if a.1 ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) * μatom {a.1}).toReal := by
  have hfin :=
    avram_p4_f_assembly_original_cash_weighted_atom_tsum_ne_top
      X x D ω T A hA μatom μdiffuse hsplit htotal q hq
  exact avram_p4_f_assembly_original_cash_real_atom_tsum_of_finite_total
    A μatom
    (fun s => if s ∈ paymentTimes (ruinTime X x D ω) then
      ENNReal.ofReal (Real.exp (-(q * s))) else 0) hfin
