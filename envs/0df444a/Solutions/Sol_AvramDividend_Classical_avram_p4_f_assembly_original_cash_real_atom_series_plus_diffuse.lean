-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_cash_real_atom_series_plus_diffuse
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:51:18.377168+00:00
-- url     : https://prove2.me/submissions/ba38169a-8012-475e-84f7-cd03d1a02bae

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_real_atom_tsum_of_finite_total
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Finite original atomic Cash yields a real series without discarding diffuse cash. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (ρ : ℝ≥0∞) (q : ℝ) (T : ℝ≥0)
    (A : Set ℝ) (μatom μdiffuse : Measure ℝ)
    (f : ℝ → ℝ≥0∞)
    (hfinite : (∑' a : A, f a.1 * μatom {a.1}) ≠ ⊤)
    (hCashEq :
      (∫⁻ s in paymentTimes ρ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂
          (dividendMeasure D ω)).toReal =
      (∑' a : A, f a.1 * μatom {a.1}).toReal +
        (∫⁻ s : ℝ, f s ∂μdiffuse).toReal) :
    Summable (fun a : A => (f a.1 * μatom {a.1}).toReal) ∧
      (∫⁻ s in paymentTimes ρ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂
          (dividendMeasure D ω)).toReal =
      (∑' a : A, (f a.1 * μatom {a.1}).toReal) +
        (∫⁻ s : ℝ, f s ∂μdiffuse).toReal := by
  obtain ⟨hsum, hconvert⟩ :=
    avram_p4_f_assembly_original_cash_real_atom_tsum_of_finite_total
      A μatom f hfinite
  constructor
  · exact hsum
  · simpa [hconvert] using hCashEq
