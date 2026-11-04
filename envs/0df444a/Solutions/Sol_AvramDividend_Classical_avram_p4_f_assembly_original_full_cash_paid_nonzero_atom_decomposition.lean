-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_full_cash_paid_nonzero_atom_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:47:15.382485+00:00
-- url     : https://prove2.me/submissions/95a8556e-8d03-42a6-96b2-288e4acf8e21

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_full_real_decomposition_with_rightjump
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_nonzero_cash_atoms_exact_tsum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The true Cash decomposition uses exactly original paid nonzero singleton atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) (T : ℝ≥0) :
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)) =
        μatom + μdiffuse ∧
      NullSingletonClass μdiffuse ∧ μatom Aᶜ = 0 ∧ μdiffuse A = 0 ∧
      (∀ t : ℝ≥0, t ≤ T →
        μatom {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      Summable (fun a : {a : A //
        a.1 ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {a.1} ≠ 0} =>
        (ENNReal.ofReal (Real.exp (-(q * a.1.1))) *
          μatom {a.1.1}).toReal) ∧
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂
          (dividendMeasure D ω)).toReal =
        (∑' a : {a : A //
          a.1 ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {a.1} ≠ 0},
          (ENNReal.ofReal (Real.exp (-(q * a.1.1))) *
            μatom {a.1.1}).toReal) +
        (∫⁻ s : ℝ,
          (if s ∈ paymentTimes (ruinTime X x D ω) then
            ENNReal.ofReal (Real.exp (-(q * s))) else 0)
            ∂μdiffuse).toReal := by
  obtain ⟨A, μatom, μdiffuse, hA, hAm, hsplit, hnull,
    hμA, hμdA, hRight, hsum, hCash⟩ :=
    avram_p4_f_assembly_original_cash_full_real_decomposition_with_rightjump
      X x D hD q hq ω T
  let B : Set A := {a | a.1 ∈ paymentTimes (ruinTime X x D ω) ∧
    μatom {a.1} ≠ 0}
  have hsumB : Summable (fun a : B =>
      (ENNReal.ofReal (Real.exp (-(q * a.1.1))) *
        μatom {a.1.1}).toReal) := by
    have hs : Summable (fun a : B =>
        ((if a.1.1 ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(q * a.1.1))) else 0) *
          μatom {a.1.1}).toReal) :=
      hsum.subtype B
    have heq : (fun a : B =>
        ((if a.1.1 ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(q * a.1.1))) else 0) *
          μatom {a.1.1}).toReal) =
        (fun a : B =>
          (ENNReal.ofReal (Real.exp (-(q * a.1.1))) *
            μatom {a.1.1}).toReal) := by
      funext a
      simp [a.2.1]
    rw [heq] at hs
    exact hs
  refine ⟨A, μatom, μdiffuse, hA, hAm, hsplit, hnull, hμA,
    hμdA, hRight, hsumB, ?_⟩
  simpa only [
    avram_p4_f_assembly_original_paid_nonzero_cash_atoms_exact_tsum
      X x D ω A μatom q] using hCash
