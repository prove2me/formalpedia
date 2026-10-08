-- Prove2me | solution 2 for AvramDividend.Classical.dividendValue_eq_iSup_truncated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T17:39:43.556976+00:00
-- url     : https://prove2.me/submissions/c619b805-3fe7-4a56-b1b1-1166d327faf5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_payment_lintegral_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_truncated_dividend_path_value_aemeasurable


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D) :
    dividendValue X q x D =
      ⨆ n : ℕ,
        ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P := by
  let g : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hg : ∀ n, AEMeasurable (g n) P := by
    intro n
    exact truncated_dividend_path_value_aemeasurable X q x D hD n
  have hdir : Directed (· ≤ ·) g := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro ω
      apply MeasureTheory.lintegral_mono_set
      intro t ht
      have hij : (i : ℝ) ≤ ((max i j : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_max_left i j
      exact ⟨ht.1, ht.2.trans hij⟩
    · intro ω
      apply MeasureTheory.lintegral_mono_set
      intro t ht
      have hjij : (j : ℝ) ≤ ((max i j : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_max_right i j
      exact ⟨ht.1, ht.2.trans hjij⟩
  unfold dividendValue
  have hpoint : ∀ ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
        ⨆ n, g n ω := by
    intro ω
    exact discounted_payment_lintegral_eq_iSup_truncated
      q (ruinTime X x D ω) (dividendMeasure D ω)
  simp_rw [hpoint]
  change (∫⁻ ω, ⨆ n, g n ω ∂P) = ⨆ n, ∫⁻ ω, g n ω ∂P
  exact MeasureTheory.lintegral_iSup_directed hg hdir
