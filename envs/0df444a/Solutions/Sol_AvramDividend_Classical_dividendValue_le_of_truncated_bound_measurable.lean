-- Prove2me | solution 1 for AvramDividend.Classical.dividendValue_le_of_truncated_bound_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T23:16:05.088741+00:00
-- url     : https://prove2.me/submissions/81c2ced0-52d1-4c80-8aee-4ac21812ae71

import Theorems.Thm_AvramDividend_Classical_paymentTimes_iUnion_bounded
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ) (M : ℝ≥0∞)
    (hMeas : ∀ n : ℕ, Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ M) :
    dividendValue X q x D ≤ M  := by
  let g : Ω → ℕ → ℝ≥0∞ := fun ω n =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hmono : ∀ ω, Monotone (g ω) := by
    intro ω n m hnm
    apply lintegral_mono_set
    intro t ht
    refine ⟨ht.1, ?_⟩
    change t ≤ (m : ℝ)
    have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    exact le_trans ht.2 hnmR
  have hdir (ω : Ω) :
      Directed (· ⊆ ·)
        (fun n : ℕ => paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ)) := by
    intro n m
    refine ⟨max n m, ?_, ?_⟩
    · intro t ht
      refine ⟨ht.1, ?_⟩
      change t ≤ ((max n m : ℕ) : ℝ)
      have hR : (n : ℝ) ≤ ((max n m : ℕ) : ℝ) := by exact_mod_cast (le_max_left n m)
      exact le_trans ht.2 hR
    · intro t ht
      refine ⟨ht.1, ?_⟩
      change t ≤ ((max n m : ℕ) : ℝ)
      have hR : (m : ℝ) ≤ ((max n m : ℕ) : ℝ) := by exact_mod_cast (le_max_right n m)
      exact le_trans ht.2 hR
  have hpoint (ω : Ω) :
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
        ⨆ n : ℕ, g ω n := by
    rw [← paymentTimes_iUnion_bounded (ruinTime X x D ω)]
    exact setLIntegral_iUnion_of_directed
      (μ := dividendMeasure D ω)
      (f := fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t))))
      (hdir ω)
  have heq :
      dividendValue X q x D = ∫⁻ ω, ⨆ n : ℕ, g ω n ∂P := by
    unfold dividendValue
    congr 1
    funext ω
    exact hpoint ω
  rw [heq, lintegral_iSup (fun n => hMeas n) (by
    intro n m hnm ω
    exact hmono ω hnm)]
  exact iSup_le (fun n => hBound n)
