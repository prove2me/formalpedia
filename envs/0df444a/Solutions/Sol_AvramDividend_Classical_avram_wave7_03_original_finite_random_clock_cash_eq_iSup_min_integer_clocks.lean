-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_cash_eq_iSup_min_integer_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:41:15.08893+00:00
-- url     : https://prove2.me/submissions/01ec9ee1-4872-4f78-9366-83350162dd73

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Finite random-clock truncations eventually retain the entire stopped
    Stieltjes payout, including a possible atom at the clock itself. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ : ℝ≥0) (q : ℝ) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    ⨆ n : ℕ,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Iic ((min τ (((n + 1 : ℕ) : ℝ≥0)) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) := by
  let F : ℝ≥0 → ℝ≥0∞ := fun u =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (u : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hMono : Monotone F := by
    intro u v huv
    apply MeasureTheory.lintegral_mono_set
    intro t ht
    have huvReal : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv
    exact ⟨ht.1, (Set.mem_Iic.mp ht.2).trans huvReal⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, τ ≤ ((n + 1 : ℕ) : ℝ≥0) := by
    obtain ⟨n, hnReal⟩ := exists_nat_ge (τ : ℝ)
    refine ⟨n, ?_⟩
    have hn : τ ≤ (n : ℝ≥0) := by exact_mod_cast hnReal
    exact hn.trans (by exact_mod_cast Nat.le_succ n)
  have hMin : min τ (((n + 1 : ℕ) : ℝ≥0)) = τ := min_eq_left hn
  change F τ = ⨆ m : ℕ, F (min τ (((m + 1 : ℕ) : ℝ≥0)))
  apply le_antisymm
  · calc
      F τ = F (min τ (((n + 1 : ℕ) : ℝ≥0))) := by rw [hMin]
      _ ≤ ⨆ m : ℕ, F (min τ (((m + 1 : ℕ) : ℝ≥0))) :=
        le_iSup_of_le n le_rfl
  · apply iSup_le
    intro m
    exact hMono (min_le_left _ _)
