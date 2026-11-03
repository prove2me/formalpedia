-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_overshooting_liminf_clock_pathwise_cash_le_liminf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:48:13.127198+00:00
-- url     : https://prove2.me/submissions/4a9af1ea-939d-41c4-948e-17c5a48702a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_cofinal_random_clocks_full_cash_lintegral_iSup
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Original cash at ruin is below the pointwise liminf of overshooting stopped cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (τ : ℕ → ℝ≥0∞)
    (hLiminfLower : ruinTime X x D ω ≤ (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k))) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    (⨆ n : ℕ, ⨅ k : ℕ,
      (∫⁻ t in paymentTimes (τ (n + k)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by
  classical
  let r : ℝ≥0∞ := ruinTime X x D ω
  let σ : ℕ → ℝ≥0∞ := fun n => min r (⨅ k : ℕ, τ (n + k))
  let A (n : ℕ) : ℝ≥0∞ :=
    ∫⁻ t in paymentTimes (σ n) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  let B (n : ℕ) : ℝ≥0∞ :=
    ∫⁻ t in paymentTimes (τ n) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have htailmono : Monotone (fun n : ℕ => ⨅ k : ℕ, τ (n + k)) := by
    intro n m hnm
    refine le_iInf (fun k => ?_)
    have hindex : n + ((m - n) + k) = m + k := by omega
    have hle : (⨅ j : ℕ, τ (n + j)) ≤ τ (n + ((m - n) + k)) :=
      iInf_le (fun j : ℕ => τ (n + j)) ((m - n) + k)
    simpa only [hindex] using hle
  have hσmono : Monotone σ := by
    intro n m hnm
    exact min_le_min_left r (htailmono hnm)
  have hσsup : (⨆ n : ℕ, σ n) = r := by
    calc
      (⨆ n : ℕ, σ n) =
          min r (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k)) := by
            change (⨆ n : ℕ, min r (⨅ k : ℕ, τ (n + k))) =
              min r (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k))
            rw [inf_iSup_eq]
      _ = r := min_eq_left hLiminfLower
  have hA_le (n k : ℕ) : A n ≤ B (n + k) := by
    dsimp [A, B]
    apply lintegral_mono_set
    intro t ht
    have hp : 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < σ n) := ht.1
    refine ⟨?_, ht.2⟩
    change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < τ (n + k))
    have hclock : σ n ≤ τ (n + k) :=
      (min_le_right r _).trans (iInf_le (fun j : ℕ => τ (n + j)) k)
    rcases hp.2 with hz | hlt
    · exact ⟨hp.1, Or.inl hz⟩
    · exact ⟨hp.1, Or.inr (lt_of_lt_of_le hlt hclock)⟩
  have hAinf (n : ℕ) : A n ≤ ⨅ k : ℕ, B (n + k) :=
    le_iInf (fun k => hA_le n k)
  calc
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
        (⨆ n : ℕ, A n) :=
      avram_wave7_19_original_cofinal_random_clocks_full_cash_lintegral_iSup
        X q x T D ω σ hσmono (by simpa [r] using hσsup)
    _ ≤ (⨆ n : ℕ, ⨅ k : ℕ, B (n + k)) := by
      apply iSup_le
      intro n
      exact (hAinf n).trans (le_iSup (fun j : ℕ => ⨅ k : ℕ, B (j + k)) n)
