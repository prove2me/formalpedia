-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger133_original_stopped_mesh_terminal_contact_and_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:02:16.313203+00:00
-- url     : https://prove2.me/submissions/b2b9ee3b-eb62-4cf7-8e12-3d9d041adbac

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger86_original_terminal_payment_cancel
import Theorems.Thm_AvramDividend_Classical_avram_gledger87_original_strict_rightlimit_le_later_dividend
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ : ℝ≥0) (v : ℕ → ℝ≥0) (k : ℕ)
    (hvk : v k < ρ) (hstop : v (k + 1) = ρ)
    (htail : ∀ i : ℕ, k < i → v i = ρ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) :
    let A : ℕ → ℝ := fun i =>
      Real.exp (-(q * (v (i + 1) : ℝ))) *
        (w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
         w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω))
    let term : ℝ := Real.exp (-(q * (ρ : ℝ))) *
      (w (riskProcess X x D ρ ω) -
       w (x + X.X ρ ω - rightLimit D ρ ω))
    A k + term ≤ 0 ∧ ∀ i : ℕ, k < i → A i = 0 := by
  dsimp only
  have hDiv := avram_gledger87_original_strict_rightlimit_le_later_dividend
    D hD ω (v k) ρ hvk
  constructor
  · have ht := avram_gledger86_original_terminal_payment_cancel
      X x D ω ρ (v k) hDiv w C hTopCap hw0 hw_cont
      hw_neg hw_grad q
    rw [hstop]
    convert ht using 1 <;> ring
  · intro i hi
    have hi1 := htail i hi
    have hi2 := htail (i + 1) (by omega)
    simp [hi1, hi2]
