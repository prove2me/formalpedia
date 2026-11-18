-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB143_original_tube_strict_prepayment_cash_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:05:02.823561+00:00
-- url     : https://prove2.me/submissions/97e90795-6be9-4d23-ad3c-8662897e7c48

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB56_original_barrier_pre_ruin_all_short_tube_times
import Theorems.Thm_AvramDividend_Classical_avram_gbB73_original_interior_caplinear_discounted_physical_strict_dividend_cash_source_ledger
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
noncomputable section
/-- Original strict pre-ruin Stieltjes grid ledger on a narrow tube. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (C : ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hsec : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ c →
      b - a ≤ w b - w a)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (n m : ℕ)
    (T : ℝ≥0)
    (hx : x = (1 / 8 : ℝ))
    (hDbarrier : D =
      barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ T →
      |X.X t ω| ≤ (1 / 400 : ℝ))
    (hmesh : ∀ i < m + 1,
      (i + 1 : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < T) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (s i : ℝ)))
    let V : ℝ → ℝ := fun z =>
      if z ≤ c then w z else w c + (z - c)
    let Y : ℕ → ℝ := fun i =>
      x + X.X (s i) ω - rightLimit D (s i) ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (s (i + 1)) ω - rightLimit D (s i) ω
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in Ioc (s i : ℝ) (s (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
    rightLimit D 0 ω + e (m + 1) * V (Y (m + 1)) +
      (Finset.range (m + 1)).sum (fun i => e (i + 1) * cash i) ≤
      V x + (Finset.range (m + 1)).sum (fun i =>
        e (i + 1) * V (Z i) - e i * V (Y i)) := by
  have hPre : ∀ i < m + 1,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * Δ
      s (i + 1) = 0 ∨
        (s (i + 1) : ℝ≥0∞) < ruinTime X x D ω := by
    intro i hi
    dsimp only
    right
    have hRuin :=
      avram_gbB56_original_barrier_pre_ruin_all_short_tube_times
        X T ω hTube
        ((i + 1 : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)))
        (hmesh i hi)
    simpa only [hx, hDbarrier, Nat.cast_add, Nat.cast_one] using hRuin
  exact
    avram_gbB73_original_interior_caplinear_discounted_physical_strict_dividend_cash_source_ledger
      X x c hc C q hq w hw_cont hw_smooth hw_grad hsec
      D hD ω n m hPre
