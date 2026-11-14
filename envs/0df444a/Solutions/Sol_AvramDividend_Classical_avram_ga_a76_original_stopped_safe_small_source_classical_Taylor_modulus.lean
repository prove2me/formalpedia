-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a76_original_stopped_safe_small_source_classical_Taylor_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:11:14.246524+00:00
-- url     : https://prove2.me/submissions/3af0f45e-12d9-4231-8e47-72afb6276746

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a47_original_small_source_increment_enlarged_compact_band
import Theorems.Thm_AvramDividend_Classical_avram_ga_a75_original_postpayment_classical_C2_spatial_taylor_finite_mesh_modulus
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original pre-stop safe-source Gaussian cells with small raw increments have arbitrarily small classical C2 Taylor quadratic energy error in every finite grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbCap : ENNReal.ofReal (b + a / 2) < C)
    (hDiff : ∀ z ∈ Icc (a / 2) (b + a / 2), DifferentiableAt ℝ w z)
    (hBand : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, s < ρ ω →
      x + X.X s ω - rightLimit D s ω ∈ Icc a b) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᵐ ω ∂P, ∀ (S : Finset ℕ) (s t : ℕ → ℝ≥0),
        (∀ i ∈ S, s i < ρ ω ∧
          X.X (t i) ω - X.X (s i) ω ≠ 0 ∧
          |X.X (t i) ω - X.X (s i) ω| < δ) →
        let Y : ℕ → ℝ := fun i =>
          x + X.X (s i) ω - rightLimit D (s i) ω
        let Z : ℕ → ℝ := fun i =>
          x + X.X (t i) ω - rightLimit D (s i) ω
        let R : ℕ → ℝ := fun i => X.X (t i) ω - X.X (s i) ω
        |∑ i ∈ S, (w (Z i) - w (Y i) -
          deriv w (Y i) * R i -
          (iteratedDeriv 2 w (Y i) * (R i)^2) / 2)| ≤
          ε * ∑ i ∈ S, (R i)^2 := by
  intro ε hε
  have ha2 : 0 < a / 2 := by linarith
  have hab2 : a / 2 ≤ b + a / 2 := by linarith
  obtain ⟨δ0,hδ0,hTaylor⟩ :=
    avram_ga_a75_original_postpayment_classical_C2_spatial_taylor_finite_mesh_modulus
      X x D hD C w hw (a / 2) (b + a / 2) ha2 hab2 hbCap hDiff ε hε
  let δ : ℝ := min δ0 (a / 2)
  have hδ : 0 < δ := lt_min hδ0 ha2
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hBand] with ω hω
  intro S s t hCells
  let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
  let Z : ℕ → ℝ := fun i => x + X.X (t i) ω - rightLimit D (s i) ω
  let R : ℕ → ℝ := fun i => X.X (t i) ω - X.X (s i) ω
  have hGood (i : ℕ) (hi : i ∈ S) :
      Y i ∈ Icc (a / 2) (b + a / 2) ∧
      Z i ∈ Icc (a / 2) (b + a / 2) ∧
      Y i ≠ Z i ∧ dist (Z i) (Y i) < δ0 := by
    rcases hCells i hi with ⟨hs,hne,hsmall⟩
    have hb := hω (s i) hs
    have hFirst : Y i ∈ Icc (a / 2) (b + a / 2) := by
      change a / 2 ≤ Y i ∧ Y i ≤ b + a / 2
      change a ≤ Y i ∧ Y i ≤ b at hb
      constructor <;> linarith [hb.1,hb.2]
    have hDelta : |X.X (t i) ω - X.X (s i) ω| ≤ a / 2 :=
      le_trans hsmall.le (min_le_right _ _)
    have hSecond : Z i ∈ Icc (a / 2) (b + a / 2) := by
      exact avram_ga_a47_original_small_source_increment_enlarged_compact_band
        X x D ω (s i) (t i) a b (a / 2) ha ha2.le (le_refl _)
        hb hDelta
    have hNe : Y i ≠ Z i := by
      intro h
      apply hne
      change Y i = Z i at h
      dsimp [Y,Z] at h
      linarith
    have hDist : dist (Z i) (Y i) < δ0 := by
      rw [Real.dist_eq]
      have hEq : Z i - Y i = X.X (t i) ω - X.X (s i) ω := by
        dsimp [Y,Z]
        ring
      rw [hEq]
      exact lt_of_lt_of_le hsmall (min_le_left _ _)
    exact ⟨hFirst,hSecond,hNe,hDist⟩
  have hBound := hTaylor ω S s Z hGood
  have hDiffEq (i : ℕ) : Z i - Y i = R i := by
    dsimp [Y,Z,R]
    ring
  change |∑ i ∈ S, (w (Z i) - w (Y i) -
      deriv w (Y i) * R i -
      (iteratedDeriv 2 w (Y i) * (R i)^2) / 2)| ≤
      ε * ∑ i ∈ S, (R i)^2
  convert hBound using 1
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hDiffEq i]
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hDiffEq i]
