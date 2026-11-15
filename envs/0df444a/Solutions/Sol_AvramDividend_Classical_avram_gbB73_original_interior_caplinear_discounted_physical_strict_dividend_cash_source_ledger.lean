-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB73_original_interior_caplinear_discounted_physical_strict_dividend_cash_source_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:33:58.226799+00:00
-- url     : https://prove2.me/submissions/f4304ae9-2b87-4f0f-97ff-56e7c6923471

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB25_original_preruin_interior_caplinear_stieltjes_signed_control
import Theorems.Thm_AvramDividend_Classical_avram_gbB58_original_caplinear_initial_right_atom_signed_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

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
    (hPre : ∀ i < m + 1,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * Δ
      s (i + 1) = 0 ∨
      (s (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
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
  change
    rightLimit D 0 ω + e (m + 1) * V (Y (m + 1)) +
      (Finset.range (m + 1)).sum (fun i => e (i + 1) * cash i) ≤
      V x + (Finset.range (m + 1)).sum (fun i =>
        e (i + 1) * V (Z i) - e i * V (Y i))
  have hInit :=
    avram_gbB58_original_caplinear_initial_right_atom_signed_budget
      X x C D hD w c hsec ω
  have hInitV : rightLimit D 0 ω + V (Y 0) ≤ V x := by
    simpa only [Y, s, Nat.cast_zero, zero_mul, X.X_zero, add_zero, V] using hInit
  have hStep (i : ℕ) (hi : i < m + 1) :
      cash i + V (Y (i + 1)) - V (Z i) ≤ 0 := by
    have hle : s i ≤ s (i + 1) := by
      dsimp [s]
      exact mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Nat.le_succ i)) (by positivity)
    exact avram_gbB25_original_preruin_interior_caplinear_stieltjes_signed_control
      X x c hc C q hq w V hw_cont hw_smooth hw_grad
      (fun z => rfl) D hD ω (s i) (s (i + 1)) hle
      (hPre i hi)
  have hWeighted (i : ℕ) (hi : i < m + 1) :
      e (i + 1) * (cash i + V (Y (i + 1)) - V (Z i)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (Real.exp_pos _)) (hStep i hi)
  have hSum :
      (Finset.range (m + 1)).sum (fun i =>
        e (i + 1) * (cash i + V (Y (i + 1)) - V (Z i))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi; exact hWeighted i (Finset.mem_range.mp hi)
  have hTel (k : ℕ) :
      e k * V (Y k) - e 0 * V (Y 0) =
        (Finset.range k).sum (fun i =>
          (e (i + 1) * V (Z i) - e i * V (Y i)) +
          e (i + 1) * (V (Y (i + 1)) - V (Z i))) := by
    induction k with
    | zero => simp
    | succ k ih => simp only [Finset.sum_range_succ]; linarith
  have hTelN := hTel (m + 1)
  have he0 : e 0 = 1 := by simp [e, s]
  rw [he0, Finset.sum_add_distrib] at hTelN
  have hSumEq :
      (Finset.range (m + 1)).sum (fun i =>
        e (i + 1) * (cash i + V (Y (i + 1)) - V (Z i))) =
      (Finset.range (m + 1)).sum (fun i => e (i + 1) * cash i) +
      (Finset.range (m + 1)).sum (fun i =>
        e (i + 1) * (V (Y (i + 1)) - V (Z i))) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl
    intro i hi; ring
  rw [hSumEq] at hSum; linarith
