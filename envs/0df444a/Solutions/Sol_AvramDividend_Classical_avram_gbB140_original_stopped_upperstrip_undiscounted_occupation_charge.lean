-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB140_original_stopped_upperstrip_undiscounted_occupation_charge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T22:07:06.327417+00:00
-- url     : https://prove2.me/submissions/c72af04d-4b17-4a33-afb2-e5a2ecbb98bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB139_original_stopped_upperstrip_positive_drift_finitegrid_sum_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) (hq : 0 ≤ q) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
    let Z : ℕ → ℝ := fun i => x + X.X (s i + Δ) ω - rightLimit D (s i) ω
    let V : ℝ → ℝ := fun y => if y ≤ b then w y else w b + (y - b)
    let centred : ℕ → ℝ := fun i =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (s i : ℝ)))
    (Finset.range (m + 1)).sum (fun i =>
      if s i < ρ ∧ b < Y i ∧ b < Z i then
        e i * (V (Z i) - V (Y i) - centred i) else 0) ≤
    (Finset.range (m + 1)).sum (fun i =>
      if s i < ρ ∧ b < Y i ∧ b < Z i then
        (Δ : ℝ) * max X.c 0 else 0) := by
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
  let Z : ℕ → ℝ := fun i => x + X.X (s i + Δ) ω - rightLimit D (s i) ω
  let V : ℝ → ℝ := fun y => if y ≤ b then w y else w b + (y - b)
  let centred : ℕ → ℝ := fun i =>
    X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
  let e : ℕ → ℝ := fun i => Real.exp (-(q * (s i : ℝ)))
  change (Finset.range (m + 1)).sum (fun i =>
      if s i < ρ ∧ b < Y i ∧ b < Z i then
        e i * (V (Z i) - V (Y i) - centred i) else 0) ≤
    (Finset.range (m + 1)).sum (fun i =>
      if s i < ρ ∧ b < Y i ∧ b < Z i then
        (Δ : ℝ) * max X.c 0 else 0)
  calc
    _ ≤ (Finset.range (m + 1)).sum (fun i =>
        if s i < ρ ∧ b < Y i ∧ b < Z i then
          e i * (Δ : ℝ) * max X.c 0 else 0) :=
      avram_gbB139_original_stopped_upperstrip_positive_drift_finitegrid_sum_bound
        X x b q w D ω n m ρ
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hp : s i < ρ ∧ b < Y i ∧ b < Z i
      · simp only [if_pos hp]
        have hqn : 0 ≤ q * (s i : ℝ) :=
          mul_nonneg hq (by positivity)
        have he : e i ≤ 1 := by
          dsimp [e]
          exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqn)
        have hd : 0 ≤ (Δ : ℝ) := by positivity
        have hc : 0 ≤ max X.c 0 := le_max_right _ _
        calc
          e i * (Δ : ℝ) * max X.c 0 ≤
              1 * (Δ : ℝ) * max X.c 0 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right he hd) hc
          _ = (Δ : ℝ) * max X.c 0 := by ring
      · simp only [if_neg hp, le_refl]
