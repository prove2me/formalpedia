-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_preruin_discounted_gaussian_full_grid_sqrt_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:34:27.476275+00:00
-- url     : https://prove2.me/submissions/ea8d24ac-04fa-4f27-89be-5f78395fd2b8

import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_dividend_gaussian_future_weighted_cell_L1
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_rightatoms_expected_mass_L1
import Theorems.Thm_AvramDividend_Classical_avram_agentB_gaussian_weighted_first_absolute_moment_grid_integral_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_prehorizon_grid_le
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (hBV : ¬ X.BoundedVariation) (hσ : 0 < X.σ)
    (x : ℝ) (hx : 0 ≤ x) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (q : ℝ) (hq : 0 ≤ q) :
    let V : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let H : ℝ := if s < ρ ω then
          Real.exp (-(q * (s : ℝ))) * (rightLimit D s ω - D s ω) else 0
        let Z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        H * |Z|
    ∃ K : ℝ, 0 ≤ K ∧ (∀ m, Integrable (V m) P) ∧
      ∀ m : ℕ, (∫ ω, V m ω ∂P) ≤
        K * Real.sqrt ((n : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let V : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    ∑ i ∈ Finset.range m,
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let H : ℝ := if s < ρ ω then
        Real.exp (-(q * (s : ℝ))) *
          (rightLimit D s ω - D s ω) else 0
      let Z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
      H * |Z|
  let B : ℝ := ∫ ω, x + runningSup X (n : ℝ≥0) ω ∂P
  let K : ℝ := X.σ * |B|
  have hK : 0 ≤ K := mul_nonneg (le_of_lt hσ) (abs_nonneg B)
  have hAll (m : ℕ) : Integrable (V m) P ∧
      (∫ ω, V m ω ∂P) ≤
        K * Real.sqrt ((n : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let a : ℕ → Ω → ℝ := fun i ω =>
      if s i < ρ ω then
        Real.exp (-(q * (s i : ℝ))) *
          (rightLimit D (s i) ω - D (s i) ω) else 0
    let z : ℕ → Ω → ℝ := fun i ω =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    have hΔ : 0 < Δ := by dsimp [Δ]; positivity
    have hSn (i : ℕ) (hi : i ∈ Finset.range m) : s i ≤ (n : ℝ≥0) := by
      have him : (i : ℝ≥0) ≤ m := by exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hi)
      exact (mul_le_mul_of_nonneg_right him (by positivity)).trans
        (avram_ga_a27_prehorizon_grid_le (n : ℝ≥0) m)
    have hstrict : ∀ i, s i < s (i + 1) := by
      intro i
      exact mul_lt_mul_of_pos_right
        (by exact_mod_cast Nat.lt_succ_self i) hΔ
    have hEach (i : ℕ) (hi : i ∈ Finset.range m) :
        Integrable (a i) P ∧
        Integrable (fun ω => a i ω * |z i ω|) P ∧
        (∫ ω, a i ω * |z i ω| ∂P) ≤
          (X.σ * Real.sqrt (Δ : ℝ)) * (∫ ω, a i ω ∂P) := by
      have hW := (avram_lsv_original_rightcont_discounted_preruin_single_atom_L2
        X hBV hσ x hx D hD (n : ℝ≥0) (s i) (hSn i hi)
        ρ hρstop hρruin q hq).2.1
      have hZ := avram_lsv_original_preruin_dividend_gaussian_future_weighted_cell_L1
        X hν hBV hσ x hx D hD (n : ℝ≥0) (s i) (hSn i hi)
        ρ hρstop hρruin q hq Δ hΔ
      exact ⟨hW, hZ.1, hZ.2.2⟩
    have hInt : Integrable (V m) P := by
      change Integrable (fun ω => ∑ i ∈ Finset.range m, a i ω * |z i ω|) P
      exact integrable_finset_sum (Finset.range m) (fun i hi => (hEach i hi).2.1)
    refine ⟨hInt, ?_⟩
    have hMass : (∫ ω, ∑ i ∈ Finset.range m, a i ω ∂P) ≤ B :=
      (avram_lsv_original_preruin_discounted_rightatoms_expected_mass_L1
        X hσ x hx D hD (n : ℝ≥0) ρ hρstop hρruin s hstrict
        m (fun i hi => hSn i hi) q hq).2
    have hδ : 0 ≤ X.σ * Real.sqrt (Δ : ℝ) :=
      mul_nonneg (le_of_lt hσ) (Real.sqrt_nonneg _)
    have hSum :
        (∫ ω, ∑ i ∈ Finset.range m, a i ω * |z i ω| ∂P) ≤
          (X.σ * Real.sqrt (Δ : ℝ)) * B :=
      avram_agentB_gaussian_weighted_first_absolute_moment_grid_integral_bound
        P m a z (X.σ * Real.sqrt (Δ : ℝ)) B hδ
        (fun i hi => (hEach i hi).1)
        (fun i hi => (hEach i hi).2.1)
        (fun i hi => (hEach i hi).2.2) hMass
    have hAbs : (X.σ * Real.sqrt (Δ : ℝ)) * B ≤
        K * Real.sqrt (Δ : ℝ) := by
      calc
        _ ≤ (X.σ * Real.sqrt (Δ : ℝ)) * |B| :=
          mul_le_mul_of_nonneg_left (le_abs_self B) hδ
        _ = K * Real.sqrt (Δ : ℝ) := by dsimp [K]; ring
    have hCast : (Δ : ℝ) =
        (n : ℝ) / ((m + 1 : ℕ) : ℝ) := by
      dsimp [Δ]; norm_num
    change (∫ ω, ∑ i ∈ Finset.range m, a i ω * |z i ω| ∂P) ≤
      K * Real.sqrt ((n : ℝ) / ((m + 1 : ℕ) : ℝ))
    calc
      _ ≤ (X.σ * Real.sqrt (Δ : ℝ)) * B := hSum
      _ ≤ K * Real.sqrt (Δ : ℝ) := hAbs
      _ = K * Real.sqrt ((n : ℝ) / ((m + 1 : ℕ) : ℝ)) := by rw [hCast]
  exact ⟨K, hK, (fun m => (hAll m).1), (fun m => (hAll m).2)⟩
