-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_generic_geometric_L1_gain_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:56:03.486187+00:00
-- url     : https://prove2.me/submissions/3bf7190d-a0b3-41a9-b838-5cdd55b4a45e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_integrable_norm_series_integrable_total_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (G J E : ℕ → Ω → ℝ)
    (hG0 : Integrable (G 0) P) (hJ0 : Integrable (J 0) P)
    (hGI : ∀ k, Integrable (fun ω => G (k + 1) ω - G k ω) P)
    (hJI : ∀ k, Integrable (fun ω => J (k + 1) ω - J k ω) P)
    (hEI : ∀ k, Integrable (E k) P)
    (hGr : ∀ k, (∫ ω, ‖G (k + 1) ω - G k ω‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k)
    (hJr : ∀ k, (∫ ω, ‖J (k + 1) ω - J k ω‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k)
    (hEr : ∀ k, (∫ ω, ‖E k ω‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k) :
    ∃ (MG MJ BG BJ : Ω → ℝ),
      (∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (MG ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => J k ω) atTop (𝓝 (MJ ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => E k ω) atTop (𝓝 (0 : ℝ))) ∧
      Integrable BG P ∧ Integrable BJ P ∧
      (∀ k, ∀ᵐ ω ∂P, ‖G k ω‖ ≤ BG ω) ∧
      (∀ k, ∀ᵐ ω ∂P, ‖J k ω‖ ≤ BJ ω) := by
  have hgeom : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have channel (A : ℕ → Ω → ℝ)
      (hA0 : Integrable (A 0) P)
      (hDI : ∀ k, Integrable (fun ω => A (k + 1) ω - A k ω) P)
      (hr : ∀ k, (∫ ω, ‖A (k + 1) ω - A k ω‖ ∂P) ≤
        ((1 : ℝ) / 2) ^ k) :
      ∃ (L B : Ω → ℝ),
        (∀ᵐ ω ∂P, Tendsto (fun k => A k ω) atTop (𝓝 (L ω))) ∧
        Integrable B P ∧
        (∀ k, ∀ᵐ ω ∂P, ‖A k ω‖ ≤ B ω) := by
    have hSum : Summable (fun k => ∫ ω, ‖A (k + 1) ω - A k ω‖ ∂P) :=
      Summable.of_nonneg_of_le
        (fun k => integral_nonneg (fun ω => norm_nonneg _)) hr hgeom
    obtain ⟨Q, hQI, hQsum, _⟩ :=
      avram_b24_integrable_norm_series_integrable_total_envelope
        (fun k ω => A (k + 1) ω - A k ω) hDI hSum
    let δ : Ω → ℕ → ℝ := fun ω k => A (k + 1) ω - A k ω
    have htel (ω : Ω) : ∀ k, A k ω =
        A 0 ω + ∑ i ∈ Finset.range k, δ ω i := by
      intro k
      induction k with
      | zero => simp [δ]
      | succ k ih =>
        calc
          A (k + 1) ω = A k ω + δ ω k := by simp [δ]
          _ = A 0 ω + (∑ i ∈ Finset.range k, δ ω i) + δ ω k := by rw [ih]
          _ = A 0 ω + ∑ i ∈ Finset.range (k + 1), δ ω i := by
            rw [Finset.sum_range_succ]
            ring
    refine ⟨(fun ω => A 0 ω + (∑' k, δ ω k)),
      (fun ω => ‖A 0 ω‖ + Q ω), ?_, hA0.norm.add hQI, ?_⟩
    · filter_upwards [hQsum] with ω hω
      have hs : Summable (δ ω) := hω.1.of_norm
      simpa only [← htel ω] using
        (hs.hasSum.tendsto_sum_nat.const_add (A 0 ω))
    · intro k
      filter_upwards [hQsum] with ω hω
      have hs : Summable (fun i => ‖δ ω i‖) := hω.1
      calc
        ‖A k ω‖ = ‖A 0 ω + ∑ i ∈ Finset.range k, δ ω i‖ := by
          rw [htel ω k]
        _ ≤ ‖A 0 ω‖ + ‖∑ i ∈ Finset.range k, δ ω i‖ :=
          norm_add_le _ _
        _ ≤ ‖A 0 ω‖ + ∑ i ∈ Finset.range k, ‖δ ω i‖ := by
          gcongr
          exact norm_sum_le _ _
        _ ≤ ‖A 0 ω‖ + ∑' i, ‖δ ω i‖ := by
          gcongr
          exact hs.sum_le_tsum (Finset.range k) (fun i _ => norm_nonneg _)
        _ ≤ ‖A 0 ω‖ + Q ω := by
          gcongr
          simpa [δ] using hω.2
  obtain ⟨MG, BG, hGlim, hBG, hGdom⟩ := channel G hG0 hGI hGr
  obtain ⟨MJ, BJ, hJlim, hBJ, hJdom⟩ := channel J hJ0 hJI hJr
  have hEsum : Summable (fun k => ∫ ω, ‖E k ω‖ ∂P) :=
    Summable.of_nonneg_of_le
      (fun k => integral_nonneg (fun ω => norm_nonneg _)) hEr hgeom
  obtain ⟨Q, hQI, hQsum, _⟩ :=
    avram_b24_integrable_norm_series_integrable_total_envelope E hEI hEsum
  have hElim : ∀ᵐ ω ∂P, Tendsto (fun k => E k ω) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hQsum] with ω hω
    exact (hω.1.of_norm).tendsto_atTop_zero
  exact ⟨MG, MJ, BG, BJ, hGlim, hJlim, hElim, hBG, hBJ, hGdom, hJdom⟩
