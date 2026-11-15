-- Prove2me | solution 1 for AvramDividend.Classical.avram_b25_geometric_L1_two_gain_integrable_ae_envelopes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T01:10:48.163628+00:00
-- url     : https://prove2.me/submissions/aa324560-d79c-482a-ae3a-6e34e6eb46d1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_integrable_norm_series_integrable_total_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (G J : ℕ → Ω → ℝ)
    (hGI : ∀ k, Integrable (G k) P)
    (hJI : ∀ k, Integrable (J k) P)
    (hGgeom : ∀ k, (∫ ω, ‖G (k + 1) ω - G k ω‖ ∂P)
      ≤ ((1 : ℝ) / 2) ^ k)
    (hJgeom : ∀ k, (∫ ω, ‖J (k + 1) ω - J k ω‖ ∂P)
      ≤ ((1 : ℝ) / 2) ^ k) :
    ∃ (BG BJ : Ω → ℝ),
      Integrable BG P ∧ Integrable BJ P ∧
      (∀ᵐ ω ∂P, Summable
        (fun k : ℕ => ‖G (k + 1) ω - G k ω‖)) ∧
      (∀ᵐ ω ∂P, Summable
        (fun k : ℕ => ‖J (k + 1) ω - J k ω‖)) ∧
      (∀ k, ∀ᵐ ω ∂P, ‖G k ω‖ ≤ BG ω) ∧
      (∀ k, ∀ᵐ ω ∂P, ‖J k ω‖ ≤ BJ ω) := by
  have hgeom : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have channel (A : ℕ → Ω → ℝ)
      (hAI : ∀ k, Integrable (A k) P)
      (hr : ∀ k, (∫ ω, ‖A (k + 1) ω - A k ω‖ ∂P) ≤
        ((1 : ℝ) / 2) ^ k) :
      ∃ B : Ω → ℝ,
        Integrable B P ∧
        (∀ᵐ ω ∂P, Summable (fun k => ‖A (k + 1) ω - A k ω‖)) ∧
        (∀ k, ∀ᵐ ω ∂P, ‖A k ω‖ ≤ B ω) := by
    have hDI (k : ℕ) :
        Integrable (fun ω => A (k + 1) ω - A k ω) P :=
      (hAI (k + 1)).sub (hAI k)
    have hSum : Summable
        (fun k => ∫ ω, ‖A (k + 1) ω - A k ω‖ ∂P) :=
      Summable.of_nonneg_of_le
        (fun k => integral_nonneg (fun ω => norm_nonneg _)) hr hgeom
    obtain ⟨Q,hQI,hQsum,_⟩ :=
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
    refine ⟨(fun ω => ‖A 0 ω‖ + Q ω), (hAI 0).norm.add hQI, ?_, ?_⟩
    · filter_upwards [hQsum] with ω hω
      simpa [δ] using hω.1
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
  obtain ⟨BG,hBGI,hGsum,hGdom⟩ := channel G hGI hGgeom
  obtain ⟨BJ,hBJI,hJsum,hJdom⟩ := channel J hJI hJgeom
  exact ⟨BG,BJ,hBGI,hBJI,hGsum,hJsum,hGdom,hJdom⟩
