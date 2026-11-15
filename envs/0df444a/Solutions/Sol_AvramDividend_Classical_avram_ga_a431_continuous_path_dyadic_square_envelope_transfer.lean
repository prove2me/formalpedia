-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a431_continuous_path_dyadic_square_envelope_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:11:51.812679+00:00
-- url     : https://prove2.me/submissions/df27e894-bdcf-40f5-9069-d8339924ec09

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a430_nonnegative_dyadic_grid_approximates_window_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} (M : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (ω : Ω)
    (hcont : Continuous (fun t : ℝ≥0 => M t ω))
    (S : ℝ)
    (hgrid : ∀ k : ℕ,
      (Finset.range (2^k + 1)).sup' (by simp)
        (fun i => (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2) ≤ S) :
    ∀ t : ℝ≥0, t ≤ T → (M t ω)^2 ≤ S := by
  intro t ht
  by_cases hTzero : T = 0
  · have ht0 : t = 0 := le_antisymm (by simpa [hTzero] using ht) bot_le
    subst t
    have h0 := Finset.le_sup'
      (f := fun (i : ℕ) => (M ((i : ℝ≥0) * T / (2^0 : ℝ≥0)) ω)^2)
      (Finset.mem_range.mpr (by norm_num : 0 < 2^0 + 1))
    exact le_trans (by simpa using h0) (hgrid 0)
  · have hTpos : 0 < T := lt_of_le_of_ne bot_le (Ne.symm hTzero)
    obtain ⟨idx,hidx,hconv⟩ :=
      avram_ga_a430_nonnegative_dyadic_grid_approximates_window_time
        T hTpos t ht
    have hcell (k : ℕ) :
        (M ((idx k : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2 ≤ S := by
      exact le_trans
        (Finset.le_sup' (f := fun (i : ℕ) =>
          (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le (hidx k))))
        (hgrid k)
    have hconvval : Filter.Tendsto
        (fun k : ℕ => (M ((idx k : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2)
        Filter.atTop (nhds ((M t ω)^2)) :=
      ((hcont.tendsto t).comp hconv).pow 2
    exact le_of_tendsto hconvval (Filter.Eventually.of_forall hcell)
