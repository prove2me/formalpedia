-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_borel_physical_ceiling_grid_pair_count_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T16:08:43.655204+00:00
-- url     : https://prove2.me/submissions/a3c9e6f0-3486-4e02-b29f-c6faa5959d85

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_finite_horizon_ceiling_pairs_equal_window_card_sum
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_window_finite_marked_times_card
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_uniform_source_grid_endpoints
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hS : ({u : ℝ≥0 |
      0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}).Finite)
    (k : ℕ) (hk : 0 < k) :
    let F : Finset ℝ≥0 := hS.toFinset
    let s : Fin k → ℝ≥0 := fun i => ((i.val : ℝ≥0) * T) / (k : ℝ≥0)
    let t : Fin k → ℝ≥0 := fun i => (((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)
    let N : ℝ≥0 → ℝ≥0 → ℝ≥0∞ := fun a b =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    ((((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞) =
      ∑ i : Fin k, N 0 (s i) * N (s i) (t i) := by
  classical
  intro F s t N
  have hF : ∀ u ∈ F, 0 < u ∧ u ≤ T := by
    intro u hu
    have hmem := (hS.mem_toFinset).mp hu
    exact ⟨hmem.1, hmem.2.1⟩
  obtain ⟨hst, htT, hs, ht⟩ :=
    avram_leanlevy_bridge_uniform_source_grid_endpoints T k hk
  have hPure :
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card =
      ∑ i : Fin k,
        (F.filter (fun u : ℝ≥0 => 0 < u ∧ u ≤ s i)).card *
        (F.filter (fun v : ℝ≥0 => s i < v ∧ v ≤ t i)).card :=
    avram_a20_finite_horizon_ceiling_pairs_equal_window_card_sum
      F T hT k hk hF
  calc
    ((((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞) =
      ∑ i : Fin k,
        ((F.filter (fun u : ℝ≥0 => 0 < u ∧ u ≤ s i)).card : ℝ≥0∞) *
        ((F.filter (fun v : ℝ≥0 => s i < v ∧ v ≤ t i)).card : ℝ≥0∞) := by
      simpa only [Nat.cast_sum, Nat.cast_mul] using
        congrArg (fun n : ℕ => (n : ℝ≥0∞)) hPure
    _ = ∑ i : Fin k, N 0 (s i) * N (s i) (t i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← avram_a20_original_borel_window_finite_marked_times_card
        X ω T B hB 0 (s i) (show (0 : ℝ≥0) ≤ s i from zero_le) ((hst i).trans (htT i)) hS]
      rw [← avram_a20_original_borel_window_finite_marked_times_card
        X ω T B hB (s i) (t i) (hst i) (htT i) hS]
