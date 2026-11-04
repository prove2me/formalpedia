-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_uniform_full_grid_compact_test_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:02:10.657003+00:00
-- url     : https://prove2.me/submissions/b849ca9d-0212-4dd0-91d4-dfb762e2d929

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_full_grid_compact_test_jump_limit
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_finite_jump_cell_selectors
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_finite_selected_indices_injective
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_selected_indices_in_grid
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_selected_right_endpoint_squeeze
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_clamped_uniform_mesh_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_horizon_coverage
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_halfopen_cell_unique_index
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology AvramDividend.Classical
open scoped NNReal

/-- The complete *actual* original uniform-grid compact-test increment sum
converges pathwise to the finite genuine jump sum, under exact endpoint and
positive-time support hypotheses. Terminal extension is degenerate. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ) (hρ : 0 < ρ) (F : Finset ℝ≥0)
    (hF : ∀ t ∈ Icc (0 : ℝ≥0) T,
      ρ ≤ |Y t - Function.leftLim Y t| → t ∈ F)
    (hpos : ∀ t ∈ F, 0 < t)
    (hbound : ∀ t ∈ F, t ≤ T)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hvanish : ∀ z : ℝ, |z| < ρ → f z = 0) :
    Tendsto (fun n : ℕ =>
      ∑ i ∈ Finset.range (n + 1),
        f (Y (((i + 1 : ℕ) : ℝ≥0) *
            (T / ((n : ℝ≥0) + 1))) -
          Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
      atTop (𝓝 (∑ t ∈ F, f (Y t - Function.leftLim Y t))) := by
  classical
  let δ : ℕ → ℝ≥0 := fun n => T / ((n : ℝ≥0) + 1)
  let a : ℕ → ℕ → ℝ≥0 :=
    fun n i => if i ≤ n then (i : ℝ≥0) * δ n else T
  let b : ℕ → ℕ → ℝ≥0 :=
    fun n i => if i ≤ n then (((i + 1 : ℕ) : ℝ≥0) * δ n) else T
  have hcover : ∀ (n : ℕ), ((n : ℝ≥0) + 1) * δ n = T := by
    intro n
    exact avram_p2_a_zero_rate_uniform_horizon_coverage T n
  have hbds : ∀ n i, a n i ≤ T ∧
      a n i ≤ b n i ∧ b n i ≤ a n i + δ n := by
    intro n i
    exact avram_p2_a_zero_rate_clamped_uniform_mesh_bounds
      T (δ n) n i (hcover n)
  have hδ : Tendsto δ atTop (𝓝 (0 : ℝ≥0)) :=
    avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero T
  obtain ⟨idx, hidx, hmark⟩ :=
    avram_p2_a_zero_rate_uniform_finite_jump_cell_selectors
      Y T hT F hpos hbound
      (fun t _ => hL t) (fun t _ => hR t)
  have hinside : ∀ n, ∀ t ∈ F, idx t n ∈ Finset.range (n + 1) :=
    avram_p2_a_zero_rate_uniform_selected_indices_in_grid
      F idx (fun t ht n => (hidx t ht n).1)
  have hright : ∀ t ∈ F,
      Tendsto (fun n => (((idx t n + 1 : ℕ) : ℝ≥0) * δ n))
        atTop (𝓝 t) := by
    intro t ht
    apply avram_p2_a_zero_rate_selected_right_endpoint_squeeze
      t (fun n => (((idx t n + 1 : ℕ) : ℝ≥0) * δ n)) δ
    · intro n
      refine ⟨(hidx t ht n).2.2, ?_⟩
      calc
        (((idx t n + 1 : ℕ) : ℝ≥0) * δ n) =
            (idx t n : ℝ≥0) * δ n + δ n := by
              rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        _ ≤ t + δ n :=
          add_le_add_left (le_of_lt (hidx t ht n).2.1) (δ n)
    · exact hδ
  have hinj : ∀ᶠ n : ℕ in atTop,
      Set.InjOn (fun t => idx t n) (F : Set ℝ≥0) :=
    avram_p2_a_zero_rate_uniform_finite_selected_indices_injective
      F idx δ hright
  have hunique : ∀ n i, ∀ t ∈ F,
      a n i < t ∧ t ≤ b n i → i = idx t n := by
    intro n i t ht hcross
    by_cases hi : i ≤ n
    · have hc : (i : ℝ≥0) * δ n < t ∧
          t ≤ (((i + 1 : ℕ) : ℝ≥0) * δ n) := by
        simpa only [a, b, if_pos hi] using hcross
      exact avram_p2_a_zero_rate_uniform_halfopen_cell_unique_index
        t (δ n) i (idx t n) hc
        ⟨(hidx t ht n).2.1, (hidx t ht n).2.2⟩
    · have hleft : a n i = T := by simp [a, hi]
      have htoo : T < t := hleft ▸ hcross.1
      exact False.elim ((not_lt_of_ge (hbound t ht)) htoo)
  have hselected : ∀ t ∈ F,
      Tendsto (fun n => Y (b n (idx t n)) - Y (a n (idx t n)))
        atTop (𝓝 (Y t - Function.leftLim Y t)) := by
    intro t ht
    convert hmark t ht using 1
    funext n
    have hi : idx t n ≤ n := (hidx t ht n).1
    simp only [a, b, if_pos hi, δ]
  have hlimit :=
    avram_p2_a_zero_rate_original_full_grid_compact_test_jump_limit
      Y T a b δ
      (fun n i => (hbds n i).1)
      (fun n i => (hbds n i).2.1)
      (fun n i => (hbds n i).2.2)
      hδ hL hR ρ hρ F hF
      (fun n => Finset.range (n + 1)) idx
      hinside hinj hunique hselected f hf hvanish
  convert hlimit using 1
  funext n
  apply Finset.sum_congr rfl
  intro i hi
  have hil : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [a, b, if_pos hil, δ]
