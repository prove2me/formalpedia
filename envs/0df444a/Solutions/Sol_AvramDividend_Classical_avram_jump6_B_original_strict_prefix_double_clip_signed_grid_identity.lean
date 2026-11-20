-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_strict_prefix_double_clip_signed_grid_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:27:28.722082+00:00
-- url     : https://prove2.me/submissions/b5cded22-af6b-4b5b-a071-ba3957d9b329

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_canonical_earlier_prefix_equal_after_double_clipping
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    (j m i : ℕ) (hi : i ≤ m)
    (ρ : ℝ≥0) (g : ℝ≥0 → ℝ≥0 → ℝ)
    (hdiag : ∀ t, g t t = 0) :
    let u : ℕ → ℝ≥0 := fun k =>
      min ((k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ
    let t : ℝ≥0 := u i
    let v : ℕ → ℝ≥0 := fun k =>
      min ((k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    (∑ l ∈ Finset.range m, g (v (l + 1)) (v l)) =
      (∑ l ∈ Finset.range i, g (u (l + 1)) (u l)) := by
  let raw : ℕ → ℝ≥0 := fun k =>
    (k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
  let u : ℕ → ℝ≥0 := fun k => min (raw k) ρ
  let t : ℝ≥0 := u i
  let v : ℕ → ℝ≥0 := fun k => min (raw k) t
  have hpre (k : ℕ) (hk : k ≤ i) : v k = u k := by
    exact avram_jump6_B_actual_canonical_earlier_prefix_equal_after_double_clipping
      j i k ρ hk
  have hpost (k : ℕ) (hk : i ≤ k) : v k = t := by
    have hraw : raw i ≤ raw k := by
      dsimp [raw]
      gcongr
    have hsmall : t ≤ raw k := (min_le_left _ _).trans hraw
    exact min_eq_right hsmall
  let f : ℕ → ℝ := fun k => g (v (k + 1)) (v k)
  have hzero (k : ℕ) (hk : i ≤ k) : f k = 0 := by
    change g (v (k + 1)) (v k) = 0
    rw [hpost k hk, hpost (k+1) (by omega)]
    exact hdiag t
  have hsum :
      (∑ k ∈ Finset.range m, f k) =
        (∑ k ∈ Finset.range i, f k) := by
    calc
      (∑ k ∈ Finset.range m, f k) =
        (∑ k ∈ Finset.range i, f k) +
        (∑ k ∈ Finset.range (m-i), f (i+k)) := by
          simpa only [Nat.add_sub_of_le hi] using
            (Finset.sum_range_add f i (m-i))
      _ = (∑ k ∈ Finset.range i, f k) := by
          simp [hzero]
  change (∑ k ∈ Finset.range m, f k) =
    ∑ k ∈ Finset.range i, g (u (k+1)) (u k)
  rw [hsum]
  apply Finset.sum_congr rfl
  intro k hk
  have hki : k < i := Finset.mem_range.mp hk
  change g (v (k+1)) (v k) = g (u (k+1)) (u k)
  rw [hpre k (by omega), hpre (k+1) (by omega)]
