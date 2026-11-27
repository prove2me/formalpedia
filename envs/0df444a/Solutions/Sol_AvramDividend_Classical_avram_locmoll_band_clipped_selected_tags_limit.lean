-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_clipped_selected_tags_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:12:49.306673+00:00
-- url     : https://prove2.me/submissions/744be9c8-f1cc-44f0-8e41-2970406f1ada

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_vanishing_width_halfopen_endpoints
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    (H θ t : ℝ≥0) (ht : t ≤ θ) (m i : ℕ → ℕ)
    (hm : Tendsto m atTop atTop)
    (hcell : ∀ n,
      min ((i n : ℝ≥0) * H / ((m n : ℝ≥0) + 1)) θ < t ∧
      t ≤ min (((i n + 1 : ℕ) : ℝ≥0) * H / ((m n : ℝ≥0) + 1)) θ) :
    Tendsto (fun n => min ((i n : ℝ≥0) * H / ((m n : ℝ≥0) + 1)) θ)
      atTop (𝓝[<] t) ∧
    Tendsto (fun n => min (((i n + 1 : ℕ) : ℝ≥0) * H / ((m n : ℝ≥0) + 1)) θ)
      atTop (𝓝[Ici t] t) := by 
  let a : ℕ → ℝ≥0 := fun n => min ((i n : ℝ≥0) * H / ((m n : ℝ≥0) + 1)) θ
  let b : ℕ → ℝ≥0 := fun n => min (((i n + 1 : ℕ) : ℝ≥0) * H / ((m n : ℝ≥0) + 1)) θ
  have hw : ∀ n, b n - a n ≤ H / ((m n : ℝ≥0) + 1) := by
    intro n
    have hl : (i n : ℝ≥0) * H / ((m n : ℝ≥0) + 1) < θ := by
      by_contra! hn
      have hh := (hcell n).1
      rw [min_eq_right hn] at hh
      exact (not_lt_of_ge ht) hh
    have he : a n = (i n : ℝ≥0) * H / ((m n : ℝ≥0) + 1) := min_eq_left hl.le
    rw [he]
    calc
      _ ≤ ((i n + 1 : ℕ) : ℝ≥0) * H / ((m n : ℝ≥0) + 1) -
          (i n : ℝ≥0) * H / ((m n : ℝ≥0) + 1) :=
        tsub_le_tsub_right (min_le_left _ _) _
      _ = _ := by
        simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_div, add_tsub_cancel_left]
  have hmesh := (avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero H).comp hm
  have hwlim : Tendsto (fun n => b n - a n) atTop (𝓝 (0 : ℝ≥0)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmesh (fun _ => zero_le) hw
  exact avram_p2_34dbea70_vanishing_width_halfopen_endpoints t a b hcell hwlim
