-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_uniform_test_zero_outside_all_large_jump_cells
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:20:55.865173+00:00
-- url     : https://prove2.me/submissions/7b8937a2-b5f9-49de-9727-9186827861bf

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_horizon_coverage
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_uniform_grid_no_spurious_large_cell_increment
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_right_closed_grid_cell_locator_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

/-- For negative tests separated from the origin, any eventually
nonzero fine grid cell contains an actual large jump in its unique cell. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ) (f : ℝ → ℝ)
    (hfzero : ∀ z : ℝ, |z| < ρ → f z = 0)
    (S : Finset ℝ≥0)
    (hS : ∀ t : ℝ≥0, 0 < t → t ≤ T →
      ρ ≤ |Y t - Function.leftLim Y t| → t ∈ S)
    (j : ℝ≥0 → ℕ → ℕ)
    (hj : ∀ u ∈ S, ∀ n : ℕ,
      j u n ≤ n ∧
      (j u n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
      u ≤ (((j u n + 1 : ℕ) : ℝ≥0) *
        (T / ((n : ℝ≥0) + 1))))
    (hL : ∀ t, t ≤ T →
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t, t ≤ T → ContinuousWithinAt Y (Ici t) t) :
    ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ Finset.range (n + 1),
        i ∉ S.image (fun u => j u n) →
        f (Y ((((i + 1 : ℕ) : ℝ≥0) *
          (T / ((n : ℝ≥0) + 1)))) -
          Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))) = 0 := by
  classical
  obtain ⟨N, hN⟩ :=
    avram_p2_h_cadlag_uniform_grid_no_spurious_large_cell_increment
      Y T hT ρ hρ hL hR
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn i hi hin
  have hinat : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  let δ : ℝ≥0 := T / ((n : ℝ≥0) + 1)
  have hbT : (((i + 1 : ℕ) : ℝ≥0) * δ) ≤ T := by
    calc
      (((i + 1 : ℕ) : ℝ≥0) * δ) ≤ ((n : ℝ≥0) + 1) * δ := by
        gcongr
        exact_mod_cast (Nat.succ_le_succ hinat)
      _ = T := avram_p2_a_zero_rate_uniform_horizon_coverage T n
  by_contra hfnonzero
  have hbig : ρ ≤
      |Y ((((i + 1 : ℕ) : ℝ≥0) * δ)) - Y ((i : ℝ≥0) * δ)| := by
    apply le_of_not_gt
    intro hsmall
    exact hfnonzero (hfzero _ hsmall)
  obtain ⟨t, htL, htR, htbig⟩ :=
    hN n hn i hinat (by simpa only [δ] using hbig)
  have htpos : (0 : ℝ≥0) < t :=
    lt_of_le_of_lt (show (0 : ℝ≥0) ≤ (i : ℝ≥0) * δ from zero_le) htL
  have htT : t ≤ T := le_trans htR hbT
  have htS : t ∈ S := hS t htpos htT htbig
  obtain ⟨_, htLj, htRj⟩ := hj t htS n
  have hji : j t n = i :=
    avram_p2_h_cadlag_right_closed_grid_cell_locator_unique
      δ t (j t n) i htLj htRj htL htR
  have himage : i ∈ S.image (fun u => j u n) :=
    Finset.mem_image.mpr ⟨t, htS, hji⟩
  exact hin himage
