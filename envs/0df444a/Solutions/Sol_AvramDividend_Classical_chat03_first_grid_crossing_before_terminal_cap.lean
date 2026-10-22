-- Prove2me | solution 1 for AvramDividend.Classical.chat03_first_grid_crossing_before_terminal_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T14:19:01.814483+00:00
-- url     : https://prove2.me/submissions/96a6acaa-3e8f-45fc-8a6e-511698de8366

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_strict_exit_approaches_infimum
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
A terminal grid cap extending at least one time unit beyond a finite
continuous first strict exit must eventually include the genuine minimal
sampled strict crossing on any positive vanishing mesh sequence.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcap : ∀ᶠ n in atTop, τ + 1 ≤ (m n : ℝ≥0) * mesh n) :
    ∀ᶠ n in atTop,
      ∃ k : ℕ, k ≤ m n ∧
        (X.X ((k : ℝ≥0) * mesh n) ω < lower ∨
         upper < X.X ((k : ℝ≥0) * mesh n) ω) ∧
        (∀ j : ℕ, j < k →
          ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
             upper < X.X ((j : ℝ≥0) * mesh n) ω)) := by
  obtain ⟨δ, hδ, hfine⟩ :=
    chat03_first_grid_strict_exit_approaches_infimum
      X ω lower upper τ hτ 1 zero_lt_one
  have hIio : Set.Iio δ ∈ 𝓝 (0 : ℝ≥0) :=
    isOpen_Iio.mem_nhds hδ
  filter_upwards [hmesh.eventually hIio, hcap] with n hn hcapn
  obtain ⟨k, _, hkε, hkExit, hkfirst⟩ :=
    hfine (mesh n) (hpos n) hn
  have htime : ((k : ℝ≥0) * mesh n) <
      (m n : ℝ≥0) * mesh n :=
    lt_of_lt_of_le hkε hcapn
  have hkm : k ≤ m n := by
    by_contra h
    have hmk : m n < k := Nat.lt_of_not_ge h
    have hmk' : (m n : ℝ≥0) < (k : ℝ≥0) := by
      exact_mod_cast hmk
    have hreverse :=
      mul_lt_mul_of_pos_right hmk' (hpos n)
    exact (not_lt_of_ge (le_of_lt htime)) hreverse
  exact ⟨k, hkm, hkExit, hkfirst⟩
