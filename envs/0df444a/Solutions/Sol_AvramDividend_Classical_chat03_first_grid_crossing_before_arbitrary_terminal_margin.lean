-- Prove2me | solution 1 for AvramDividend.Classical.chat03_first_grid_crossing_before_arbitrary_terminal_margin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:21:25.450059+00:00
-- url     : https://prove2.me/submissions/160a9d69-7c0b-4bb2-a4ae-15a38bd8f227

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
Any positive terminal margin beyond the continuous strict exit suffices
to capture the earliest sampled crossing on all sufficiently fine grids.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ ε : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hε : 0 < ε)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcap : ∀ᶠ n in atTop, τ + ε ≤ (m n : ℝ≥0) * mesh n) :
    ∀ᶠ n in atTop,
      ∃ k : ℕ, k ≤ m n ∧
        (X.X ((k : ℝ≥0) * mesh n) ω < lower ∨
         upper < X.X ((k : ℝ≥0) * mesh n) ω) ∧
        (∀ j : ℕ, j < k →
          ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
             upper < X.X ((j : ℝ≥0) * mesh n) ω)) := by
  obtain ⟨δ, hδ, hfine⟩ :=
    chat03_first_grid_strict_exit_approaches_infimum
      X ω lower upper τ hτ ε hε
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
    have hreverse := mul_lt_mul_of_pos_right hmk' (hpos n)
    exact (not_lt_of_ge (le_of_lt htime)) hreverse
  exact ⟨k, hkm, hkExit, hkfirst⟩
