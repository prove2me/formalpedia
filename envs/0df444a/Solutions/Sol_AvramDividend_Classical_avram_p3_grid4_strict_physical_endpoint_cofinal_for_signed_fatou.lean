-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_strict_physical_endpoint_cofinal_for_signed_fatou
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:52:23.290201+00:00
-- url     : https://prove2.me/submissions/d33c1fb8-eaad-42e1-904a-7881736e01dc

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Pointwise
import Mathlib.Topology.Order.OrderClosed
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped Topology
noncomputable section

/-- The strict physical dividend-grid endpoints approach the genuine horizon from below. -/
theorem solution (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let u : ℕ → ℝ := fun n => T - δ n
    Monotone u ∧ (∀ n, 0 ≤ u n) ∧
      (∀ n, u n ≤ T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < u n) := by
  dsimp
  obtain ⟨hpos, hle, hanti, hlim⟩ :=
    avram_p3_grid3_strict_prefix_margin_sequence T hT
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let u : ℕ → ℝ := fun n => T - δ n
  have huT : Tendsto u atTop (𝓝 T) := by
    simpa only [u, sub_zero] using (tendsto_const_nhds.sub hlim)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab
    change T - δ a ≤ T - δ b
    exact sub_le_sub_left (hanti hab) T
  · intro n
    change 0 ≤ T - δ n
    exact sub_nonneg.mpr (hle n)
  · intro n
    change T - δ n ≤ T
    exact sub_le_self T (le_of_lt (hpos n))
  · intro s hs
    have he : ∀ᶠ n : ℕ in atTop, s < u n :=
      huT.eventually (Ioi_mem_nhds hs)
    obtain ⟨n, hn⟩ := he.exists
    exact ⟨n, hn⟩
