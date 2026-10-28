-- Prove2me | solution 1 for AvramDividend.Classical.levy_upper_first_grid_terminal_reserve_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:11:16.67486+00:00
-- url     : https://prove2.me/submissions/0aaadf67-3ad5-4bd7-b0f0-3367965560ea

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_upper_exit_mesh_approximation
import Mathlib.Topology.Order.LeftRightNhds

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB {t : ℝ≥0 | upper < X.X t ω} τ)
    (mesh : ℕ → ℝ≥0) (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (first : ℕ → ℕ)
    (hfirst : ∀ᶠ n in atTop,
      upper < X.X ((first n : ℝ≥0) * mesh n) ω ∧
      ∀ j : ℕ, j < first n →
        ¬ upper < X.X ((j : ℝ≥0) * mesh n) ω) :
    Tendsto (fun n => X.X ((first n : ℝ≥0) * mesh n) ω) atTop
      (𝓝 (X.X τ ω)) := by
  have hge : ∀ᶠ n in atTop, τ ≤ (first n : ℝ≥0) * mesh n :=
    hfirst.mono fun n hn => hτ.1 hn.1
  have hT : Tendsto (fun n => (first n : ℝ≥0) * mesh n) atTop (𝓝[≥] τ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hge⟩
    refine tendsto_order.2 ⟨fun a ha => hge.mono fun n hn => lt_of_lt_of_le ha hn, ?_⟩
    intro b hb
    obtain ⟨δ, hδ, hk⟩ := chat03_strict_upper_exit_mesh_approximation X ω upper τ hτ (b - τ)
      (tsub_pos_of_lt hb)
    have hsmall : ∀ᶠ n in atTop, mesh n < δ := (tendsto_order.1 hmesh).2 δ hδ
    filter_upwards [hsmall, hfirst] with n hn hf
    obtain ⟨k, -, hk2, hk3⟩ := hk (mesh n) (hpos n) hn
    have hle : first n ≤ k := by
      by_contra h
      exact hf.2 k (lt_of_not_ge h) hk3
    calc (first n : ℝ≥0) * mesh n ≤ (k : ℝ≥0) * mesh n := by gcongr
      _ < τ + (b - τ) := hk2
      _ = b := add_tsub_cancel_of_le hb.le
  exact (X.rightCont ω τ).tendsto.comp hT
