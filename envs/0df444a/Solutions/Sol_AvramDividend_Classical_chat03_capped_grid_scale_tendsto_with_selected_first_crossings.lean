-- Prove2me | solution 1 for AvramDividend.Classical.chat03_capped_grid_scale_tendsto_with_selected_first_crossings
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T14:06:25.526254+00:00
-- url     : https://prove2.me/submissions/934884fb-a118-4cf9-864f-811c73994a00

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_crossing_exists_eventually_of_mesh_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_discounted_scale_mesh_tendsto
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
A strictly finite first-passage infimum supplies an eventual selected first-grid
crossing along each positive vanishing mesh. Its capped discounted q-scale
payoff converges to the continuous capped value when W(0)=0.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (discount : ℝ≥0 → ℝ)
    (hdiscount : Continuous discount)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n) :
    ∃ first : ℕ → ℕ,
      (∀ᶠ n in atTop,
        (X.X ((first n : ℝ≥0) * mesh n) ω < lower ∨
         upper < X.X ((first n : ℝ≥0) * mesh n) ω) ∧
        (∀ j : ℕ, j < first n →
          ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
             upper < X.X ((j : ℝ≥0) * mesh n) ω))) ∧
      Tendsto (fun n =>
        discount (min ((first n : ℝ≥0) * mesh n) T) *
          W (x + X.X (min ((first n : ℝ≥0) * mesh n) T) ω))
        atTop
        (𝓝 (discount (min τ T) * W (x + X.X (min τ T) ω))) := by
  classical
  let Good : ℕ → ℕ → Prop := fun n k =>
    (X.X ((k : ℝ≥0) * mesh n) ω < lower ∨
      upper < X.X ((k : ℝ≥0) * mesh n) ω) ∧
    (∀ j : ℕ, j < k →
      ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
         upper < X.X ((j : ℝ≥0) * mesh n) ω))
  have hfound : ∀ᶠ n in atTop, ∃ k : ℕ, Good n k := by
    exact chat03_first_grid_crossing_exists_eventually_of_mesh_tendsto
      X ω lower upper τ hτ mesh hmesh hpos
  let first : ℕ → ℕ := fun n =>
    if h : ∃ k : ℕ, Good n k then Classical.choose h else 0
  have hchosen : ∀ᶠ n in atTop, Good n (first n) := by
    filter_upwards [hfound] with n hn
    change Good n (if h : ∃ k : ℕ, Good n k then Classical.choose h else 0)
    rw [dif_pos hn]
    exact Classical.choose_spec hn
  refine ⟨first, hchosen, ?_⟩
  exact chat03_capped_grid_discounted_scale_mesh_tendsto
    X q W hW hzero ω lower upper x τ T hτ
      discount hdiscount mesh hmesh hpos first hchosen
