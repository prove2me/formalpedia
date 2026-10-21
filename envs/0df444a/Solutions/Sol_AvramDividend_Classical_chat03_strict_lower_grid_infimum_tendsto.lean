-- Prove2me | solution 1 for AvramDividend.Classical.chat03_strict_lower_grid_infimum_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T21:53:44.169464+00:00
-- url     : https://prove2.me/submissions/881d44c0-8441-413d-bc38-93137f408a24

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_lower_exit_mesh_approximation
import Theorems.Thm_AvramDividend_Classical_chat03_tendsto_first_passage_of_mesh_brackets
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Genuine strict lower grid first-passage infima converge along
arbitrary positive mesh sequences tending to zero.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB {t : ℝ≥0 | X.X t ω < lower} τ)
    (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)))
    (σ : ℕ → ℝ≥0)
    (hσ : ∀ n, IsGLB
      {s : ℝ≥0 | ∃ k : ℕ,
        s = (k : ℝ≥0) * mesh n ∧
        (X.X s ω < lower)} (σ n)) :
    Tendsto σ atTop (𝓝 τ) := by
  apply chat03_tendsto_first_passage_of_mesh_brackets
    τ mesh σ hzero
  intro ε hε
  obtain ⟨δ, hδ, hgrid⟩ :=
    chat03_strict_lower_exit_mesh_approximation
      X ω lower τ hτ ε hε
  refine ⟨δ, hδ, ?_⟩
  intro n hn
  obtain ⟨k, hτk, hkε, hkCross⟩ :=
    hgrid (mesh n) (hpos n) hn
  have hτlb : τ ∈ lowerBounds
      {s : ℝ≥0 | ∃ k : ℕ,
        s = (k : ℝ≥0) * mesh n ∧
        (X.X s ω < lower)} := by
    intro s hs
    obtain ⟨j, hj, hsCross⟩ := hs
    exact hτ.1 hsCross
  have hleft : τ ≤ σ n := (hσ n).2 hτlb
  have hright : σ n ≤ (k : ℝ≥0) * mesh n :=
    (hσ n).1 ⟨k, rfl, hkCross⟩
  exact ⟨hleft, lt_of_le_of_lt hright hkε⟩
