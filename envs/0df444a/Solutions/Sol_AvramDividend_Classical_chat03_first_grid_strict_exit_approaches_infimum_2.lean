-- Prove2me | solution 2 for AvramDividend.Classical.chat03_first_grid_strict_exit_approaches_infimum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:36:15.451355+00:00
-- url     : https://prove2.me/submissions/84669567-4f7a-4dcd-8470-0903a4ed2674

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_exit_mesh_approximation
import Mathlib.Data.Nat.Find

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
Strong mesh convergence result: the actual *first* strict grid exit index
exists for every fine mesh and approaches the continuous infimum from above.
This does not assume that the continuous first passage is attained.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → h < δ →
      ∃ k : ℕ,
        τ ≤ (k : ℝ≥0) * h ∧
        (k : ℝ≥0) * h < τ + ε ∧
        (X.X ((k : ℝ≥0) * h) ω < lower ∨
         upper < X.X ((k : ℝ≥0) * h) ω) ∧
        (∀ j : ℕ, j < k →
          ¬ (X.X ((j : ℝ≥0) * h) ω < lower ∨
             upper < X.X ((j : ℝ≥0) * h) ω)) := by
  classical
  obtain ⟨δ, hδ, hmesh⟩ :=
    chat03_strict_exit_mesh_approximation X ω lower upper τ hτ ε hε
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhd
  obtain ⟨j, hτj, hjε, hjExit⟩ := hmesh h hh hhd
  let pred : ℕ → Prop := fun n =>
    X.X ((n : ℝ≥0) * h) ω < lower ∨
      upper < X.X ((n : ℝ≥0) * h) ω
  have hex : ∃ n, pred n := ⟨j, hjExit⟩
  let k : ℕ := Nat.find hex
  have hkExit : pred k := Nat.find_spec hex
  have hklej : k ≤ j := Nat.find_min' hex hjExit
  have hkfirst : ∀ n : ℕ, n < k → ¬ pred n := by
    intro n hn
    exact Nat.find_min hex hn
  have hkj : (k : ℝ≥0) * h ≤ (j : ℝ≥0) * h := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hklej) (show 0 ≤ h from zero_le)
  have hτk : τ ≤ (k : ℝ≥0) * h :=
    hτ.1 hkExit
  refine ⟨k, hτk, lt_of_le_of_lt hkj hjε, hkExit, ?_⟩
  exact hkfirst