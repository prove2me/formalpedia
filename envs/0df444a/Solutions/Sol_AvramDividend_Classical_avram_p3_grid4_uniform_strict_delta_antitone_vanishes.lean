-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_uniform_strict_delta_antitone_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:17:24.489269+00:00
-- url     : https://prove2.me/submissions/16bf9c99-aea0-48dc-bddb-0faab8758719

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original strict physical horizon deficits are positive, bounded,
    antitone, and vanish along the same uniform mesh used by the BV proof. -/
theorem solution (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    (∀ n, 0 < δ n ∧ δ n ≤ T) ∧
    Antitone δ ∧ Tendsto δ atTop (𝓝 (0 : ℝ)) := by
  dsimp
  constructor
  · intro n
    constructor
    · positivity
    · have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 2)).2
      nlinarith [mul_nonneg (le_of_lt hT) hn]
  constructor
  · intro m n hmn
    have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    apply (div_le_div_iff₀ hn hm).2
    nlinarith [mul_nonneg (le_of_lt hT) (sub_nonneg.mpr hcast)]
  · have hco :=
      (avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon T hT).2
    have hconst : Tendsto (fun _ : ℕ => T) atTop (𝓝 T) :=
      tendsto_const_nhds
    have h := hconst.sub hco
    convert h using 1
    · funext n
      ring
    · ring
