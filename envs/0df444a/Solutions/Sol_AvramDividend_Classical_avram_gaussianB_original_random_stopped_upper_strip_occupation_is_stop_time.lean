-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_random_stopped_upper_strip_occupation_is_stop_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:16:13.418199+00:00
-- url     : https://prove2.me/submissions/cec461bb-30f3-4c75-a95c-af12a7463d4c

import Mathlib.Topology.Instances.NNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_true_stopped_upper_strip_occupation_equals_physical_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal
noncomputable section
/-- Genuine physical time occupation of the strict upper strip equals the original stop time. -/
theorem solution
    {Ω : Type*} (A : Set Ω)
    (ρ : Ω → ℝ≥0) (n : ℕ) (b : ℝ)
    (f : ℝ≥0 → Ω → ℝ)
    (hρpos : ∀ ω ∈ A, 0 < ρ ω)
    (hρn : ∀ ω ∈ A, ρ ω ≤ (n : ℝ≥0))
    (hFloor : ∀ ω ∈ A, ∀ s : ℝ≥0,
      0 < s → s < ρ ω → b < f s ω) :
    ∀ ω ∈ A,
      (∫ t in Ioo (0 : ℝ) (n : ℝ),
        (if t < (ρ ω : ℝ) ∧ b < f (Real.toNNReal t) ω
          then (1 : ℝ) else 0) ∂volume) = (ρ ω : ℝ) := by
  intro ω hω
  have hPos : (0 : ℝ) < (ρ ω : ℝ) :=
    NNReal.coe_pos.mpr (hρpos ω hω)
  have hBound : (ρ ω : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (hρn ω hω)
  have hReal : ∀ t : ℝ, 0 < t → t < (ρ ω : ℝ) →
      b < f (Real.toNNReal t) ω := by
    intro t ht hlt
    have htNN : 0 < Real.toNNReal t :=
      Real.toNNReal_pos.mpr ht
    have hltNN : Real.toNNReal t < ρ ω :=
      (Real.toNNReal_lt_iff_lt_coe ht.le).2 hlt
    exact hFloor ω hω (Real.toNNReal t) htNN hltNN
  exact
    avram_gaussianB_true_stopped_upper_strip_occupation_equals_physical_horizon
      (ρ ω : ℝ) (n : ℝ) b hPos hBound
      (fun t : ℝ => f (Real.toNNReal t) ω) hReal
