-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_uniform_negative_test_difference_stability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:51:32.956921+00:00
-- url     : https://prove2.me/submissions/07cf6815-d236-4b43-babd-bbb5e60f3403

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_uniform_all_negative_test_sum_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

/-- Uniformly approximating a negative-supported test function changes the
original-grid test sum by at most the finite significant-jump count times
the test approximation error, on all sufficiently fine meshes. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      ∀ᶠ n : ℕ in atTop, ∀ f g : ℝ → ℝ,
        (∀ z : ℝ, -ρ < z → f z = g z) →
        ∀ δ : ℝ, 0 ≤ δ → (∀ z : ℝ, |f z - g z| ≤ δ) →
        |(∑ i ∈ Finset.range (n + 1),
          f (Y (((i + 1 : ℕ) : ℝ≥0) *
                (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) -
          (∑ i ∈ Finset.range (n + 1),
          g (Y (((i + 1 : ℕ) : ℝ≥0) *
                (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))| ≤
          (S.card : ℝ) * δ := by
  classical
  obtain ⟨S, hS, hBound⟩ :=
    avram_p2_l_mesh_uniform_all_negative_test_sum_envelope Y T hT ρ hρ hL hR
  refine ⟨S, hS, ?_⟩
  filter_upwards [hBound] with n hn
  intro f g hfg δ hδ hdiff
  have hzero : ∀ z : ℝ, -ρ < z → f z - g z = 0 := by
    intro z hz
    rw [hfg z hz]
    exact sub_self _
  have hb := hn (fun z => f z - g z) hzero δ hδ hdiff
  simpa only [Finset.sum_sub_distrib] using hb
