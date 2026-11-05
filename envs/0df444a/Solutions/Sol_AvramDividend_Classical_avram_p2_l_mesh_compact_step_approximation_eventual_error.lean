-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_compact_step_approximation_eventual_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:24:36.854101+00:00
-- url     : https://prove2.me/submissions/9d7ec48a-9184-402f-8214-b2fe67a75397

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_uniform_negative_test_difference_stability
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_intrinsic_finite_test_difference_stability
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_interval_simple_test_negative_support
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_original_interval_simple_test_sum_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

/-- If one interval-step test uniformly approximates a negative-supported
test, then every sufficiently fine original grid agrees with its true
intrinsic jump sum up to twice the finite jump-count approximation error. -/
theorem solution {ι : Type*} [Fintype ι]
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (f : ℝ → ℝ) (hf : ∀ z : ℝ, -ρ < z → f z = 0)
    (a b c : ι → ℝ) (hb : ∀ i, b i ≤ -ρ)
    (hEndpoint : ∀ (i : ι) (u : ℝ≥0), 0 < u → u ≤ T →
      ρ ≤ |Y u - Function.leftLim Y u| →
      Y u - Function.leftLim Y u ≠ a i ∧
        Y u - Function.leftLim Y u ≠ b i)
    (η : ℝ) (hη : 0 ≤ η)
    (hApprox : ∀ z : ℝ,
      |f z - (∑ i : ι,
        if z ∈ Ioc (a i) (b i) then c i else 0)| ≤ η) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      ∀ᶠ n : ℕ in atTop,
        |(∑ j ∈ Finset.range (n + 1),
          f (Y (((j + 1 : ℕ) : ℝ≥0) *
                (T / ((n : ℝ≥0) + 1))) -
            Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) -
          (∑ u ∈ S, f (Y u - Function.leftLim Y u))| ≤
          2 * (S.card : ℝ) * η := by
  classical
  let g : ℝ → ℝ := fun z =>
    ∑ i : ι, if z ∈ Ioc (a i) (b i) then c i else 0
  have hfg : ∀ z : ℝ, -ρ < z → f z = g z := by
    intro z hz
    rw [hf z hz]
    exact (avram_p2_l_mesh_finite_interval_simple_test_negative_support
      a b c ρ hb z hz).symm
  obtain ⟨S, hS, hStable⟩ :=
    avram_p2_l_mesh_uniform_negative_test_difference_stability
      Y T hT ρ hρ hL hR
  obtain ⟨S', hS', hSteps⟩ :=
    avram_p2_l_mesh_original_interval_simple_test_sum_exact
      Y T hT a b ρ hρ hb hEndpoint hL hR
  have hSeq : S' = S := by
    ext u
    exact (hS' u).trans (hS u).symm
  refine ⟨S, hS, ?_⟩
  filter_upwards [hStable, hSteps] with n hn hm
  let A : ℝ := ∑ j ∈ Finset.range (n + 1),
    f (Y (((j + 1 : ℕ) : ℝ≥0) *
          (T / ((n : ℝ≥0) + 1))) -
      Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))
  let B : ℝ := ∑ j ∈ Finset.range (n + 1),
    g (Y (((j + 1 : ℕ) : ℝ≥0) *
          (T / ((n : ℝ≥0) + 1))) -
      Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))
  let C : ℝ := ∑ u ∈ S, g (Y u - Function.leftLim Y u)
  let D : ℝ := ∑ u ∈ S, f (Y u - Function.leftLim Y u)
  have hAB : |A - B| ≤ (S.card : ℝ) * η := by
    simpa only [A, B] using hn f g hfg η hη hApprox
  have hDC : |D - C| ≤ (S.card : ℝ) * η := by
    simpa only [D, C, g] using
      (avram_p2_l_mesh_intrinsic_finite_test_difference_stability
        Y S f g η hApprox)
  have hBC : B = C := by
    simpa only [B, C, g, hSeq] using (hm c)
  have hdecomp : A - D = (A - B) + (C - D) := by
    rw [hBC]
    ring
  calc
    _ = |A - D| := by rfl
    _ = |(A - B) + (C - D)| := by rw [hdecomp]
    _ ≤ |A - B| + |C - D| := abs_add_le _ _
    _ ≤ (S.card : ℝ) * η + (S.card : ℝ) * η := by
      apply add_le_add hAB
      simpa only [abs_sub_comm] using hDC
    _ = 2 * (S.card : ℝ) * η := by ring
