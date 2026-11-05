-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_compact_test_convergence_of_step_approximations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:37:24.657085+00:00
-- url     : https://prove2.me/submissions/e0475d26-7d28-4dc4-be26-317d13fe585f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_step_approximation_eventual_error

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

/-- An explicit uniformly dense family of marked-step tests with endpoint
avoidance yields genuine original-grid to intrinsic marked-test convergence.
The independent approximation obligation is stated without convergence. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (f : ℝ → ℝ) (hf : ∀ z : ℝ, -ρ < z → f z = 0)
    (hApprox : ∀ η : ℝ, 0 < η →
      ∃ m : ℕ, ∃ a b c : Fin m → ℝ,
        (∀ i, b i ≤ -ρ) ∧
        (∀ (i : Fin m) (u : ℝ≥0), 0 < u → u ≤ T →
          ρ ≤ |Y u - Function.leftLim Y u| →
          Y u - Function.leftLim Y u ≠ a i ∧
            Y u - Function.leftLim Y u ≠ b i) ∧
        (∀ z : ℝ,
          |f z - (∑ i : Fin m,
            if z ∈ Ioc (a i) (b i) then c i else 0)| ≤ η)) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      Tendsto (fun n : ℕ =>
        ∑ j ∈ Finset.range (n + 1),
          f (Y (((j + 1 : ℕ) : ℝ≥0) *
                (T / ((n : ℝ≥0) + 1))) -
            Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        atTop (𝓝 (∑ u ∈ S, f (Y u - Function.leftLim Y u))) := by
  classical
  let Q : Set ℝ≥0 := {u | 0 < u ∧ u ≤ T ∧
    ρ ≤ dist (Y u - Function.leftLim Y u) 0}
  have hQ : Q.Finite :=
    avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
      Y hR (fun t _ => hL t) T ρ hρ
  let S : Finset ℝ≥0 := hQ.toFinset
  have hS (u : ℝ≥0) : u ∈ S ↔ 0 < u ∧ u ≤ T ∧
      ρ ≤ |Y u - Function.leftLim Y u| := by
    simpa only [S, Q, Set.mem_setOf_eq, Real.dist_eq, sub_zero]
      using (hQ.mem_toFinset (a := u))
  refine ⟨S, hS, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  let k : ℝ := S.card
  let η : ℝ := ε / (4 * (k + 1))
  have hk : 0 ≤ k := by
    dsimp [k]
    positivity
  have hden : 0 < 4 * (k + 1) := by positivity
  have hη : 0 < η := div_pos hε hden
  obtain ⟨m, a, b, c, hb, hend, happ⟩ := hApprox η hη
  obtain ⟨S', hS', hev⟩ :=
    avram_p2_l_mesh_compact_step_approximation_eventual_error
      Y T hT ρ hρ hL hR f hf a b c hb hend η (le_of_lt hη) happ
  have hSeq : S' = S := by
    ext u
    exact (hS' u).trans (hS u).symm
  have hsmall : 2 * k * η < ε := by
    dsimp [η]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).2
    nlinarith [mul_pos hε (by linarith : 0 < 2 * k + 4)]
  have hEvent : ∀ᶠ n : ℕ in atTop,
      dist (∑ j ∈ Finset.range (n + 1),
          f (Y (((j + 1 : ℕ) : ℝ≥0) *
                (T / ((n : ℝ≥0) + 1))) -
            Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        (∑ u ∈ S, f (Y u - Function.leftLim Y u)) < ε := by
    filter_upwards [hev] with n hn
    have hn' := hn
    rw [hSeq] at hn'
    rw [Real.dist_eq]
    exact lt_of_le_of_lt hn' (by simpa only [k] using hsmall)
  exact Filter.eventually_atTop.1 hEvent
