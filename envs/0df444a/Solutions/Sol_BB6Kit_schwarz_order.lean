-- Prove2me | solution 1 for BB6Kit.schwarz_order
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-24T07:01:54.011804+00:00
-- url     : https://prove2.me/submissions/626df433-fe32-4e1a-afc3-947d6a17756c

import Mathlib

namespace SW

lemma diff_iter (h : ℂ → ℂ) (hh : Differentiable ℂ h) : ∀ k : ℕ, Differentiable ℂ (iteratedDeriv k h)
  | 0 => by rw [iteratedDeriv_zero]; exact hh
  | k + 1 => by
      rw [iteratedDeriv_succ]
      exact differentiableOn_univ.mp
        ((differentiableOn_univ.mpr (diff_iter h hh k)).deriv isOpen_univ)

lemma iter_mul_z (h : ℂ → ℂ) (hh : Differentiable ℂ h) : ∀ n : ℕ,
    iteratedDeriv (n + 1) (fun z => z * h z) =
      fun z => ((n : ℂ) + 1) * iteratedDeriv n h z + z * iteratedDeriv (n + 1) h z := by
  have hd : ∀ (k : ℕ) (z : ℂ), HasDerivAt (iteratedDeriv k h) (iteratedDeriv (k + 1) h z) z := by
    intro k z
    rw [iteratedDeriv_succ]
    exact (diff_iter h hh k z).hasDerivAt
  intro n
  induction n with
  | zero =>
    rw [iteratedDeriv_one]
    funext z
    have h1 : HasDerivAt (fun z => z * h z) (1 * h z + z * deriv h z) z :=
      (hasDerivAt_id z).mul (hh z).hasDerivAt
    rw [h1.deriv, iteratedDeriv_zero, iteratedDeriv_one]
    push_cast
    ring
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    have h1 : HasDerivAt (fun z => ((n : ℂ) + 1) * iteratedDeriv n h z + z * iteratedDeriv (n + 1) h z)
        (((n : ℂ) + 1) * iteratedDeriv (n + 1) h z + (1 * iteratedDeriv (n + 1) h z + z * iteratedDeriv (n + 1 + 1) h z)) z :=
      ((hd n z).const_mul _).add ((hasDerivAt_id z).mul (hd (n + 1) z))
    rw [h1.deriv]
    push_cast
    ring

lemma factor : ∀ J : ℕ, ∀ f : ℂ → ℂ, Differentiable ℂ f → (∀ n < J, iteratedDeriv n f 0 = 0) →
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = z ^ J * g z := by
  intro J
  induction J with
  | zero =>
    intro f hf _
    exact ⟨f, hf, fun z => by simp⟩
  | succ J ih =>
    intro f hf hJ
    have hf0 : f 0 = 0 := by
      have := hJ 0 (Nat.succ_pos _)
      rwa [iteratedDeriv_zero] at this
    have hdh : Differentiable ℂ (dslope f 0) :=
      differentiableOn_univ.mp ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hf.differentiableOn)
    have hfz : ∀ z, f z = z * dslope f 0 z := by
      intro z
      have := sub_smul_dslope f 0 z
      rw [smul_eq_mul, sub_zero, hf0, sub_zero] at this
      exact this.symm
    have hfeq : f = fun z => z * dslope f 0 z := funext hfz
    have hvan : ∀ n < J, iteratedDeriv n (dslope f 0) 0 = 0 := by
      intro n hn
      have h1 := hJ (n + 1) (by omega)
      rw [hfeq, iter_mul_z _ hdh n] at h1
      simp only [zero_mul, add_zero] at h1
      have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      exact (mul_eq_zero.mp h1).resolve_left hn1
    obtain ⟨g, hg, hgz⟩ := ih (dslope f 0) hdh hvan
    refine ⟨g, hg, fun z => ?_⟩
    rw [hfz z, hgz z]
    ring

end SW

theorem solution (f : ℂ → ℂ) (hf : Differentiable ℂ f) (J : ℕ)
    (hJ : ∀ n < J, iteratedDeriv n f 0 = 0) (ρ B : ℝ) (hρ : 1 ≤ ρ)
    (hB : ∀ x : ℂ, ‖x‖ = ρ → ‖f x‖ ≤ B) :
    ‖f 1‖ ≤ B / ρ ^ J := by
  obtain ⟨g, hg, hgz⟩ := SW.factor J f hf hJ
  have hρ0 : 0 < ρ := by linarith
  have hρJ : 0 < ρ ^ J := pow_pos hρ0 J
  have hg1 : ‖g 1‖ ≤ B / ρ ^ J := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball (0 : ℂ) ρ)
      Metric.isBounded_ball hg.diffContOnCl ?_ ?_
    · intro z hz
      rw [frontier_ball (0 : ℂ) hρ0.ne', mem_sphere_zero_iff_norm] at hz
      have h1 := hB z hz
      rw [hgz z, norm_mul, norm_pow, hz] at h1
      rw [le_div_iff₀ hρJ]
      linarith
    · rw [closure_ball (0 : ℂ) hρ0.ne', mem_closedBall_zero_iff]
      simpa using hρ
  rw [hgz 1, one_pow, one_mul]
  exact hg1
