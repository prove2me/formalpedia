-- Prove2me | solution 1 for Disjunctive.IntroDuality.intersection_cut
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:28:46.030422+00:00
-- url     : https://prove2.me/submissions/cf13a53f-fb18-4836-aa3d-ff1e73a1b824

import Mathlib
import Definitions.Def_Disjunctive_IntroDuality_IntersectionCut

set_option autoImplicit false

/- Counterexample with no nonbasic indices: `ι = Unit`, `I = J = ∅`, `xbar = 0`,
`S = {x | x () < 1}` (an open half-line), `PI = {fun _ => 1}`. Then `S` is `P_I`-free at `0`,
every hypothesis indexed by `J` is vacuous, and the cut sum over `J = ∅` is `0`, so the
claimed inequality `1 ≤ 0` fails at the point of `PI`. -/
open Disjunctive.IntroDuality in
theorem solution : ¬ (∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (I J : Finset ι) (abar : ι → ι → ℝ) (xbar : ι → ℝ) (PI S : Set (ι → ℝ))
    (hPIFree : PIFree S PI xbar)
    (hxbarJ : ∀ j ∈ J, xbar j = 0)
    (hPI_cone : ∀ x ∈ PI, ∀ j ∈ J, 0 ≤ x j)
    (lam : ι → ℝ)
    (hlam_max : ∀ j ∈ J, IsGreatest {t : ℝ | xbar + t • extremeRay I abar j ∈ S} (lam j)),
    (∑ j ∈ J, (lam j)⁻¹ * xbar j) < 1 ∧ ∀ x ∈ PI, 1 ≤ ∑ j ∈ J, (lam j)⁻¹ * x j) := by
  intro h
  have hopen : IsOpen {x : Unit → ℝ | x () < 1} :=
    isOpen_lt (continuous_apply ()) continuous_const
  have hconv : Convex ℝ {x : Unit → ℝ | x () < 1} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    rcases ha.eq_or_lt with ha0 | ha0
    · subst ha0
      have hb1 : b = 1 := by linarith
      subst hb1
      linarith
    · nlinarith [mul_lt_mul_of_pos_left hx ha0, mul_le_mul_of_nonneg_left hy.le hb]
  have hfree : PIFree {x : Unit → ℝ | x () < 1} {fun _ => (1 : ℝ)} (0 : Unit → ℝ) := by
    refine ⟨hconv, ?_, ?_⟩
    · rw [hopen.interior_eq]
      simp
    · rw [hopen.interior_eq]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro hx hx1
      rw [hx1] at hx
      exact lt_irrefl _ hx
  have key := h (ι := Unit) ∅ ∅ (fun _ _ => 0) 0 {fun _ => (1 : ℝ)}
    {x : Unit → ℝ | x () < 1} hfree (by simp) (by simp) (fun _ => 1) (by simp)
  have h2 := key.2 (fun _ => (1 : ℝ)) rfl
  simp at h2
  linarith
