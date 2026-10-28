-- Prove2me | solution 1 for CosmologyEOS.cosmological_constant_exponential_expansion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:27:15.493477+00:00
-- url     : https://prove2.me/submissions/9cf46d02-72c5-4e74-8f22-cf7c7fc38776

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology
open CosmologyEOS

theorem solution (G : ℝ) (hG : 0 < G) (a ε p : ℝ → ℝ)
    (ha_diff : ∀ t, DifferentiableAt ℝ a t)
    (hε_diff : ∀ t, DifferentiableAt ℝ ε t)
    (ha_pos : ∀ t, 0 < a t)
    (heos : ∀ t, p t = -1 * ε t)
    (hfluid : ∀ t, FluidEquation a ε p t)
    (hfried : ∀ t, FlatFriedmannEquation G a ε t) :
    ∃ H C : ℝ, 0 < C ∧ H ^ 2 = 8 * π * G / 3 * ε 0 ∧
      ∀ t, a t = C * Real.exp (H * t) ∧ ε t = ε 0 := by
  have hεc : ∀ t, ε t = ε 0 := by
    intro t
    apply is_const_of_deriv_eq_zero (fun t => hε_diff t)
    intro x; rw [hfluid x, heos x]; ring
  set L : ℝ → ℝ := fun t => Real.log (a t) with hL
  have hLd : ∀ t, HasDerivAt L (deriv a t / a t) t := fun t =>
    (ha_diff t).hasDerivAt.log (ha_pos t).ne'
  have hsq : ∀ t, (deriv a t / a t) ^ 2 = 8 * π * G / 3 * ε 0 := by
    intro t; rw [← hεc t]; exact hfried t
  set H := deriv a 0 / a 0 with hH
  have hconst : ∀ t, deriv a t / a t = H := by
    intro t
    have h2 : (deriv a t / a t) ^ 2 = H ^ 2 := by rw [hsq, hsq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exact h
    · by_cases hH0 : H = 0
      · rw [h, hH0, neg_zero]
      exfalso
      have hoc : Set.OrdConnected (deriv L '' Set.univ) :=
        Set.OrdConnected.image_deriv Set.ordConnected_univ
          (fun x _ => (hLd x).differentiableAt)
      have hm1 : deriv a t / a t ∈ deriv L '' Set.univ := ⟨t, trivial, (hLd t).deriv⟩
      have hm2 : H ∈ deriv L '' Set.univ := ⟨0, trivial, (hLd 0).deriv⟩
      have h0 : (0:ℝ) ∈ Set.uIcc (deriv a t / a t) H := by
        rw [h, Set.mem_uIcc]
        rcases lt_or_gt_of_ne hH0 with hh | hh
        · right; constructor <;> linarith
        · left; constructor <;> linarith
      obtain ⟨s, -, hs⟩ := hoc.uIcc_subset hm1 hm2 h0
      rw [(hLd s).deriv] at hs
      have := hsq s
      rw [hs, ← hsq 0] at this
      apply hH0
      have : H ^ 2 = 0 := by rw [← hH] at this; linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  have hLin : ∀ t, L t - H * t = L 0 - H * 0 := by
    intro t
    have hd : ∀ x, HasDerivAt (fun t => L t - H * t) (deriv a x / a x - H * 1) x :=
      fun x => (hLd x).sub ((hasDerivAt_id x).const_mul H)
    apply is_const_of_deriv_eq_zero (f := fun t => L t - H * t)
    · intro x; exact (hd x).differentiableAt
    · intro x
      rw [(hd x).deriv, hconst x]; ring
  refine ⟨H, a 0, ha_pos 0, by rw [← hsq 0], fun t => ⟨?_, hεc t⟩⟩
  have := hLin t
  simp only [hL, mul_zero, sub_zero] at this
  have e : Real.log (a t) = Real.log (a 0) + H * t := by linarith
  rw [← Real.exp_log (ha_pos t), e, Real.exp_add, Real.exp_log (ha_pos 0)]
