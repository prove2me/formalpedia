-- Prove2me | solution 1 for FiniteMagmaE677.unique_left_orbit_complement_collision_gives_fixer
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-11T05:12:05.996047+00:00
-- url     : https://prove2.me/submissions/139884f7-13f7-4b19-9c09-4ab222a5db61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Fintype.Card
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Theorems.Thm_FiniteMagmaE677_backward_recurrence
import Theorems.Thm_FiniteMagmaE677_cross_boundary_collision_propagates_to_left_successor
import Theorems.Thm_FiniteMagmaE677_fixer_unique
import Theorems.Thm_FiniteMagmaE677_left_bijective

/-!
# Reduction to forward invariance of the cross-boundary collision
-/

universe u

private theorem orbit_reachable_of_injective_finite
    {α : Type u} [Fintype α] {f : α → α} (hinj : Function.Injective f)
    (x a b : α) (ha : ∃ i : ℕ, a = f^[i] x) (hb : ∃ j : ℕ, b = f^[j] x) :
    ∃ n : ℕ, b = f^[n] a := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  obtain ⟨d, hd, hperiod⟩ :=
    Function.mem_periodicPts.mp (Function.Injective.mem_periodicPts hinj x)
  have hmul : ∀ q : ℕ, f^[d * q] x = x := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [Nat.mul_succ, Function.iterate_add_apply, hperiod]
        exact ih
  let n := d * (i + 1) + j - i
  have hi_base : i ≤ d * (i + 1) + j := by
    have hd_one : 1 ≤ d := hd
    have hi_mul : i ≤ d * (i + 1) := by
      calc
        i ≤ i + 1 := Nat.le_succ i
        _ = 1 * (i + 1) := by simp
        _ ≤ d * (i + 1) := Nat.mul_le_mul_right (i + 1) hd_one
    exact hi_mul.trans (Nat.le_add_right _ _)
  have hni : n + i = d * (i + 1) + j := by
    dsimp [n]
    exact Nat.sub_add_cancel hi_base
  refine ⟨n, ?_⟩
  calc
    b = f^[j] x := hj
    _ = f^[j] (f^[d * (i + 1)] x) := by rw [hmul]
    _ = f^[j + d * (i + 1)] x := by rw [Function.iterate_add_apply]
    _ = f^[d * (i + 1) + j] x := by rw [Nat.add_comm]
    _ = f^[n + i] x := by rw [hni]
    _ = f^[n] (f^[i] x) := by rw [Function.iterate_add_apply]
    _ = f^[n] a := by rw [hi]

theorem solution
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x A : α) (_hni : op x x ≠ x)
    (hA_notin : ¬ FiniteMagmaE677.InLeftOrbit op x A)
    (hA_unique : ∀ a : α, ¬ FiniteMagmaE677.InLeftOrbit op x a → a = A)
    (hcollision : ∃ a : α,
      FiniteMagmaE677.InLeftOrbit op x a ∧ op a x = op A x) :
    FiniteMagmaE677.HasFixerAt op x := by
  by_cases hfix : FiniteMagmaE677.HasFixerAt op x
  · exact hfix
  let f : α → α := op x
  have hf_bij : Function.Bijective f :=
    FiniteMagmaE677.left_bijective op h x
  have hxA : op x A = A := by
    obtain ⟨B, hB⟩ := hf_bij.2 A
    have hB_notin : ¬ FiniteMagmaE677.InLeftOrbit op x B := by
      rintro ⟨k, hk⟩
      apply hA_notin
      refine ⟨k + 1, ?_⟩
      rw [Function.iterate_succ_apply']
      exact hB ▸ congrArg (op x) hk
    have hBA : B = A := hA_unique B hB_notin
    simpa [hBA] using hB
  have hPhi : op (op A A) A = x := by
    exact (FiniteMagmaE677.fixer_unique op h A x hxA).symm
  have hAA_ne_A : op A A ≠ A := by
    intro hAA
    have hxAeq : x = A := by simpa [hAA] using hPhi.symm
    apply hA_notin
    exact ⟨0, by simpa using hxAeq.symm⟩
  have hA_Ax : op A (op A x) = A := by
    have hE := h A A
    rw [hPhi] at hE
    exact hE.symm
  have hAx_ne_A : op A x ≠ A := by
    intro hAx
    apply hAA_ne_A
    calc
      op A A = op A (op A x) := by rw [hAx]
      _ = A := hA_Ax
  have hAx_orbit : FiniteMagmaE677.InLeftOrbit op x (op A x) := by
    by_contra hnot
    exact hAx_ne_A (hA_unique (op A x) hnot)
  obtain ⟨a, ha_orbit, ha_collision⟩ := hcollision
  have hiterate_collision : ∀ n : ℕ, op (f^[n] a) x = op A x := by
    intro n
    induction n with
    | zero => simpa [f] using ha_collision
    | succ n ih =>
        have hn_orbit : FiniteMagmaE677.InLeftOrbit op x (f^[n] a) := by
          obtain ⟨i, hi⟩ := ha_orbit
          refine ⟨n + i, ?_⟩
          dsimp [f]
          rw [Function.iterate_add_apply, hi]
        simpa [f, Function.iterate_succ_apply'] using
          FiniteMagmaE677.cross_boundary_collision_propagates_to_left_successor
            op h x A hfix hA_notin hA_unique (f^[n] a) hn_orbit ih
  have hconstant : ∀ c : α,
      FiniteMagmaE677.InLeftOrbit op x c → op c x = op A x := by
    intro c hc
    obtain ⟨n, hn⟩ :=
      orbit_reachable_of_injective_finite hf_bij.1 x a c ha_orbit hc
    rw [hn]
    exact hiterate_collision n
  have hxb_orbit : FiniteMagmaE677.InLeftOrbit op x (op x (op A x)) := by
    obtain ⟨k, hk⟩ := hAx_orbit
    refine ⟨k + 1, ?_⟩
    rw [Function.iterate_succ_apply', ← hk]
  have hxxb_orbit :
      FiniteMagmaE677.InLeftOrbit op x (op x (op x (op A x))) := by
    obtain ⟨k, hk⟩ := hxb_orbit
    refine ⟨k + 1, ?_⟩
    rw [Function.iterate_succ_apply', ← hk]
  have hxb : op (op x (op A x)) x = op A x :=
    hconstant _ hxb_orbit
  have hxxb : op (op x (op x (op A x))) x = op A x :=
    hconstant _ hxxb_orbit
  have hrec := FiniteMagmaE677.backward_recurrence op h (op A x) x
  rw [hxxb] at hrec
  have hsame :
      op (op x (op A x)) x = op (op x (op A x)) (op A x) := by
    exact hxb.trans hrec
  have hx_eq_Ax : x = op A x :=
    (FiniteMagmaE677.left_bijective op h (op x (op A x))).1 hsame
  exact ⟨A, hx_eq_Ax.symm⟩
