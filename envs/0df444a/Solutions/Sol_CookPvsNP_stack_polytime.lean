-- Prove2me | solution 1 for CookPvsNP.stack_polytime
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T12:09:39.842428+00:00
-- url     : https://prove2.me/submissions/e1726829-56dd-4683-bf81-da2de1d71c21

import Definitions.Def_CookPvsNP_StackRepresentation
import Theorems.Thm_CookPvsNP_stack_setup
import Theorems.Thm_CookPvsNP_stack_run
import Theorems.Thm_CookPvsNP_stack_cleanup
import Theorems.Thm_CookPvsNP_stack_output
import Theorems.Thm_CookPvsNP_comp_budget
import Theorems.Thm_CookPvsNP_tm_run_eq_of_halting

set_option autoImplicit false
open CookPvsNP

private theorem initial_rep {K A Q : Type} [DecidableEq K]
    (P : StackMachine K A Q) (ki : K) (w : List A) :
    StackRep (w.map (stackInitialCol ki) ++ [stackZero]) (P.init ki w).store := by
  intro k
  by_cases hk : k = ki
  · simp [StackMachine.init, hk, stackPad, stackInitialCol, stackZero,
      List.map_map, Function.comp_def]
  · simp [StackMachine.init, hk, stackPad, stackInitialCol, stackZero,
      List.map_map, Function.comp_def, List.replicate_succ']

theorem solution {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (f : List A → List A) (k : ℕ)
    (h : ∀ w : List A, ∃ m, m ≤ w.length ^ k + k ∧
      P.done ((P.step^[m]) (P.init ki w)).state = true ∧
      ((P.step^[m]) (P.init ki w)).store ko = f w) : PolyTimeComputable f := by
  classical
  obtain ⟨b, hb⟩ := comp_budget k 2
  refine ⟨StackSym K A, inferInstance, stackInput, stackOutput, stackTM P ki ko, b, ?_⟩
  intro w
  let M := stackTM P ki ko
  let r := w.map (stackInitialCol ki) ++ [stackZero]
  have hlen : r.length = w.length + 1 := by simp [r]
  obtain ⟨m, hm, hd, ho⟩ := h w
  let c := (P.step^[m]) (P.init ki w)
  obtain ⟨t, r', ht, hn, hpos, hrep, hr⟩ :=
    stack_run P ki ko m (P.init ki w) r (by simp [r]) (initial_rep P ki w)
  have hs := stack_setup P ki ko w
  cases r' with
  | nil => simp at hpos
  | cons x xs =>
    have hc := stack_cleanup P ki ko c.state x xs hd
    let out := (x :: xs).map (fun v => (v ko).map (StackSym.output (K := K))) ++ [none]
    let final : Cfg (StackSym K A) (StackQ K A Q) :=
      ⟨.accept, [some .origin], out.headD none, out.tail⟩
    let N := (2 * (x :: xs).length + 2) + (t + (2 * w.length + 4))
    have hall : M.run N (M.init (w.map stackInput)) = final := by
      have h1 := (congrArg (M.run t) hs).trans hr
      have h2 := (congrArg (M.run (2 * (x :: xs).length + 2)) h1).trans hc
      unfold TM.run at h2 ⊢
      dsimp only [M, stackTM] at h2 ⊢
      dsimp only [N]
      rw [Function.iterate_add_apply _ (2 * (x :: xs).length + 2) (t + (2 * w.length + 4)),
        Function.iterate_add_apply _ t (2 * w.length + 4)]
      exact h2
    have hN : N ≤ w.length ^ b + b := by
      apply le_trans _ (hb w.length)
      rw [hlen] at hn ht
      unfold stackTime at ht
      dsimp only [N]
      have hsq : m * m ≤ (w.length ^ k + k) * (w.length ^ k + k) := Nat.mul_self_le_mul_self hm
      have hmul := Nat.mul_le_mul_left (2 * w.length + 3) hm
      nlinarith
    have hf : M.IsHalting final := by simp [TM.IsHalting, M, stackTM, final]
    have hlong : M.run (w.length ^ b + b) (M.init (w.map stackInput)) = final := by
      rw [show w.length ^ b + b = (w.length ^ b + b - N) + N by omega]
      unfold TM.run at hall ⊢
      dsimp only [M, stackTM] at hall ⊢
      rw [Function.iterate_add_apply, hall]
      exact tm_run_eq_of_halting M final hf _
    constructor
    · change M.IsHalting (M.run _ _) 
      rw [hlong]
      exact hf
    · change M.output (M.run _ _) = _
      rw [hlong]
      have hout := stack_output P ki ko (x :: xs) c.store hrep
      change c.store ko = f w at ho
      rw [ho] at hout
      exact hout

#print axioms solution
