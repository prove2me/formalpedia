-- Prove2me | solution 1 for CookPvsNP.comp_second_halt
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T08:54:23.262929+00:00
-- url     : https://prove2.me/submissions/7e749a1d-4cb5-4d60-92f6-6b3d4ae2f6f5

import Theorems.Thm_CookPvsNP_comp_second_frame_step
import Theorems.Thm_CookPvsNP_tm_run_eq_of_halting

set_option autoImplicit false

open CookPvsNP

private theorem blocks {A B : Type} (f : A → A) (g : B → B) (e : A → B) (H : A → Prop)
    (hs : ∀ a, ¬ H a → g^[3] (e a) = e (f a))
    (n : ℕ) (a : A) (hn : ∀ i < n, ¬ H (f^[i] a)) :
    g^[3 * n] (e a) = e (f^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm, Function.iterate_add_apply,
      ih (fun i hi => hn i (Nat.lt_succ_of_lt hi)), hs _ (hn n (Nat.lt_succ_self n))]
    rw [Function.iterate_succ_apply']

private theorem right_step {A B : Type} (M : TM B) (c : CompSecondFrame A B M.Q) :
    (c.step M).right.length ≤ c.right.length + 1 := by
  by_cases h : M.IsHalting c.source
  · simp [CompSecondFrame.step, h]
  · rcases hd : M.δ c.state c.head.2 with ⟨q, w, move⟩
    cases move <;> cases hl : c.left <;> cases hr : c.right <;>
      simp [CompSecondFrame.step, h, hd, hl, hr] <;> omega

private theorem right_run {A B : Type} (M : TM B) (c : CompSecondFrame A B M.Q) (n : ℕ) :
    ((CompSecondFrame.step M)^[n] c).right.length ≤ c.right.length + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h := right_step M ((CompSecondFrame.step M)^[n] c)
    omega

/-- Simulate the second source machine only up to its first halt, retaining a
bound on the active right list needed for the cleanup phase. -/
theorem solution {S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)
    (c : CompSecondFrame Γ₁ Γ₂ M₂.Q) (n : ℕ)
    (hn : M₂.IsHalting (M₂.run n c.source)) :
    ∃ m ≤ n, ∃ d : CompSecondFrame Γ₁ Γ₂ M₂.Q,
      (compTM j₁ j₂ M₁ M₂).run (3 * m) c.encode = d.encode ∧
      d.source = M₂.run n c.source ∧ d.right.length ≤ c.right.length + n := by
  classical
  have hs : Function.Semiconj CompSecondFrame.source (CompSecondFrame.step M₂) M₂.step :=
    fun d => (comp_second_frame_step j₁ j₂ M₁ M₂ d).1
  have hsource (k : ℕ) : ((CompSecondFrame.step M₂)^[k] c).source = M₂.run k c.source :=
    hs.iterate_right k c
  let hex : ∃ m, M₂.IsHalting (M₂.run m c.source) := ⟨n, hn⟩
  let m := Nat.find hex
  have hm : m ≤ n := Nat.find_min' hex hn
  have hstop : M₂.IsHalting (M₂.run m c.source) := Nat.find_spec hex
  have heq : M₂.run n c.source = M₂.run m c.source := by
    conv_lhs => rw [show n = (n - m) + m by omega]
    change (M₂.step)^[(n - m) + m] c.source = _
    rw [Function.iterate_add_apply]
    exact tm_run_eq_of_halting M₂ _ hstop (n - m)
  refine ⟨m, hm, (CompSecondFrame.step M₂)^[m] c, ?_, ?_, ?_⟩
  · apply blocks (CompSecondFrame.step M₂) (compTM j₁ j₂ M₁ M₂).step
      CompSecondFrame.encode (fun d => M₂.IsHalting d.source)
      (fun d hd => (comp_second_frame_step j₁ j₂ M₁ M₂ d).2 hd)
    intro i hi
    rw [hsource]
    exact Nat.find_min hex hi
  · exact (hsource m).trans heq.symm
  · have h := right_run M₂ c m
    omega

#print axioms solution
