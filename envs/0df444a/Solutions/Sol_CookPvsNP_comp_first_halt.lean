-- Prove2me | solution 1 for CookPvsNP.comp_first_halt
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T08:35:51.15698+00:00
-- url     : https://prove2.me/submissions/893ea022-608e-4471-ac03-716c82cb8fbf

import Theorems.Thm_CookPvsNP_comp_first_frame_step
import Theorems.Thm_CookPvsNP_tm_run_eq_of_halting

set_option autoImplicit false

open CookPvsNP

private theorem run_add {Γ : Type} (M : TM Γ) (a b : ℕ) (c : Cfg Γ M.Q) :
    M.run (a + b) c = M.run a (M.run b c) := Function.iterate_add_apply _ _ _ _

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

private theorem first_run {S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)
    (c : Cfg Γ₁ M₁.Q) (n : ℕ)
    (hn : ∀ i < n, ¬ M₁.IsHalting (M₁.run i c)) :
    (compTM j₁ j₂ M₁ M₂).run (3 * n) (compFirstCfg c) = compFirstCfg (M₁.run n c) := by
  exact blocks M₁.step (compTM j₁ j₂ M₁ M₂).step compFirstCfg M₁.IsHalting
    (comp_first_frame_step j₁ j₂ M₁ M₂) n c hn

/-- If the first source machine halts by n steps, its final configuration is
reached in the first phase after 3*m composite steps for some m <= n. -/
theorem solution {S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)
    (c : Cfg Γ₁ M₁.Q) (n : ℕ) (hn : M₁.IsHalting (M₁.run n c)) :
    ∃ m ≤ n, (compTM j₁ j₂ M₁ M₂).run (3 * m) (compFirstCfg c) =
      compFirstCfg (M₁.run n c) := by
  classical
  let hex : ∃ m, M₁.IsHalting (M₁.run m c) := ⟨n, hn⟩
  let m := Nat.find hex
  have hm : m ≤ n := Nat.find_min' hex hn
  have hstop : M₁.IsHalting (M₁.run m c) := Nat.find_spec hex
  have heq : M₁.run n c = M₁.run m c := by
    conv_lhs => rw [show n = (n - m) + m by omega]
    rw [run_add, tm_run_eq_of_halting M₁ _ hstop]
  refine ⟨m, hm, ?_⟩
  rw [heq]
  exact first_run j₁ j₂ M₁ M₂ c m (fun i hi => Nat.find_min hex hi)

#print axioms solution
