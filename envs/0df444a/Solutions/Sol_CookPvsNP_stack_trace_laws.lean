-- Prove2me | solution 1 for CookPvsNP.stack_trace_laws
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:24:44.331246+00:00
-- url     : https://prove2.me/submissions/051f2c5c-39b4-4076-9088-5a5f015b2178

import Definitions.Def_CookPvsNP_StackProgram

set_option autoImplicit false
open CookPvsNP

private theorem trace_run {K A Q : Type} (P : StackMachine K A Q) {n : ℕ}
    {c d : StackCfg K A Q} (h : StackTrace P n c d) : (P.step^[n]) c = d := by
  induction h with
  | refl => rfl
  | cons _ _ ih => simpa only [Function.iterate_succ_apply] using ih

private theorem trace_append {K A Q : Type} (P : StackMachine K A Q) {n m : ℕ}
    {c d e : StackCfg K A Q} (h : StackTrace P n c d) (h' : StackTrace P m d e) :
    StackTrace P (n + m) c e := by
  induction h with
  | refl => simpa using h'
  | cons hd _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using StackTrace.cons hd (ih h')

private theorem trace_map {K A Q R : Type} (P : StackMachine K A Q) (S : StackMachine K A R)
    (f : StackCfg K A Q → StackCfg K A R)
    (hf : ∀ c, P.done c.state = false → S.done (f c).state = false ∧ S.step (f c) = f (P.step c))
    {n : ℕ} {c d : StackCfg K A Q} (h : StackTrace P n c d) : StackTrace S n (f c) (f d) := by
  induction h with
  | refl => exact .refl _
  | @cons n c d hd ht ih =>
    exact .cons (hf c hd).1 ((hf c hd).2 ▸ ih)

theorem solution {K A Q : Type} (P : StackMachine K A Q) :
    (∀ {n : ℕ} {c d : StackCfg K A Q}, StackTrace P n c d → (P.step^[n]) c = d) ∧
    (∀ {n m : ℕ} {c d e : StackCfg K A Q}, StackTrace P n c d → StackTrace P m d e →
      StackTrace P (n + m) c e) ∧
    (∀ {R : Type} (S : StackMachine K A R) (f : StackCfg K A Q → StackCfg K A R),
      (∀ c, P.done c.state = false → S.done (f c).state = false ∧ S.step (f c) = f (P.step c)) →
      ∀ {n : ℕ} {c d : StackCfg K A Q}, StackTrace P n c d → StackTrace S n (f c) (f d)) := by
  refine ⟨trace_run P, trace_append P, ?_⟩
  intro R S f hf n c d h
  exact trace_map P S f hf h

#print axioms solution
