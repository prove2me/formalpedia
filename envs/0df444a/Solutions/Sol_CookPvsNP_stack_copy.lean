-- Prove2me | solution 1 for CookPvsNP.stack_copy
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:35.468368+00:00
-- url     : https://prove2.me/submissions/eaa1571c-9766-44c6-ba81-c3608b6a51b8

import Definitions.Def_CookPvsNP_StackMacros
import Theorems.Thm_CookPvsNP_stack_transfer

set_option autoImplicit false
open CookPvsNP

theorem solution {K A : Type} [DecidableEq K] (src dst scratch : K)
    (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch)
    (s : K → List A) (he : s scratch = []) :
    (copyProg src dst scratch).Exec s
      (Function.update s dst (s src ++ s dst)) (6 * (s src).length + 3) := by
  let targets₁ := fun k => decide (k = scratch)
  let targets₂ := fun k => decide (k = src ∨ k = dst)
  let mid := transferStore src targets₁ s
  have hs : mid scratch = (s src).reverse := by
    simp [mid, transferStore, targets₁, Ne.symm hst, he]
  have hf : transferStore scratch targets₂ mid = Function.update s dst (s src ++ s dst) := by
    funext k
    by_cases hk : k = src
    · subst k
      simp [transferStore, targets₂, hs, mid, targets₁, hst, hsd]
    by_cases hk' : k = dst
    · subst k
      simp [transferStore, targets₂, hs, mid, targets₁, hdt, Ne.symm hsd]
    by_cases hk'' : k = scratch
    · subst k
      simp [transferStore, Function.update_of_ne (Ne.symm hdt), he]
    · simp [transferStore, targets₂, mid, targets₁, hk, hk', hk'']
  have hp := StackProg.Exec.seq (stack_transfer src targets₁ s)
    (stack_transfer scratch targets₂ mid)
  rw [hf] at hp
  convert hp using 1 <;> first | rfl | (simp only [hs, List.length_reverse]; omega)

#print axioms solution
