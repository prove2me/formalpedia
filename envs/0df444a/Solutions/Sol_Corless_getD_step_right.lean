-- Prove2me | solution 1 for Corless.getD_step_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:27.984124+00:00
-- url     : https://prove2.me/submissions/337f0a6d-7f0b-429c-be68-3b4f88a64b0b

module
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Set.Card
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Definitions.Def_LeanPool_CorlessNilpotent_Vectors
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_zero
public import Theorems.Thm_Corless_entrySign_I
public import Theorems.Thm_Corless_entrySign_one
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero
attribute [local simp] Corless.entrySign_I
attribute [local simp] Corless.entrySign_one



set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Corless
namespace Corless
theorem _root_.solution (u : List ℂ) (a b : ℂ) {i : ℕ} (hi : i < u.length) :
    (foldVector u a b).getD (2 * u.length + 1 - i) 1 = u.getD i 1 := by
  rw [foldVector, List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
    List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_cons, List.length_nil]
  rw [show 2 * u.length + 1 - i - u.length - (0 + 1 + 1) = u.length - 1 - i by omega,
    List.getD_reverse _ (by omega), show u.length - 1 - (u.length - 1 - i) = i by omega]
end Corless
