-- Prove2me | solution 1 for Corless.eq_of_foldVector_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:44:05.635221+00:00
-- url     : https://prove2.me/submissions/6ab6fead-913d-4189-9cd3-ca1bbc8caf43

module
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Set.Card
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Definitions.Def_LeanPool_CorlessNilpotent_Vectors
public import Theorems.Thm_Corless_length_foldVector
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
theorem _root_.solution {α : Type*} {u v : List α} {a b c d : α}
    (h : foldVector u a b = foldVector v c d) : u = v := by
  have lengths := congrArg List.length h
  simp only [length_foldVector] at lengths
  simp only [foldVector, List.append_assoc] at h
  exact (List.append_inj h (by omega)).1
end Corless
