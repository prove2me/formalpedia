-- Prove2me | solution 1 for Champernowne.prefix_of_prefix_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:43.822564+00:00
-- url     : https://prove2.me/submissions/4dcc6afe-e610-42b4-a66f-80320c3640c9

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {α : Type*} {w a c : List α}
    (h : w <+: a ++ c) (hl : w.length ≤ a.length) : w <+: a := by
  obtain ⟨t, ht⟩ := h
  have h1 : (a ++ c).take w.length = w := by
    rw [← ht]
    exact List.take_left ..
  have h2 : w = a.take w.length :=
    h1.symm.trans (List.take_append_of_le_length hl)
  rw [h2]
  exact List.take_prefix _ _
end Champernowne
