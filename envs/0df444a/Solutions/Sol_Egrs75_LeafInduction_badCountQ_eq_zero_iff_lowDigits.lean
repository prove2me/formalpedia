-- Prove2me | solution 1 for Egrs75.LeafInduction.badCountQ_eq_zero_iff_lowDigits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:48.405777+00:00
-- url     : https://prove2.me/submissions/7b5237bc-ef9c-43ed-bf02-db8046a22f8b

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_LeafInduction

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.LeafInduction
open Nat
open Egrs75
namespace Egrs75.LeafInduction
theorem _root_.solution {q n : ℕ} :
    badCountQ q n = 0 ↔ LowDigits q n := by
  unfold badCountQ badDigitsQ LowDigits
  simp_all
end Egrs75.LeafInduction
