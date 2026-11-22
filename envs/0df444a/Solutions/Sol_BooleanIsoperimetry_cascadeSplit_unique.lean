-- Prove2me | solution 1 for BooleanIsoperimetry.cascadeSplit_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:45.586783+00:00
-- url     : https://prove2.me/submissions/5048a2db-42b2-48a8-b718-1e307a8ca15f

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_isBinomialCascade_unique

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k p q p' q' : ℕ}
    (h : CascadeSplit n k p q) (h' : CascadeSplit n k p' q') :
    p = p' ∧ q = q' := by
  obtain ⟨r, t, hbc, hp, hq⟩ := h
  obtain ⟨r', t', hbc', hp', hq'⟩ := h'
  obtain ⟨hrr, htt⟩ := isBinomialCascade_unique hbc hbc'
  subst hrr; subst htt
  exact ⟨hp.trans hp'.symm, hq.trans hq'.symm⟩
end BooleanIsoperimetry
