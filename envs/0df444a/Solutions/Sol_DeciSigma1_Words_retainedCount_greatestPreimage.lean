-- Prove2me | solution 1 for DeciSigma1.Words.retainedCount_greatestPreimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:45:58.495809+00:00
-- url     : https://prove2.me/submissions/e7b4f703-845e-4e2a-bf95-29e1c677076a

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_retainedCount_add_le
public import Theorems.Thm_DeciSigma1_Words_le_greatestPreimage_iff

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (a : ℕ) :
    retainedCount D (greatestPreimage D a) = a := by
  have h1 := le_greatestPreimage_iff.mp (le_refl (greatestPreimage D a))
  have h2 :=
      mt (le_greatestPreimage_iff (D := D) (p := greatestPreimage D a + 1) (a := a)).mpr (by omega)
  have := retainedCount_add_le (D := D) (greatestPreimage D a) 1
  omega
end DeciSigma1.Words
