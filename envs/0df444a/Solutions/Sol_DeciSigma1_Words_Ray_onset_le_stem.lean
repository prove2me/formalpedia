-- Prove2me | solution 1 for DeciSigma1.Words.Ray.onset_le_stem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:47.679802+00:00
-- url     : https://prove2.me/submissions/114f29bc-349b-40ad-a48e-81c58f359e5b

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Words (pow)
variable {α : Type}
open DeciSigma1.Words.Ray
variable (Ω : Ray α)
variable {Ω}
variable [DecidableEq α]
namespace DeciSigma1.Words.Ray
theorem _root_.solution : Ω.onset ≤ Ω.stem.length :=
  Nat.find_min' Ω.exists_onsetAt (fun t ht => by omega)
end DeciSigma1.Words.Ray
