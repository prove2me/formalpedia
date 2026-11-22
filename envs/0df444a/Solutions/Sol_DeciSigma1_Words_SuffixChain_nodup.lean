-- Prove2me | solution 1 for DeciSigma1.Words.SuffixChain.nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:50:57.029044+00:00
-- url     : https://prove2.me/submissions/23d093ee-fdfc-491c-8490-6363cf21c13b

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Theorems.Thm_DeciSigma1_Words_SuffixChain_pairwise

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}
variable [DecidableEq α]
namespace DeciSigma1.Words
namespace SuffixChain
theorem _root_.solution {t : List α} {bs : List ℕ} (h : SuffixChain t bs) : bs.Nodup :=
  h.pairwise.imp fun h => Nat.ne_of_lt h.1
end SuffixChain
end DeciSigma1.Words
