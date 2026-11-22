-- Prove2me | solution 1 for DeciSigma1.Words.PeriodicOn.transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:19.543773+00:00
-- url     : https://prove2.me/submissions/624f779e-4734-42e9-950d-331fe19c90e9

module
public import Mathlib.Data.List.PeriodicityLemma
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
variable {α : Type*}
namespace DeciSigma1.Words
namespace PeriodicOn
theorem _root_.solution {w w' : List α} {p s e : ℕ}
    (h : PeriodicOn w p s e)
    (hw : ∀ q < e, w'[q]? = w[q]?) : PeriodicOn w' p s e := by
  intro q hq hqe
  rw [hw q (by omega), hw (q + p) hqe]
  exact h q hq hqe
end PeriodicOn
end DeciSigma1.Words
