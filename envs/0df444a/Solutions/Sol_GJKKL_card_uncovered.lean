-- Prove2me | solution 1 for GJKKL.card_uncovered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:27.986798+00:00
-- url     : https://prove2.me/submissions/7be9b9f5-8a21-4343-9be0-f8140951bc76

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Theorems.Thm_GJKKL_IsGreedySeq_card_covered


set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution {H : Finset (Finset V)} {k : ℕ} (hk : IsUniform H k)
    {h : List (Finset V)} (hh : IsGreedySeq H h) :
    (uncovered h).card + k * h.length = Fintype.card V := by
  rw [uncovered, card_sdiff_of_subset (subset_univ _), card_univ, ← hh.card_covered hk]
  have : (covered h).card ≤ Fintype.card V := card_le_univ _
  omega
end GJKKL
