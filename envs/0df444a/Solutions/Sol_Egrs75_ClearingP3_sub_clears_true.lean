-- Prove2me | solution 1 for Egrs75.ClearingP3.sub_clears_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:40:57.661234+00:00
-- url     : https://prove2.me/submissions/9c2e5128-3895-4859-b2b6-522addd59e51

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.Nat.Factorization.Defs
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
public import Theorems.Thm_Egrs75_ClearingP3_sub_preserves_lowDigits
public import Theorems.Thm_Egrs75_ClearingP3_sub_not_badAt_above_top

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.ClearingP3
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
namespace Egrs75.ClearingP3
theorem _root_.solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpo : Odd p)
    {N n : ℕ} (hpn : LowDigits p n) (hNn : N < n) (hbad : 0 < badCountQ q n)
    (hST : (p ^ (lowPDigitIndex p n) + 1) / 2 ≤ n % q ^ (topBadIndex q n)) :
    LowDigits p (n - (p ^ (lowPDigitIndex p n) + 1) / 2) ∧
      (∀ idx, topBadIndex q n < idx →
        ¬ BadAt q idx (n - (p ^ (lowPDigitIndex p n) + 1) / 2)) := by
  have hq1 : 1 < q := hq.one_lt
  have hn0 : n ≠ 0 := by omega
  refine ⟨sub_preserves_lowDigits hp hpo hpn hn0, ?_⟩
  intro idx hidx
  exact sub_not_badAt_above_top hq hbad hST hidx
end Egrs75.ClearingP3
