-- Prove2me | solution 1 for Egrs75.MuFinish.muVal_lt_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:41.881182+00:00
-- url     : https://prove2.me/submissions/f8abe517-e879-461f-8738-a7748f961190

module
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow
public import Definitions.Def_LeanPool_Egrs75_AddBranch
public import Definitions.Def_LeanPool_Egrs75_MoveDigits
public import Definitions.Def_LeanPool_Egrs75_Reduction
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SeedWindow
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
public import Mathlib.Data.Nat.Totient
public import Definitions.Def_LeanPool_Egrs75_MuFinish
public import Theorems.Thm_Egrs75_P4_strictGoodAt_leastGoodAbove
public import Theorems.Thm_Egrs75_P4_topBad_lt_leastGoodAbove


set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.MuFinish
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
open Egrs75.P4
namespace Egrs75.MuFinish
theorem _root_.solution {q : ℕ} (hq3 : 3 ≤ q) {n n' : ℕ} (hbad : 0 < badCountQ q n)
    (h : badCountQ q n' = 0 ∨
         ∃ hbad' : 0 < badCountQ q n',
           leastGoodAbove hq3 hbad' < leastGoodAbove hq3 hbad ∨
           (leastGoodAbove hq3 hbad' = leastGoodAbove hq3 hbad ∧
            n / q ^ (leastGoodAbove hq3 hbad) % q
              < n' / q ^ (leastGoodAbove hq3 hbad') % q)) :
    muVal q hq3 n' < muVal q hq3 n := by
  have hmn : muVal q hq3 n
      = leastGoodAbove hq3 hbad * q
        + ((q - 1) / 2 - n / q ^ (leastGoodAbove hq3 hbad) % q) := by
    simp only [muVal, dif_pos hbad]
  have hbB : n / q ^ (leastGoodAbove hq3 hbad) % q < (q - 1) / 2 :=
    strictGoodAt_leastGoodAbove hq3 hbad
  have hi1 : 1 ≤ leastGoodAbove hq3 hbad := by
    have := topBad_lt_leastGoodAbove hq3 hbad; omega
  rcases h with hzero | ⟨hbad', hcase⟩
  · have hmn' : muVal q hq3 n' = 0 := by
      simp only [muVal, dif_neg (by omega : ¬ 0 < badCountQ q n')]
    simp_all
  · have hmn' : muVal q hq3 n'
        = leastGoodAbove hq3 hbad' * q
          + ((q - 1) / 2 - n' / q ^ (leastGoodAbove hq3 hbad') % q) := by
      simp only [muVal, dif_pos hbad']
    have hb'B : n' / q ^ (leastGoodAbove hq3 hbad') % q < (q - 1) / 2 :=
      strictGoodAt_leastGoodAbove hq3 hbad'
    rw [hmn, hmn']
    rcases hcase with hlt | ⟨heq, hbb⟩
    · have key : leastGoodAbove hq3 hbad' * q + q ≤ leastGoodAbove hq3 hbad * q := by
        have hle : leastGoodAbove hq3 hbad' + 1 ≤ leastGoodAbove hq3 hbad := by omega
        calc leastGoodAbove hq3 hbad' * q + q
            = (leastGoodAbove hq3 hbad' + 1) * q := by ring
          _ ≤ leastGoodAbove hq3 hbad * q := by gcongr
      omega
    · rw [heq] at hbb hb'B ⊢; omega
end Egrs75.MuFinish
