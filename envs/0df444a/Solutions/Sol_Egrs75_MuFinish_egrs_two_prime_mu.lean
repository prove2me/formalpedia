-- Prove2me | solution 1 for Egrs75.MuFinish.egrs_two_prime_mu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:43:55.481904+00:00
-- url     : https://prove2.me/submissions/e09b52d5-a781-4c0e-96bf-cd3b385eabdf

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
public import Theorems.Thm_Egrs75_MuFinish_align_to_crux
public import Theorems.Thm_Egrs75_MuFinish_align_finish_mu
public import Theorems.Thm_Egrs75_egrs_two_prime_of_crux


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
theorem _root_.solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    {n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n}.Infinite :=
  egrs_two_prime_of_crux hp hq hpo hqo
    (align_to_crux (align_finish_mu hp hq hpo hqo hpq))
end Egrs75.MuFinish
