-- Prove2me | solution 1 for Egrs75.MuFinish.egrs_crux_mu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:43:56.520893+00:00
-- url     : https://prove2.me/submissions/7ccc4460-bc60-42f1-80df-012464ad337d

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
    {n : ℕ | LowDigits p n ∧ LowDigits q n}.Infinite :=
  align_to_crux (align_finish_mu hp hq hpo hqo hpq)
end Egrs75.MuFinish
