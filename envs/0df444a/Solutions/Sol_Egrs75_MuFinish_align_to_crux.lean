-- Prove2me | solution 1 for Egrs75.MuFinish.align_to_crux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:00.748105+00:00
-- url     : https://prove2.me/submissions/92e77ed8-28b5-4818-a777-1cfcfd49b6b3

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
theorem _root_.solution {p q : ℕ}
    (halign : ∀ N, ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n) :
    {n : ℕ | LowDigits p n ∧ LowDigits q n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hN, hpn, hqn⟩ := halign N
  exact ⟨n, ⟨hpn, hqn⟩, hN⟩
end Egrs75.MuFinish
