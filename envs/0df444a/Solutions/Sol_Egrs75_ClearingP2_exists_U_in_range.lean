-- Prove2me | solution 1 for Egrs75.ClearingP2.exists_U_in_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:02.104736+00:00
-- url     : https://prove2.me/submissions/eb0084e5-2921-407a-ae3b-cf11af5584be

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_AddBranch
public import Theorems.Thm_Egrs75_RoundUp_exists_lowDigits_between


set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.ClearingP2
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
namespace Egrs75.ClearingP2
theorem _root_.solution {p q i T m : ℕ} (hp : 3 ≤ p) (hpo : Odd p)
    (hx1 : 1 ≤ q ^ i - T) (hcond3 : 2 * (q ^ i - T) ≤ p ^ m) :
    ∃ U, q ^ i - T ≤ U ∧ U < p ^ m ∧ LowDigits p U := by
  obtain ⟨U, hlo, hhi, hUlow⟩ := RoundUp.exists_lowDigits_between hp hpo (q ^ i - T) hx1
  exact ⟨U, hlo, by omega, hUlow⟩
end Egrs75.ClearingP2
