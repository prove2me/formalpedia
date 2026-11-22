-- Prove2me | solution 1 for Egrs75.MuFinish.egrs_clearing_low_mu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:43:55.951597+00:00
-- url     : https://prove2.me/submissions/a8fda0cc-3ff2-470c-9a63-e9f1c031ac3a

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
public import Theorems.Thm_Egrs75_MuFinish_align_finish_mu
public import Theorems.Thm_Egrs75_RepairPaperfaithful_lowDigits_iff_digitAt


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
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) (N : ℕ)
    {n : ℕ} (_hpn : LowDigits p n) (_hNn : N < n) (_hbad : 0 < badCountQ q n)
    (_hlow : q ^ (topBadIndex q n) ≤ N) :
    ∃ n', LowDigits p n' ∧ N < n' ∧ (∀ i, topBadIndex q n ≤ i → ¬ BadAt q i n') := by
  obtain ⟨n', hN', hpn', hqn'⟩ := align_finish_mu hp hq hpo hqo hpq N
  refine ⟨n', hpn', hN', fun idx _ => ?_⟩
  have hq3 : 3 ≤ q := by have h2 := hq.two_le; rcases hqo with ⟨c, hc⟩; omega
  have hd := (lowDigits_iff_digitAt (by omega : 2 ≤ q)).mp hqn' idx
  unfold BadAt
  omega
end Egrs75.MuFinish
