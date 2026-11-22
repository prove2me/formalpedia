-- Prove2me | solution 1 for Egrs75.Finish.align_finish
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:52.452283+00:00
-- url     : https://prove2.me/submissions/449dbbe8-2683-4500-bd32-d626da95f870

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_Egrs75_ClearingHigh
public import Definitions.Def_LeanPool_Egrs75_MuFinish
public import Definitions.Def_LeanPool_Egrs75_Reduction
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Totient
public import Definitions.Def_LeanPool_Egrs75_BadPrefixRoute
public import Theorems.Thm_Egrs75_Finish_align_lex
public import Theorems.Thm_Egrs75_Finish_repair_step_lex
public import Theorems.Thm_Egrs75_LeafInduction_seed_lowDigits_pow
public import Theorems.Thm_Egrs75_LeafInduction_seed_lt_pow_succ


set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.Finish
open Nat
open Finset
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
open Egrs75.Probe
namespace Egrs75.Finish
theorem _root_.solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    ∀ N, ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n := by
  intro N
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le; rcases hpo with ⟨k, hk⟩; omega
  -- The lex induction consumes `repair_step_lex` (with the running magnitude floor `N`,
  -- threaded by `align_lex` as `hNm`).
  refine align_lex N
    (fun {m} hpm hNm hbad => repair_step_lex hp hq hpo hqo hpq N hpm hNm hbad)
    (p ^ (N + 1)) (seed_lt_pow_succ (by omega) N) (seed_lowDigits_pow hp3 (N + 1))
end Egrs75.Finish
