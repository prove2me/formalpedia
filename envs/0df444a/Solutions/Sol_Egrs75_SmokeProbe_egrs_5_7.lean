-- Prove2me | solution 1 for Egrs75.SmokeProbe.egrs_5_7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:44:31.070614+00:00
-- url     : https://prove2.me/submissions/9f858781-b315-4310-8e64-d3ea1bf385e3

module
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Prime.Defs
public import Definitions.Def_LeanPool_Egrs75_MuFinish
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_LeanPool_Egrs75_Instances
public import Theorems.Thm_Egrs75_MuFinish_egrs_two_prime_mu


set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.SmokeProbe
open Egrs75.MuFinish
namespace Egrs75.SmokeProbe
theorem _root_.solution : {n : ℕ | ¬ 5 ∣ Nat.centralBinom n ∧ ¬ 7 ∣ Nat.centralBinom n}.Infinite :=
  egrs_two_prime_mu (by norm_num) (by norm_num) ⟨2, rfl⟩ ⟨3, rfl⟩ (by norm_num)
end Egrs75.SmokeProbe
