-- Prove2me | solution 1 for Egrs75.SmokeProbe.egrs_3_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:44:30.038087+00:00
-- url     : https://prove2.me/submissions/57440fa2-5508-4d10-a1e3-6db5685faec4

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
theorem _root_.solution : {n : ℕ | ¬ 3 ∣ Nat.centralBinom n ∧ ¬ 5 ∣ Nat.centralBinom n}.Infinite :=
  egrs_two_prime_mu (by norm_num) (by norm_num) ⟨1, rfl⟩ ⟨2, rfl⟩ (by norm_num)
end Egrs75.SmokeProbe
