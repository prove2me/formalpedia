-- Prove2me | solution 1 for Egrs75.SmokeProbe.egrs_two_prime_challenge_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:44:31.570547+00:00
-- url     : https://prove2.me/submissions/8717b82f-e1d4-4443-aca0-d7a73f3eb7dd

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
theorem _root_.solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    {n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n}.Infinite :=
  egrs_two_prime_mu hp hq hpo hqo hpq
end Egrs75.SmokeProbe
