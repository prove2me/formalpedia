-- Prove2me | solution 1 for Egrs75.MathlibAPI.no_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:39.668011+00:00
-- url     : https://prove2.me/submissions/8ead9b7a-6e98-4a32-8a7e-f4bcf500378b

module
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Definitions.Def_LeanPool_Egrs75_LogIrrationality

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.MathlibAPI
open Nat
open Egrs75
namespace Egrs75.MathlibAPI
theorem _root_.solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {n m : ℕ} (hn : 1 ≤ n) : (p : ℝ) ^ n ≠ (q : ℝ) ^ m := by
  intro hreal
  -- Move to ℕ: (p:ℝ)^n = (q:ℝ)^m  ⟹  p^n = q^m.
  have hnat : p ^ n = q ^ m := by
    have : ((p ^ n : ℕ) : ℝ) = ((q ^ m : ℕ) : ℝ) := by push_cast; exact hreal
    exact_mod_cast this
  -- p ∣ p^n = q^m ⟹ p ∣ q ⟹ p = q.
  have hdvd : p ∣ q ^ m := by
    rw [← hnat]; exact dvd_pow_self p (by omega)
  have hpdvdq : p ∣ q := hp.prime.dvd_of_dvd_pow hdvd
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpdvdq)
end Egrs75.MathlibAPI
