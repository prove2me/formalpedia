-- Prove2me | solution 3 for Erdos77.uniform_binomial_entropy_log_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T16:32:58.0797+00:00
-- url     : https://prove2.me/submissions/54cfff7a-6bf9-47e0-bcaa-3d36346d0c9e

import Mathlib
import Theorems.Thm_Erdos77_binomial_entropy_log_bound_general
import Definitions.Def_Erdos77_asymmetric_ramsey
open Filter Topology

theorem solution :
  forall k ell : Nat, 0 < k -> 0 < ell -> ell <= k ->
    Real.exp ((((1 + ((ell : Real) / k)) * Real.log (1 + ((ell : Real) / k)) -
      ((ell : Real) / k) * Real.log ((ell : Real) / k)) * (k : Real)) -
      Real.log (2 * (k : Real) + 1)) <= (Nat.choose (k + ell) ell : Real) := by
  intro k ell hk hell hle
  have hlt : ell < k + ell := by omega
  have hchild := Erdos77.binomial_entropy_log_bound_general (k + ell) ell hell hlt
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hellR : (0 : Real) < (ell : Real) := by exact_mod_cast hell
  have hsumR : (0 : Real) < ((k + ell : Nat) : Real) := by exact_mod_cast (show 0 < k + ell by omega)
  have hratio : 1 + (ell : Real) / (k : Real) = ((k + ell : Nat) : Real) / (k : Real) := by
    push_cast
    field_simp [hkR.ne']
    <;> ring
  have hident :
      ((1 + (ell : Real) / (k : Real)) * Real.log (1 + (ell : Real) / (k : Real)) -
        (ell : Real) / (k : Real) * Real.log ((ell : Real) / (k : Real))) * (k : Real) =
        ((k + ell : Nat) : Real) * Real.log ((k + ell : Nat) : Real) -
          (k : Real) * Real.log (k : Real) - (ell : Real) * Real.log (ell : Real) := by
    rw [hratio, Real.log_div hsumR.ne' hkR.ne', Real.log_div hellR.ne' hkR.ne']
    push_cast
    field_simp [hkR.ne']
    <;> ring
  have hsub : k + ell - ell = k := Nat.add_sub_cancel_right k ell
  rw [hsub] at hchild
  have hdenNat : k + ell + 1 <= 2 * k + 1 := by omega
  have hden : ((k + ell + 1 : Nat) : Real) <= 2 * (k : Real) + 1 := by
    exact_mod_cast hdenNat
  have hdenPos : (0 : Real) < ((k + ell + 1 : Nat) : Real) := by positivity
  have hdenRhsPos : (0 : Real) < 2 * (k : Real) + 1 := by positivity
  have hlogden := Real.log_le_log hdenPos hden
  calc
    Real.exp ((((1 + (ell : Real) / (k : Real)) * Real.log (1 + (ell : Real) / (k : Real)) -
        (ell : Real) / (k : Real) * Real.log ((ell : Real) / (k : Real))) * (k : Real)) -
        Real.log (2 * (k : Real) + 1))
      <= Real.exp (((k + ell : Nat) : Real) * Real.log ((k + ell : Nat) : Real) -
          (k : Real) * Real.log (k : Real) - (ell : Real) * Real.log (ell : Real) -
          Real.log ((k + ell + 1 : Nat) : Real)) := by
        apply Real.exp_le_exp.mpr
        rw [hident]
        exact sub_le_sub_left hlogden _
    _ <= (Nat.choose (k + ell) ell : Real) := by
      convert hchild using 1 <;> congr 1 <;> ring
