-- Prove2me | solution 2 for Erdos77.gnnw_diagonal_exponential_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:33:22.718884+00:00
-- url     : https://prove2.me/submissions/e401be8d-2d1a-4c4c-9f95-ce1f9e8e3882
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Erdos77_gnnw_uniform_ramsey_bound
import Definitions.Def_Erdos77_diagonal_ramsey
import Definitions.Def_Erdos77_asymmetric_ramsey
import Mathlib
open Filter Topology

theorem solution :
    Exists fun err : Nat -> Real =>
      And (err =o[atTop] (fun k : Nat => (k : Real)))
      (forall k : Nat,
        (Erdos77.diagonalRamsey k : Real) <=
          Real.exp ((- (0.14 : Real) / Real.exp 1) * (k : Real) + err k) *
            (Nat.choose (2 * k) k : Real)) := by
  apply Exists.elim Erdos77.gnnw_uniform_ramsey_bound
  intro err hpair
  apply Exists.intro err
  apply And.intro hpair.left
  intro k
  have hbound := hpair.right
  by_cases hk : k = 0
  case pos =>
    subst k
    have hzero : Erdos77.diagonalRamsey 0 = 0 := by
      unfold Erdos77.diagonalRamsey
      apply Nat.sInf_eq_zero.mpr
      left
      simp
    rw [hzero]
    have hc : (Nat.choose (2 * 0) 0 : Real) = 1 := by norm_num
    rw [hc]
    simpa using (Real.exp_pos (err 0)).le
  case neg =>
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have h := hbound k k hkpos hkpos le_rfl
    change (Erdos77.diagonalRamsey k : Real) <=
      Real.exp (((-(1 / 4 : Real) * ((k : Real) / k) +
        (3 / 100 : Real) * ((k : Real) / k) ^ 2 +
        (2 / 25 : Real) * ((k : Real) / k) ^ 3) *
        Real.exp (-((k : Real) / k))) * (k : Real) + err k) *
        (Nat.choose (k + k) k : Real) at h
    have hcoeff :
        ((-(1 / 4 : Real) * ((k : Real) / k) +
          (3 / 100 : Real) * ((k : Real) / k) ^ 2 +
          (2 / 25 : Real) * ((k : Real) / k) ^ 3) *
          Real.exp (-((k : Real) / k))) * (k : Real) =
          (-(0.14 : Real) / Real.exp 1) * (k : Real) := by
      have hkreal : Ne (k : Real) 0 := Nat.cast_ne_zero.mpr hk
      rw [div_self hkreal]
      rw [Real.exp_neg]
      norm_num [div_eq_mul_inv] <;> ring
    rw [hcoeff] at h
    have htwo : k + k = 2 * k := by omega
    rw [htwo] at h
    exact h
