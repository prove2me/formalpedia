-- Prove2me | solution 1 for Erdos77.erdos_1947_floor_vertex_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:24:42.467994+00:00
-- url     : https://prove2.me/submissions/f1f4e188-5a56-4ef0-b79e-c0449c6f9c3b

import Mathlib

private theorem square_le_pow_two (k : Nat) (hk : 4 ≤ k) :
    (k : Real) ^ 2 ≤ (2 : Real) ^ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk4 : k = 4
    · subst k
      norm_num
    · have hk5 : 5 ≤ k := by omega
      have hprevbound : 4 ≤ k - 1 := by omega
      have hprev := ih (k - 1) (by omega) hprevbound
      have hprevreal : ((k - 1 : Nat) : Real) = (k : Real) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ k)]
        norm_num
      have hk5real : (5 : Real) ≤ (k : Real) := by exact_mod_cast hk5
      have hstep : (k : Real) ^ 2 ≤ 2 * ((k : Real) - 1) ^ 2 := by
        nlinarith [sq_nonneg ((k : Real) - 2)]
      have hp := mul_le_mul_of_nonneg_left hprev (by norm_num : (0 : Real) ≤ 2)
      rw [hprevreal] at hp
      have hexp : (2 : Real) ^ (k - 1) * 2 = (2 : Real) ^ k := by
        rw [← pow_succ]
        congr 1
        omega
      calc
        (k : Real) ^ 2 ≤ 2 * ((k : Real) - 1) ^ 2 := hstep
        _ ≤ 2 * (2 : Real) ^ (k - 1) := hp
        _ = (2 : Real) ^ k := by simpa [mul_comm] using hexp

theorem solution (k : Nat) (hk : 4 ≤ k) :
    let n : Nat := Nat.floor ((2 : Real) ^ ((k : Real) / 2))
    k ≤ n := by
  dsimp
  apply Nat.le_floor
  have hpow := square_le_pow_two k hk
  have hrpow : ((2 : Real) ^ ((k : Real) / 2)) ^ 2 = (2 : Real) ^ k := by
    calc
      ((2 : Real) ^ ((k : Real) / 2)) ^ 2 = (2 : Real) ^ (((k : Real) / 2) * 2) := by
        rw [← Real.rpow_natCast ((2 : Real) ^ ((k : Real) / 2)) 2]
        symm
        exact Real.rpow_mul (x := (2 : Real)) (by norm_num) ((k : Real) / 2) 2
      _ = (2 : Real) ^ (k : Real) := by congr 1; ring
      _ = (2 : Real) ^ k := Real.rpow_natCast _ _
  have hx : 0 ≤ (2 : Real) ^ ((k : Real) / 2) :=
    Real.rpow_nonneg (x := (2 : Real)) (by norm_num) ((k : Real) / 2)
  have hk0 : 0 ≤ (k : Real) := by positivity
  have hsquare : (k : Real) ^ 2 ≤ ((2 : Real) ^ ((k : Real) / 2)) ^ 2 := by
    rw [hrpow]
    exact hpow
  exact (sq_le_sq₀ (a := (k : Real)) (b := (2 : Real) ^ ((k : Real) / 2)) hk0 hx).mp hsquare
