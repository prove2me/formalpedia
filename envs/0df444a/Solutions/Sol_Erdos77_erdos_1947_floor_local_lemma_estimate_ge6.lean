-- Prove2me | solution 1 for Erdos77.erdos_1947_floor_local_lemma_estimate_ge6
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T13:14:46.75249+00:00
-- url     : https://prove2.me/submissions/908a0900-793c-4bd1-af37-913f5ccec854

import Theorems.Thm_Erdos77_erdos_1947_pair_count_lt_factorial

theorem solution (k : Nat) (hk : 6 <= k) :
    let n : Nat := Nat.floor ((2 : Real) ^ ((k : Real) / 2))
    (4 : Real) * (Nat.choose k 2 : Real) *
      (Nat.choose (n - 2) (k - 2) : Real) *
      (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1 := by
  dsimp only
  let n : Nat := Nat.floor ((2 : Real) ^ ((k : Real) / 2))
  have hn : (n : Real) <= (2 : Real) ^ ((k : Real) / 2) := by
    dsimp [n]
    exact Nat.floor_le (by positivity)
  have hnsub : ((n - 2 : Nat) : Real) <= (n : Real) := by
    exact_mod_cast Nat.sub_le n 2
  have hnsubpow : ((n - 2 : Nat) : Real) <= (2 : Real) ^ ((k : Real) / 2) :=
    hnsub.trans hn
  have hchoose : (Nat.choose (n - 2) (k - 2) : Real) <=
      ((2 : Real) ^ ((k : Real) / 2)) ^ (k - 2) /
        (Nat.factorial (k - 2) : Real) := by
    calc
      (Nat.choose (n - 2) (k - 2) : Real) <=
          ((n - 2 : Nat) : Real) ^ (k - 2) /
            (Nat.factorial (k - 2) : Real) := by
        simpa using (Nat.choose_le_pow_div (k - 2) (n - 2) :
          (Nat.choose (n - 2) (k - 2) : Real) <=
            (((n - 2 : Nat) : Real) ^ (k - 2)) /
              (Nat.factorial (k - 2) : Real))
      _ <= ((2 : Real) ^ ((k : Real) / 2)) ^ (k - 2) /
            (Nat.factorial (k - 2) : Real) := by
        gcongr
  have hchoose2 : (Nat.choose k 2 : Real) =
      (k : Real) * ((k : Real) - 1) / 2 := by
    rw [Nat.choose_two_right]
    rw [Nat.cast_div_charZero (Nat.two_dvd_mul_sub_one k)]
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 <= k)]
    norm_num
  have hpow :
      ((2 : Real) ^ ((k : Real) / 2)) ^ (k - 2) *
          (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) =
        (2 : Real) ^ (1 - (k : Real) / 2) := by
    rw [← Real.rpow_natCast ((2 : Real) ^ ((k : Real) / 2)) (k - 2)]
    rw [← Real.rpow_mul (x := (2 : Real)) (by norm_num : (0 : Real) <= 2)
      ((k : Real) / 2) ((k - 2 : Nat) : Real)]
    rw [← Real.rpow_add (by norm_num : (0 : Real) < 2)]
    rw [hchoose2]
    push_cast
    rw [Nat.cast_sub (by omega : 2 <= k)]
    congr 1
    ring_nf
  have hratio : (Nat.choose k 2 : Real) / (Nat.factorial (k - 2) : Real) < 1 := by
    apply (div_lt_one (by positivity)).2
    exact_mod_cast Erdos77.erdos_1947_pair_count_lt_factorial k hk
  have hkReal : (6 : Real) <= (k : Real) := by exact_mod_cast hk
  have hexp : (3 : Real) - (k : Real) / 2 <= 0 := by
    nlinarith
  have hsmall : (2 : Real) ^ ((3 : Real) - (k : Real) / 2) <= 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hexp
  have hlast :
      (Nat.choose k 2 : Real) / (Nat.factorial (k - 2) : Real) *
        (2 : Real) ^ ((3 : Real) - (k : Real) / 2) < 1 := by
    calc
      _ <= (Nat.choose k 2 : Real) / (Nat.factorial (k - 2) : Real) * 1 :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ < 1 := by simpa using hratio
  calc
    (4 : Real) * (Nat.choose k 2 : Real) *
        (Nat.choose (n - 2) (k - 2) : Real) *
        (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) <=
      4 * (Nat.choose k 2 : Real) *
        (((2 : Real) ^ ((k : Real) / 2)) ^ (k - 2) /
          (Nat.factorial (k - 2) : Real)) *
        (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) := by
      gcongr
    _ = (Nat.choose k 2 : Real) / (Nat.factorial (k - 2) : Real) *
        (2 : Real) ^ ((3 : Real) - (k : Real) / 2) := by
      calc
        _ = ((Nat.choose k 2 : Real) / (Nat.factorial (k - 2) : Real)) *
            (4 * (((2 : Real) ^ ((k : Real) / 2)) ^ (k - 2) *
              (2 : Real) ^ (1 - (Nat.choose k 2 : Real)))) := by ring
        _ = ((Nat.choose k 2 : Real) / (Nat.factorial (k - 2) : Real)) *
            (4 * (2 : Real) ^ (1 - (k : Real) / 2)) := by rw [hpow]
        _ = (Nat.choose k 2 : Real) / (Nat.factorial (k - 2) : Real) *
            (2 : Real) ^ ((3 : Real) - (k : Real) / 2) := by
          have h4 : (4 : Real) = (2 : Real) ^ (2 : Nat) := by norm_num
          rw [h4, ← Real.rpow_natCast (2 : Real) 2]
          rw [← Real.rpow_add (by norm_num : (0 : Real) < 2)]
          congr 1
          ring_nf
    _ < 1 := hlast
