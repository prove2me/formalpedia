-- Prove2me | solution 1 for Erdos77.gnnw_diagonal_rate_exact
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:05:58.233634+00:00
-- url     : https://prove2.me/submissions/74741566-176e-470d-9f67-6ab1bbf1299d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Erdos77_gnnw_diagonal_exponential_witness
import Definitions.Def_Erdos77_diagonal_ramsey
import Mathlib
open Filter Topology

theorem solution (eps : Real) (heps : 0 < eps) :
    Filter.Eventually
      (fun k : Nat =>
        (Erdos77.diagonalRamsey k : Real) <=
          (4 * Real.exp (- (0.14 : Real) / Real.exp 1)) ^ ((1 + eps) * (k : Real)))
      Filter.atTop := by
  rcases Erdos77.gnnw_diagonal_exponential_witness with ⟨err, herr, hbound⟩
  let d : Real := (0.14 : Real) / Real.exp 1
  let B : Real := 4 * Real.exp (-d)
  have he : 1 < Real.exp 1 := by
    exact Real.one_lt_exp_iff.mpr (by norm_num)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hdlt : d < 1 / 4 := by
    dsimp [d]
    calc
      (0.14 : Real) / Real.exp 1 < 0.14 := div_lt_self (by norm_num) he
      _ < 1 / 4 := by norm_num
  have hBgt : 1 < B := by
    dsimp [B]
    calc
      (1 : Real) < 4 * (1 - d) := by nlinarith
      _ <= 4 * Real.exp (-d) := by
        have := Real.add_one_le_exp (-d)
        nlinarith
  have hBpos : 0 < B := lt_trans zero_lt_one hBgt
  have hlogB : Real.log B = Real.log 4 - d := by
    dsimp [B, d]
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
    ring
  have hlogBpos : 0 < Real.log B := Real.log_pos hBgt
  let c : Real := eps * Real.log B
  have hc : 0 < c := mul_pos heps hlogBpos
  have herr_eventually : Filter.Eventually (fun k : Nat => err k <= c * (k : Real)) Filter.atTop := by
    filter_upwards [herr.bound hc] with k hk
    calc
      err k <= |err k| := le_abs_self _
      _ = ‖err k‖ := (Real.norm_eq_abs _).symm
      _ <= c * ‖(k : Real)‖ := hk
      _ = c * (k : Real) := by rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  filter_upwards [herr_eventually] with k hk
  have hchoose : (Nat.choose (2 * k) k : Real) <= (4 : Real) ^ k := by
    have hnat : Nat.choose (2 * k) k <= 2 ^ (2 * k) := Nat.choose_le_two_pow _ _
    have hreal : (Nat.choose (2 * k) k : Real) <= (2 : Real) ^ (2 * k) := by
      exact_mod_cast hnat
    calc
      (Nat.choose (2 * k) k : Real) <= (2 : Real) ^ (2 * k) := hreal
      _ = (4 : Real) ^ k := by norm_num [pow_mul]
  have hfour : (4 : Real) ^ k = Real.exp (Real.log 4 * (k : Real)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  have hexp :
      (-d * (k : Real) + err k) + Real.log 4 * (k : Real) <=
        (1 + eps) * (k : Real) * Real.log B := by
    calc
      (-d * (k : Real) + err k) + Real.log 4 * (k : Real) <=
          (-d * (k : Real) + (eps * Real.log B) * (k : Real)) + Real.log 4 * (k : Real) := by
        gcongr
      _ = (1 + eps) * (k : Real) * Real.log B := by rw [hlogB]; ring
  have hdeq : -d * (k : Real) + err k =
      (- (0.14 : Real) / Real.exp 1) * (k : Real) + err k := by
    dsimp [d]
    ring
  have hBaseEq : B = 4 * Real.exp (- (0.14 : Real) / Real.exp 1) := by
    dsimp [B, d]
    congr 1
    rw [← neg_div]
  calc
    (Erdos77.diagonalRamsey k : Real) <=
        Real.exp (-d * (k : Real) + err k) * (Nat.choose (2 * k) k : Real) := by
      rw [hdeq]
      exact hbound k
    _ <= Real.exp (-d * (k : Real) + err k) * (4 : Real) ^ k :=
      mul_le_mul_of_nonneg_left hchoose (Real.exp_pos _).le
    _ = Real.exp ((-d * (k : Real) + err k) + Real.log 4 * (k : Real)) := by
      rw [hfour, ← Real.exp_add]
    _ <= Real.exp ((1 + eps) * (k : Real) * Real.log B) := Real.exp_le_exp.mpr hexp
    _ = B ^ ((1 + eps) * (k : Real)) := by
      rw [Real.rpow_def_of_pos hBpos]
      congr 1
      ring
    _ = (4 * Real.exp (- (0.14 : Real) / Real.exp 1)) ^ ((1 + eps) * (k : Real)) := by
      rw [hBaseEq]
