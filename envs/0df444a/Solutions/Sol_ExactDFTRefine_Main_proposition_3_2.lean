-- Prove2me | solution 1 for ExactDFTRefine.Main.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:19:35.278806+00:00
-- url     : https://prove2.me/submissions/44dda2b5-3c61-42e7-8eb9-dee2608e3c97

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments
import Theorems.Thm_ExactDFTRefine_Main_lemma_3_1
import Theorems.Thm_ExactDFTRefine_Main_appendix_a

open ExactDFTRefine.Main

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private lemma Cpar_nonneg : 0 ≤ Cpar := by norm_num [Cpar]

private lemma SN_le_exp (N : ℕ) (x : ℝ) (hx : 0 ≤ x) : SN N x ≤ Real.exp x := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
  simp only [SN, div_eq_inv_mul, smul_eq_mul, mul_comm]
  apply Summable.sum_le_tsum (Finset.range N)
  · intro n hn
    positivity
  · simpa only [NormedSpace.expSeries_apply_eq, smul_eq_mul, mul_comm] using
      (NormedSpace.expSeries_summable (𝕂 := ℝ) x)

private lemma moment_add (t : ℝ) (A B : Multiset ℕ) :
    moment t (A + B) = moment t A + moment t B := by
  simp [moment, Multiset.map_add]

private lemma moment_replicate (t : ℝ) (n r : ℕ) :
    moment t (Multiset.replicate n r) = n * (r : ℝ) ^ t := by
  simp [moment]

private lemma log_le_of_exp_le' {x y : ℝ} (hx : 0 < x) (h : x ≤ Real.exp y) :
    Real.log x ≤ y := by
  have h' := Real.log_le_log hx h
  simpa using h'

private lemma le_log_of_exp_le' {x y : ℝ} (h : Real.exp y ≤ x) :
    y ≤ Real.log x := by
  have h' := Real.log_le_log (Real.exp_pos y) h
  simpa using h'

private lemma log_upper_cert {r : ℕ} {N : ℕ} {ℓ : ℝ} (hr : 0 < r)
    (hℓ0 : 0 ≤ ℓ) (h : (145 : ℝ) / r ≤ SN N ℓ) : Real.log ((145 : ℝ) / r) ≤ ℓ := by
  apply log_le_of_exp_le' (by positivity)
  exact h.trans (SN_le_exp N ℓ hℓ0)

private lemma log_lower_cert {r : ℕ} {N : ℕ} {ℓ : ℝ} (hr : 0 < r)
    (hN : 1 ≤ N) (hℓ0 : 0 ≤ ℓ / 8) (hℓ1 : ℓ / 8 ≤ 1)
    (h : UN N (ℓ / 8) ^ 8 ≤ (145 : ℝ) / r) : ℓ ≤ Real.log ((145 : ℝ) / r) := by
  apply le_log_of_exp_le'
  calc
    Real.exp ℓ = (Real.exp (ℓ / 8)) ^ 8 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ UN N (ℓ / 8) ^ 8 := by
      exact pow_le_pow_left₀ (Real.exp_pos _).le (appendix_a N hN (ℓ / 8) hℓ0 hℓ1).2 8
    _ ≤ (145 : ℝ) / r := h

private lemma normalized_rank (r : ℕ) (hr : 0 < r) :
    ((r : ℝ) / 145) ^ tpar =
      ((r : ℝ) / 145) * Real.exp (Cpar * Real.log ((145 : ℝ) / r)) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hq : 0 < (r : ℝ) / 145 := by positivity
  have hinv : (145 : ℝ) / r = (((r : ℝ) / 145))⁻¹ := by field_simp
  rw [tpar, Real.rpow_def_of_pos hq, hinv, Real.log_inv]
  calc
    Real.exp (Real.log ((r : ℝ) / 145) * (1 - Cpar)) =
        Real.exp (Real.log ((r : ℝ) / 145)) *
          Real.exp (Cpar * -Real.log ((r : ℝ) / 145)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = ((r : ℝ) / 145) *
          Real.exp (Cpar * -Real.log ((r : ℝ) / 145)) := by rw [Real.exp_log hq]

private lemma charged_row (m r N : ℕ) (ℓ br : ℝ) (hr : 0 < r)
    (hℓ0 : 0 ≤ ℓ) (hlog : (145 : ℝ) / r ≤ SN N ℓ)
    (hx0 : 0 ≤ Cpar * ℓ) (hx1 : Cpar * ℓ ≤ 1)
    (hb : (m : ℝ) * (((r : ℝ) / 145) * UN 6 (Cpar * ℓ)) ≤ br) :
    (m : ℝ) * (((r : ℝ) / 145) ^ tpar) ≤ br := by
  rw [normalized_rank r hr]
  calc
    (m : ℝ) * (((r : ℝ) / 145) * Real.exp (Cpar * Real.log ((145 : ℝ) / r))) ≤
        (m : ℝ) * (((r : ℝ) / 145) * Real.exp (Cpar * ℓ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (log_upper_cert hr hℓ0 hlog) Cpar_nonneg))
        (by positivity)) (by positivity)
    _ ≤ (m : ℝ) * (((r : ℝ) / 145) * UN 6 (Cpar * ℓ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (appendix_a 6 (by norm_num) _ hx0 hx1).2 (by positivity)) (by positivity)
    _ ≤ br := hb

private lemma target_row (m r N : ℕ) (ℓ br : ℝ) (hr : 0 < r) (hN : 1 ≤ N)
    (hℓ0 : 0 ≤ ℓ / 8) (hℓ1 : ℓ / 8 ≤ 1)
    (hlog : UN N (ℓ / 8) ^ 8 ≤ (145 : ℝ) / r)
    (hx0 : 0 ≤ Cpar * ℓ)
    (hb : br ≤ (m : ℝ) * (((r : ℝ) / 145) * SN 6 (Cpar * ℓ))) :
    br ≤ (m : ℝ) * (((r : ℝ) / 145) ^ tpar) := by
  rw [normalized_rank r hr]
  calc
    br ≤ (m : ℝ) * (((r : ℝ) / 145) * SN 6 (Cpar * ℓ)) := hb
    _ ≤ (m : ℝ) * (((r : ℝ) / 145) * Real.exp (Cpar * ℓ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (lemma_3_1.1 _ hx0) (by positivity)) (by positivity)
    _ ≤ (m : ℝ) * (((r : ℝ) / 145) * Real.exp (Cpar * Real.log ((145 : ℝ) / r))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (log_lower_cert hr hN hℓ0 hℓ1 hlog) Cpar_nonneg))
        (by positivity)) (by positivity)

private lemma blocksP_expansion :
    moment tpar blocksP / (145 : ℝ) ^ tpar =
      41946 * (((1 : ℝ) / 145) ^ tpar) +
      6984 * (((2 : ℝ) / 145) ^ tpar) +
      8892 * (((3 : ℝ) / 145) ^ tpar) +
      2646 * (((4 : ℝ) / 145) ^ tpar) +
      648 * (((5 : ℝ) / 145) ^ tpar) +
      144 * (((8 : ℝ) / 145) ^ tpar) +
      448 * (((16 : ℝ) / 145) ^ tpar) +
      448 * (((24 : ℝ) / 145) ^ tpar) +
      448 * (((32 : ℝ) / 145) ^ tpar) +
      448 * (((40 : ℝ) / 145) ^ tpar) +
      448 * (((48 : ℝ) / 145) ^ tpar) +
      448 * (((56 : ℝ) / 145) ^ tpar) +
      448 * (((64 : ℝ) / 145) ^ tpar) +
      224 * (((72 : ℝ) / 145) ^ tpar) := by
  simp only [blocksP, moment_add, moment_replicate, Nat.cast_ofNat, Nat.cast_one]
  rw [add_div, add_div, add_div, add_div, add_div, add_div, add_div,
    add_div, add_div, add_div, add_div, add_div, add_div]
  rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 5) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 8) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 16) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 24) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 32) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 40) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 48) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 56) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 64) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 72) (by norm_num : (0 : ℝ) ≤ 145)]
  ring

private lemma targetsT_expansion :
    moment tpar targetsT / (145 : ℝ) ^ tpar =
      504 * (((4 : ℝ) / 145) ^ tpar) +
      126 * (((7 : ℝ) / 145) ^ tpar) +
      846 * (((8 : ℝ) / 145) ^ tpar) +
      5868 * (((9 : ℝ) / 145) ^ tpar) +
      448 * (((17 : ℝ) / 145) ^ tpar) +
      448 * (((25 : ℝ) / 145) ^ tpar) +
      448 * (((33 : ℝ) / 145) ^ tpar) +
      448 * (((41 : ℝ) / 145) ^ tpar) +
      448 * (((49 : ℝ) / 145) ^ tpar) +
      448 * (((57 : ℝ) / 145) ^ tpar) +
      448 * (((65 : ℝ) / 145) ^ tpar) +
      224 * (((73 : ℝ) / 145) ^ tpar) +
      224 * (((145 : ℝ) / 145) ^ tpar) := by
  simp only [targetsT, moment_add, moment_replicate, Nat.cast_ofNat, Nat.cast_one]
  rw [add_div, add_div, add_div, add_div, add_div, add_div, add_div,
    add_div, add_div, add_div, add_div, add_div]
  rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 7) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 8) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 9) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 17) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 25) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 33) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 41) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 49) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 57) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 65) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 73) (by norm_num : (0 : ℝ) ≤ 145),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 145) (by norm_num : (0 : ℝ) ≤ 145)]
  ring

theorem solution :
    moment tpar blocksP / (145 : ℝ) ^ tpar ≤ Ubound ∧
    moment tpar targetsT / (145 : ℝ) ^ tpar ≥ Lbound ∧
    moment tpar blocksP / moment tpar targetsT ≤ 1 - eps := by
  have hp1 : (41946 : ℝ) * (((1 : ℝ) / 145) ^ tpar) ≤ 293663682394904 / 10 ^ 12 := by
    convert charged_row (m := 41946) (r := 1) (N := 29)
      (ℓ := 4976733742421 / 10 ^ 12) (br := 293663682394904 / 10 ^ 12) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have hp2 : (6984 : ℝ) * (((2 : ℝ) / 145) ^ tpar) ≤ 97585379104181 / 10 ^ 12 := by
    convert charged_row (m := 6984) (r := 2) (N := 27)
      (ℓ := 4283586561861 / 10 ^ 12) (br := 97585379104181 / 10 ^ 12) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have hp3 : (8892 : ℝ) * (((3 : ℝ) / 145) ^ tpar) ≤ 186139872110444 / 10 ^ 12 := by
    convert charged_row (m := 8892) (r := 3) (N := 26)
      (ℓ := 3878121453753 / 10 ^ 12) (br := 186139872110444 / 10 ^ 12) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have hp4 : (2646 : ℝ) * (((4 : ℝ) / 145) ^ tpar) ≤ 73788927475228 / 10 ^ 12 := by
    convert charged_row (m := 2646) (r := 4) (N := 25)
      (ℓ := 3590439381301 / 10 ^ 12) (br := 73788927475228 / 10 ^ 12) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have hp5 : (648 : ℝ) * (((5 : ℝ) / 145) ^ tpar) ≤ 22573229270017 / 10 ^ 12 := by
    convert charged_row (m := 648) (r := 5) (N := 24)
      (ℓ := 3367295829987 / 10 ^ 12) (br := 22573229270017 / 10 ^ 12) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have hp8 : (144 : ℝ) * (((8 : ℝ) / 145) ^ tpar) ≤ 8014652284989 / 10 ^ 12 := by
    convert charged_row (m := 144) (r := 8) (N := 23)
      (ℓ := 2897292200741 / 10 ^ 12) (br := 8014652284989 / 10 ^ 12) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have hp16 : (448 : ℝ) * (((16 : ℝ) / 145) ^ tpar) ≤ 49764660119895 / 10 ^ 12 := by
    convert charged_row (m := 448) (r := 16) (N := 21)
      (ℓ := 2204145020181 / 10 ^ 12) (br := 49764660119895 / 10 ^ 12) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have hp24 : (448 : ℝ) * (((24 : ℝ) / 145) ^ tpar) ≤ 74555635518839 / 10 ^ 12 := by
    convert charged_row (m := 448) (r := 24) (N := 19)
      (ℓ := 1798679912073 / 10 ^ 12) (br := 74555635518839 / 10 ^ 12) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have hp32 : (448 : ℝ) * (((32 : ℝ) / 145) ^ tpar) ≤ 99321181555482 / 10 ^ 12 := by
    convert charged_row (m := 448) (r := 32) (N := 18)
      (ℓ := 1510997839621 / 10 ^ 12) (br := 99321181555482 / 10 ^ 12) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have hp40 : (448 : ℝ) * (((40 : ℝ) / 145) ^ tpar) ≤ 124067835657887 / 10 ^ 12 := by
    convert charged_row (m := 448) (r := 40) (N := 17)
      (ℓ := 1287854288307 / 10 ^ 12) (br := 124067835657887 / 10 ^ 12) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have hp48 : (448 : ℝ) * (((48 : ℝ) / 145) ^ tpar) ≤ 148799445098402 / 10 ^ 12 := by
    convert charged_row (m := 448) (r := 48) (N := 16)
      (ℓ := 1105532731513 / 10 ^ 12) (br := 148799445098402 / 10 ^ 12) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have hp56 : (448 : ℝ) * (((56 : ℝ) / 145) ^ tpar) ≤ 173518550400695 / 10 ^ 12 := by
    convert charged_row (m := 448) (r := 56) (N := 15)
      (ℓ := 951382051686 / 10 ^ 12) (br := 173518550400695 / 10 ^ 12) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have hp64 : (448 : ℝ) * (((64 : ℝ) / 145) ^ tpar) ≤ 198226956274002 / 10 ^ 12 := by
    convert charged_row (m := 448) (r := 64) (N := 15)
      (ℓ := 817850659061 / 10 ^ 12) (br := 198226956274002 / 10 ^ 12) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have hp72 : (224 : ℝ) * (((72 : ℝ) / 145) ^ tpar) ≤ 111463005749806 / 10 ^ 12 := by
    convert charged_row (m := 224) (r := 72) (N := 14)
      (ℓ := 700067623405 / 10 ^ 12) (br := 111463005749806 / 10 ^ 12) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have hP : moment tpar blocksP / (145 : ℝ) ^ tpar ≤ Ubound := by
    rw [blocksP_expansion]
    unfold Ubound
    linarith

  have ht4 : (14055033804805 / 10 ^ 12 : ℝ) ≤ (504 : ℝ) * (((4 : ℝ) / 145) ^ tpar) := by
    convert target_row (m := 504) (r := 4) (N := 12)
      (ℓ := 3590439381300 / 10 ^ 12) (br := 14055033804805 / 10 ^ 12)
      (by norm_num) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have ht7 : (6138693311557 / 10 ^ 12 : ℝ) ≤ (126 : ℝ) * (((7 : ℝ) / 145) ^ tpar) := by
    convert target_row (m := 126) (r := 7) (N := 11)
      (ℓ := 3030823593365 / 10 ^ 12) (br := 6138693311557 / 10 ^ 12)
      (by norm_num) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have ht8 : (47086082174304 / 10 ^ 12 : ℝ) ≤ (846 : ℝ) * (((8 : ℝ) / 145) ^ tpar) := by
    convert target_row (m := 846) (r := 8) (N := 11)
      (ℓ := 2897292200740 / 10 ^ 12) (br := 47086082174304 / 10 ^ 12)
      (by norm_num) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have ht9 : (367291038096216 / 10 ^ 12 : ℝ) ≤ (5868 : ℝ) * (((9 : ℝ) / 145) ^ tpar) := by
    convert target_row (m := 5868) (r := 9) (N := 11)
      (ℓ := 2779509165084 / 10 ^ 12) (br := 367291038096216 / 10 ^ 12)
      (by norm_num) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have ht17 : (52865271049404 / 10 ^ 12 : ℝ) ≤ (448 : ℝ) * (((17 : ℝ) / 145) ^ tpar) := by
    convert target_row (m := 448) (r := 17) (N := 10)
      (ℓ := 2143520398364 / 10 ^ 12) (br := 52865271049404 / 10 ^ 12)
      (by norm_num) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have ht25 : (77652546021820 / 10 ^ 12 : ℝ) ≤ (448 : ℝ) * (((25 : ℝ) / 145) ^ tpar) := by
    convert target_row (m := 448) (r := 25) (N := 10)
      (ℓ := 1757857917552 / 10 ^ 12) (br := 77652546021820 / 10 ^ 12)
      (by norm_num) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have ht33 : (102415450004130 / 10 ^ 12 : ℝ) ≤ (448 : ℝ) * (((33 : ℝ) / 145) ^ tpar) := by
    convert target_row (m := 448) (r := 33) (N := 10)
      (ℓ := 1480226180954 / 10 ^ 12) (br := 102415450004130 / 10 ^ 12)
      (by norm_num) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have ht41 : (127160048134959 / 10 ^ 12 : ℝ) ≤ (448 : ℝ) * (((41 : ℝ) / 145) ^ tpar) := by
    convert target_row (m := 448) (r := 41) (N := 9)
      (ℓ := 1263161675716 / 10 ^ 12) (br := 127160048134959 / 10 ^ 12)
      (by norm_num) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have ht49 : (151889974497414 / 10 ^ 12 : ℝ) ≤ (448 : ℝ) * (((49 : ℝ) / 145) ^ tpar) := by
    convert target_row (m := 448) (r := 49) (N := 9)
      (ℓ := 1084913444309 / 10 ^ 12) (br := 151889974497414 / 10 ^ 12)
      (by norm_num) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have ht57 : (176607655012455 / 10 ^ 12 : ℝ) ≤ (448 : ℝ) * (((57 : ℝ) / 145) ^ tpar) := by
    convert target_row (m := 448) (r := 57) (N := 9)
      (ℓ := 933682474586 / 10 ^ 12) (br := 176607655012455 / 10 ^ 12)
      (by norm_num) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have ht65 : (201314825634830 / 10 ^ 12 : ℝ) ≤ (448 : ℝ) * (((65 : ℝ) / 145) ^ tpar) := by
    convert target_row (m := 448) (r := 65) (N := 8)
      (ℓ := 802346472524 / 10 ^ 12) (br := 201314825634830 / 10 ^ 12)
      (by norm_num) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have ht73 : (113006395319643 / 10 ^ 12 : ℝ) ≤ (224 : ℝ) * (((73 : ℝ) / 145) ^ tpar) := by
    convert target_row (m := 224) (r := 73) (N := 8)
      (ℓ := 686274301272 / 10 ^ 12) (br := 113006395319643 / 10 ^ 12)
      (by norm_num) (by norm_num) using 1
    all_goals norm_num [SN, UN, Finset.sum_range_succ, Cpar]
  have ht145 : (224 : ℝ) * (((145 : ℝ) / 145) ^ tpar) = 224 := by norm_num
  have hT : moment tpar targetsT / (145 : ℝ) ^ tpar ≥ Lbound := by
    rw [targetsT_expansion]
    unfold Lbound
    linarith

  refine ⟨hP, hT, ?_⟩
  have hd : 0 < (145 : ℝ) ^ tpar := Real.rpow_pos_of_pos (by norm_num) _
  have hL : 0 < Lbound := by norm_num [Lbound]
  have hTpos : 0 < moment tpar targetsT := by
    have hq : 0 < moment tpar targetsT / (145 : ℝ) ^ tpar := hL.trans_le hT
    exact (div_pos_iff_of_pos_right hd).mp hq
  have hP' : moment tpar blocksP ≤ Ubound * (145 : ℝ) ^ tpar := (div_le_iff₀ hd).mp hP
  have hT' : Lbound * (145 : ℝ) ^ tpar ≤ moment tpar targetsT := (le_div_iff₀ hd).mp hT
  apply (div_le_iff₀ hTpos).2
  have hUL : Ubound ≤ (1 - eps) * Lbound := by norm_num [Ubound, Lbound, eps]
  calc
    moment tpar blocksP ≤ Ubound * (145 : ℝ) ^ tpar := hP'
    _ ≤ ((1 - eps) * Lbound) * (145 : ℝ) ^ tpar :=
      mul_le_mul_of_nonneg_right hUL hd.le
    _ = (1 - eps) * (Lbound * (145 : ℝ) ^ tpar) := by ring
    _ ≤ (1 - eps) * moment tpar targetsT := by
      apply mul_le_mul_of_nonneg_left hT'
      norm_num [eps]
