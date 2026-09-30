-- Prove2me | solution 1 for ComplementFreeCA.XOSRounding.eq1_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:59:22.908711+00:00
-- url     : https://prove2.me/submissions/45a8cb11-691f-4305-8ac3-bf19574dfaec

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic
open Finset

private theorem amgm_pow (d : ℕ) (hd : 0 < d) (Z : Fin d → ℝ) (hZ : ∀ i, 0 ≤ Z i) :
    ∏ i, Z i ≤ ((∑ i, Z i)/(d:ℝ)) ^ d := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have h := Real.geom_mean_le_arith_mean univ (fun _ : Fin d => (1:ℝ)) Z
    (by intro i hi; norm_num) (by simpa using hdR) (fun i hi => hZ i)
  simp only [Real.rpow_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, one_mul] at h
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg (prod_nonneg (fun i hi => hZ i)) _) h (show (0:ℝ) ≤ d by positivity)
  rw [← Real.rpow_mul (prod_nonneg (fun i hi => hZ i)), inv_mul_cancel₀ (ne_of_gt hdR),
    Real.rpow_one, Real.rpow_natCast] at hp
  exact hp

private theorem failure_mono_step (a : ℕ) (ha : 1 ≤ a) :
    (1-1/(a:ℝ))^a ≤ (1-1/((a+1:ℕ):ℝ))^(a+1) := by
  have haR : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hap : (0:ℝ) < a := by linarith
  have hbase : 0 ≤ 1-1/(a:ℝ) := by rw [sub_nonneg, div_le_one hap]; exact haR
  let Z : Fin (a+1) → ℝ := fun i => if i = Fin.last a then 1 else 1-1/(a:ℝ)
  have hz : ∀ i, 0 ≤ Z i := by intro i; dsimp [Z]; split_ifs <;> positivity
  have h := amgm_pow (a+1) (by omega) Z hz
  have hp : ∏ i, Z i = (1-1/(a:ℝ))^a := by simp [Z, Fin.prod_univ_castSucc]
  have hs : (∑ i, Z i) / ((a+1:ℕ):ℝ) = 1-1/((a+1:ℕ):ℝ) := by
    simp [Z, Fin.sum_univ_castSucc]
    field_simp
    ring
  rwa [hp,hs] at h

theorem solution (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (X : Fin k → ℝ)
    (hX0 : ∀ i, 0 ≤ X i) (hX1 : ∀ i, X i ≤ 1) (hsum : ∑ i, X i ≤ 1) :
    1 - (1 - (∑ i, X i) / (k : ℝ)) ^ k ≤ 1 - ∏ i, (1 - X i) ∧
    (1 - (1 - 1 / (k : ℝ)) ^ k) * ∑ i, X i ≤ 1 - (1 - (∑ i, X i) / (k : ℝ)) ^ k ∧
    (1 - (1 - 1 / (n : ℝ)) ^ n) * ∑ i, X i ≤ (1 - (1 - 1 / (k : ℝ)) ^ k) * ∑ i, X i := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0:ℝ) < k := by linarith
  have hS : (0:ℝ) ≤ ∑ i, X i := sum_nonneg (fun i hi => hX0 i)
  refine ⟨?_, ?_, ?_⟩
  · have h := amgm_pow k (by omega) (fun i => 1-X i) (fun i => sub_nonneg.mpr (hX1 i))
    have he : (∑ i, (1-X i))/(k:ℝ) = 1-(∑ i, X i)/(k:ℝ) := by
      rw [sum_sub_distrib]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [sub_div, div_self (ne_of_gt hkp)]
    rw [he] at h
    linarith
  · have hbase : 0 ≤ 1-1/(k:ℝ) := by rw [sub_nonneg, div_le_one hkp]; exact hkR
    have h := (convexOn_pow (𝕜 := ℝ) k).2 (show 1-1/(k:ℝ) ∈ Set.Ici 0 from hbase)
      (show (1:ℝ) ∈ Set.Ici 0 by norm_num) hS (sub_nonneg.mpr hsum) (by ring : (∑ i, X i)+(1-∑ i,X i)=1)
    simp only [smul_eq_mul, one_pow, mul_one] at h
    have he : (∑ i, X i)*(1-1/(k:ℝ))+(1-∑ i,X i) = 1-(∑ i,X i)/(k:ℝ) := by ring
    rw [he] at h
    nlinarith
  · have hm : (1-1/(k:ℝ))^k ≤ (1-1/(n:ℝ))^n := by
      induction n, hkn using Nat.le_induction with
      | base => exact le_rfl
      | succ t hkt ih => exact ih.trans (failure_mono_step t (hk.trans hkt))
    exact mul_le_mul_of_nonneg_right (by linarith) hS
