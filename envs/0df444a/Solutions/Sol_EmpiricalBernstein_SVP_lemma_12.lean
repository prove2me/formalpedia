-- Prove2me | solution 1 for EmpiricalBernstein.SVP.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:18:30.066603+00:00
-- url     : https://prove2.me/submissions/7e807baa-a60d-40b8-beca-70be6d2a4a98

import Mathlib
import Definitions.Def_EmpiricalBernstein_SVP_PhiPsi

set_option autoImplicit false
open scoped BigOperators
open EmpiricalBernstein.SVP VarianceRegularization.Expansion

private noncomputable def pairs {n : ℕ} (x : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n × Fin n) := WithLp.toLp 2 (fun ij => x ij.1 - x ij.2)

private lemma pairs_sq {n : ℕ} (x : Fin n → ℝ) :
    ‖pairs x‖ ^ 2 = ∑ i, ∑ j, (x i - x j) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  rfl

private lemma pair_identity {n : ℕ} (x : Fin n → ℝ) :
    (∑ i, ∑ j, (x i - x j) ^ 2) =
      2 * n * (∑ i, (x i) ^ 2) - 2 * (∑ i, x i) ^ 2 := by
  simp_rw [show ∀ i j : Fin n, (x i - x j)^2 = (x i)^2 + (x j)^2 - 2*x i*x j by intros; ring]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring_nf
  simp_rw [← Finset.sum_mul]
  ring

private lemma pairs_bound {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    ‖pairs x‖ ≤ 2 * Real.sqrt ((n : ℝ) * (n - 1)) * ‖x‖ := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : 0 ≤ (n : ℝ) - 1 := by linarith
  have hn2 : 0 ≤ (n : ℝ) - 2 := by linarith
  have hs : (∑ i, (x i)^2) ≤ n * ‖x‖ ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin n, ‖x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
        nlinarith [sq_abs (x i), abs_nonneg (x i), norm_nonneg x]
      _ = _ := by simp
  have hp := pairs_sq x
  rw [pair_identity] at hp
  have hr := Real.sq_sqrt (show 0 ≤ (n : ℝ) * (n - 1) by positivity)
  have hb : ‖pairs x‖ ^ 2 ≤ (2 * Real.sqrt ((n : ℝ) * (n - 1)) * ‖x‖)^2 := by
    nlinarith [sq_nonneg (∑ i, x i), mul_nonneg (sq_nonneg ‖x‖) (show 0 ≤ (n : ℝ) * (n - 2) by positivity)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hb

private lemma std_eq {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    Real.sqrt (2 * sampleVar x) = ‖pairs x‖ / Real.sqrt ((n : ℝ) * (n - 1)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hden : 0 < (n : ℝ) * (n - 1) := by positivity
  have hs : 0 ≤ sampleVar x := by unfold sampleVar; positivity
  have he : 2 * sampleVar x * ((n : ℝ) * (n - 1)) = ‖pairs x‖ ^ 2 := by
    rw [pairs_sq]
    unfold sampleVar
    simp_rw [← Finset.sum_div]
    field_simp [hden.ne']
    <;> ring
  apply (eq_div_iff (ne_of_gt (Real.sqrt_pos.2 hden))).2
  have h1 := Real.sq_sqrt (show 0 ≤ 2 * sampleVar x by positivity)
  have h2 := Real.sq_sqrt hden.le
  have h3 : (Real.sqrt (2 * sampleVar x) * Real.sqrt ((n : ℝ) * (n - 1)))^2 = ‖pairs x‖ ^ 2 := by
    rw [mul_pow, h1, h2]; exact he
  exact (sq_eq_sq₀ (by positivity) (norm_nonneg _)).mp h3

private lemma std_lipschitz {n : ℕ} (hn : 2 ≤ n) (x y : Fin n → ℝ) :
    Real.sqrt (2 * sampleVar x) - Real.sqrt (2 * sampleVar y) ≤ 2 * ‖x - y‖ := by
  rw [std_eq hn, std_eq hn, ← sub_div]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  rw [div_le_iff₀ (Real.sqrt_pos.2 (show 0 < (n : ℝ) * (n - 1) by positivity))]
  have he : pairs x - pairs y = pairs (x - y) := by
    ext ij
    simp [pairs]
    ring
  have h := norm_sub_norm_le (pairs x) (pairs y)
  rw [he] at h
  have h := h.trans (pairs_bound hn (x-y))
  nlinarith

private lemma mean_lipschitz {n : ℕ} (hn : 2 ≤ n) (x y : Fin n → ℝ) :
    empMean x - empMean y ≤ ‖x-y‖ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold empMean
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have hs : (∑ i, (x i-y i)) ≤ n * ‖x-y‖ := by
    calc
      _ ≤ ∑ _i : Fin n, ‖x-y‖ := by
        apply Finset.sum_le_sum
        intro i _
        exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (x-y) i)
      _ = _ := by simp
  have h := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hnR.le)
  simpa [← mul_assoc, inv_mul_cancel₀ hnR.ne'] using h

theorem solution {n : ℕ} (hn : 2 ≤ n) (t : ℝ) (ht : 0 < t) (x x' : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) (hx' : ∀ i, x' i ∈ Set.Icc (0 : ℝ) 1) :
    Phi x t - Phi x' t ≤ (1 + 2 * Real.sqrt (t / n)) * ‖x - x'‖ ∧
      Psi x t - Psi x' t ≤ (1 + 6 * Real.sqrt (t / n)) * ‖x - x'‖ := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : 0 ≤ (n : ℝ) - 1 := by linarith
  have hs (y : Fin n → ℝ) : 0 ≤ sampleVar y := by unfold sampleVar; positivity
  have he (y : Fin n → ℝ) : Real.sqrt (2 * sampleVar y * t / n) =
      Real.sqrt (2 * sampleVar y) * Real.sqrt (t / n) := by
    rw [mul_div_assoc, Real.sqrt_mul (mul_nonneg (by norm_num) (hs y))]
  have he' (y : Fin n → ℝ) : Real.sqrt (18 * sampleVar y * t / n) =
      3 * (Real.sqrt (2 * sampleVar y) * Real.sqrt (t / n)) := by
    rw [show 18 * sampleVar y * t / n = 9 * (2 * sampleVar y * t / n) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9), show Real.sqrt 9 = 3 by norm_num, he]
  have hm := mean_lipschitz hn x x'
  have hv := mul_le_mul_of_nonneg_right (std_lipschitz hn x x') (Real.sqrt_nonneg (t/n))
  constructor
  · unfold Phi
    rw [he, he]
    nlinarith
  · unfold Psi
    rw [he', he']
    nlinarith

#print axioms solution
