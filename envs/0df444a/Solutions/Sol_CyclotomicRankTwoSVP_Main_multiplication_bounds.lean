-- Prove2me | solution 1 for CyclotomicRankTwoSVP.Main.multiplication_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:26:08.8012+00:00
-- url     : https://prove2.me/submissions/c371aeb0-00c1-42f1-9b3c-66f41301364e

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Checker

noncomputable section
namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

set_option maxHeartbeats 1000000

private lemma zeta_primitive (q : ℕ) [Fact q.Prime] : IsPrimitiveRoot (zeta q) q := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  letI : NeZero q := ⟨hq0⟩
  letI : NeZero (q : ℚ) := ⟨Nat.cast_ne_zero.mpr hq0⟩
  letI : IsCyclotomicExtension {q} ℚ (K q) := CyclotomicField.isCyclotomicExtension q ℚ
  simp only [zeta, dif_neg hq0]
  exact IsCyclotomicExtension.zeta_spec q ℚ (K q)

private lemma norm_zeta_embedding (q : ℕ) [Fact q.Prime]
    (σ : K q →ₐ[ℚ] ℂ) : ‖σ (zeta q)‖ = 1 := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  exact Complex.norm_eq_one_of_pow_eq_one
    ((zeta_primitive q).map_of_injective σ.injective).pow_eq_one hq0

private lemma star_root_pow {q : ℕ} [NeZero q] {z : ℂ}
    (hzq : z ^ q = 1) (hz : ‖z‖ = 1) (a : ZMod q) :
    star (z ^ a.val) = z ^ (-a).val := by
  have hmod : (a.val + (-a).val) % q = 0 := by
    rw [← ZMod.val_add]
    simp
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hmod
  have hprod : z ^ a.val * z ^ (-a).val = 1 := by
    calc
      z ^ a.val * z ^ (-a).val = z ^ (a.val + (-a).val) := (pow_add _ _ _).symm
      _ = (z ^ q) ^ c := by rw [hc, pow_mul]
      _ = 1 := by rw [hzq, one_pow]
  have hstar : star z = z⁻¹ := by
    rw [Complex.star_def, ← Complex.inv_eq_conj hz]
  rw [star_pow, hstar, inv_pow]
  exact inv_eq_of_mul_eq_one_right hprod

private lemma star_g_embedding {q M n : ℕ} [Fact q.Prime]
    (A : Incidence M n) (α : Fin n → ℕ) (σ : K q →ₐ[ℚ] ℂ) :
    star (σ (g A α)) = σ (g A α) := by
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hzq : σ (zeta q) ^ q = 1 :=
    ((zeta_primitive q).map_of_injective σ.injective).pow_eq_one
  have hz := norm_zeta_embedding q σ
  simp only [g, map_sum, map_add, map_pow, star_sum, star_add]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [star_root_pow hzq hz, star_root_pow hzq hz, neg_neg]
  exact add_comm _ _

private lemma N_nonneg {q : ℕ} (y : K q) : 0 ≤ N y := by
  unfold N
  exact Finset.sum_nonneg fun σ _ => sq_nonneg _

private lemma sqrt_N_mul_ge {q : ℕ} (a y : K q) (c : ℝ) (hc : 0 ≤ c)
    (ha : ∀ σ : K q →ₐ[ℚ] ℂ, c ≤ ‖σ a‖) :
    c * Real.sqrt (N y) ≤ Real.sqrt (N (a * y)) := by
  have hN : c ^ 2 * N y ≤ N (a * y) := by
    calc
      c ^ 2 * N y = ∑ σ : K q →ₐ[ℚ] ℂ, c ^ 2 * ‖σ y‖ ^ 2 := by
        rw [N, Finset.mul_sum]
      _ ≤ ∑ σ : K q →ₐ[ℚ] ℂ, ‖σ (a * y)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro σ hσ
        have hs : c ^ 2 ≤ ‖σ a‖ ^ 2 := (sq_le_sq₀ hc (norm_nonneg _)).mpr (ha σ)
        calc
          c ^ 2 * ‖σ y‖ ^ 2 ≤ ‖σ a‖ ^ 2 * ‖σ y‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hs (sq_nonneg _)
          _ = ‖σ (a * y)‖ ^ 2 := by simp [mul_pow]
      _ = N (a * y) := rfl
  apply (sq_le_sq₀ (mul_nonneg hc (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt (N_nonneg y), Real.sq_sqrt (N_nonneg (a * y))]
  exact hN

private lemma sqrt_N_mul_le {q : ℕ} (a y : K q) (c : ℝ) (hc : 0 ≤ c)
    (ha : ∀ σ : K q →ₐ[ℚ] ℂ, ‖σ a‖ ≤ c) :
    Real.sqrt (N (a * y)) ≤ c * Real.sqrt (N y) := by
  have hN : N (a * y) ≤ c ^ 2 * N y := by
    calc
      N (a * y) = ∑ σ : K q →ₐ[ℚ] ℂ, ‖σ (a * y)‖ ^ 2 := rfl
      _ ≤ ∑ σ : K q →ₐ[ℚ] ℂ, c ^ 2 * ‖σ y‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro σ hσ
        have hs : ‖σ a‖ ^ 2 ≤ c ^ 2 := (sq_le_sq₀ (norm_nonneg _) hc).mpr (ha σ)
        calc
          ‖σ (a * y)‖ ^ 2 = ‖σ a‖ ^ 2 * ‖σ y‖ ^ 2 := by simp [mul_pow]
          _ ≤ c ^ 2 * ‖σ y‖ ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      _ = c ^ 2 * N y := by rw [N, Finset.mul_sum]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hc (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (N_nonneg y), Real.sq_sqrt (N_nonneg (a * y))]
  exact hN

private lemma W_eq_three_mul {M n : ℕ} (A : Incidence M n) (hA : IsX3C A) :
    W A = 3 * n := by
  unfold W
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ) (by
    intro x hx
    simp)]
  have hfiber (j : Fin n) : {a ∈ incidences A | a.2 = j}.card = 3 := by
    have heq : {a ∈ incidences A | a.2 = j} =
        (Finset.univ.filter fun i => A i j) ×ˢ ({j} : Finset (Fin n)) := by
      ext ⟨i, k⟩
      simp only [incidences, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product, Finset.mem_singleton]
      constructor
      · rintro ⟨hAik, rfl⟩
        exact ⟨hAik, rfl⟩
      · rintro ⟨hAij, hjk⟩
        subst k
        exact ⟨hAij, rfl⟩
    rw [heq, Finset.card_product, hA j]
    simp
  simp [hfiber, Nat.mul_comm]

end CyclotomicRankTwoSVP.Main

open CyclotomicRankTwoSVP.Main
open scoped BigOperators

theorem solution :
    ∃ C₀ k₀ : ℕ, 1 ≤ C₀ ∧ 1 ≤ k₀ ∧
      ∀ (k q : ℕ) [Fact q.Prime], Odd q → parameterDomain C₀ k₀ k q →
        ∀ (M n : ℕ) (A : Incidence M n), IsX3C A → Nondegenerate A →
          ∀ α : Fin n → ℕ, IsSidon α → 4 * beta α M < q →
            ∀ y w : K q,
              Real.sqrt (N (U k A α * y)) ≥ Q k A * Real.sqrt (N y) ∧
              Real.sqrt (N (V α * w)) ≤ 2 * W A * Real.sqrt (N w) := by
  refine ⟨1, 1, le_rfl, le_rfl, ?_⟩
  intro k q inst hq hdom M n A hA hnd α hα hsep y w
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hU (σ : K q →ₐ[ℚ] ℂ) : (Q k A : ℝ) ≤ ‖σ (U k A α)‖ := by
    have hg : (σ (g A α)).im = 0 := by
      rw [← Complex.conj_eq_iff_im]
      exact CyclotomicRankTwoSVP.Main.star_g_embedding A α σ
    have hre : (σ (U k A α)).re =
        (Q k A : ℝ) + (σ (g A α)).re ^ 2 := by
      simp [U, Complex.add_re, Complex.mul_re, hg, pow_two]
    have hQre : (Q k A : ℝ) ≤ (σ (U k A α)).re := by
      rw [hre]
      nlinarith [sq_nonneg (σ (g A α)).re]
    exact hQre.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hV (σ : K q →ₐ[ℚ] ℂ) : ‖σ (V α)‖ ≤ (2 * W A : ℝ) := by
    have hz := CyclotomicRankTwoSVP.Main.norm_zeta_embedding q σ
    have hsum : ‖∑ j, σ (zeta q) ^ α j‖ ≤ (n : ℝ) := by
      calc
        ‖∑ j, σ (zeta q) ^ α j‖ ≤ ∑ j, ‖σ (zeta q) ^ α j‖ := norm_sum_le _ _
        _ = (n : ℝ) := by simp [norm_pow, hz]
    have hVn : ‖σ (V α)‖ ≤ 6 * (n : ℝ) := by
      calc
        ‖σ (V α)‖ = 6 * ‖∑ j, σ (zeta q) ^ α j‖ := by
          simp only [V, map_mul, map_sum, map_pow, norm_mul]
          rw [show ‖σ (6 : K q)‖ = (6 : ℝ) by
            rw [map_ofNat]
            exact Complex.norm_ofNat 6]
        _ ≤ 6 * (n : ℝ) := by nlinarith
    rw [CyclotomicRankTwoSVP.Main.W_eq_three_mul A hA]
    norm_num at hVn ⊢
    nlinarith
  exact ⟨CyclotomicRankTwoSVP.Main.sqrt_N_mul_ge _ _ _ (Nat.cast_nonneg _) hU,
    CyclotomicRankTwoSVP.Main.sqrt_N_mul_le _ _ _ (by positivity) hV⟩
