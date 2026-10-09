-- Prove2me | solution 1 for GaussianMatrix.inverse_wishart_spectral_moment
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T06:42:59.036175+00:00
-- url     : https://prove2.me/submissions/5c130068-09bf-4d4e-9f34-39328fa44b8a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_wishart_lambda_min_tail
import Theorems.Thm_GaussianMatrix_specNorm_inv_gram_eq
import Theorems.Thm_GaussianMatrix_tw_inverse_moment_numeric
import Theorems.Thm_GaussianMatrix_integral_le_of_tail_bound

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- Entries of `(G Gᵀ)⁻¹` are measurable functions of `G`. -/
theorem iwsm_measurable_inv_gram_entry {r k : ℕ} (a b : Fin r) :
    Measurable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ a b) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have hc : Continuous (fun G : Fin r → Fin k → ℝ => Matrix.of G * (Matrix.of G)ᵀ) := by
    fun_prop
  refine Measurable.mul ?_ ?_
  · exact (hc.matrix_det.measurable).inv
  · exact ((hc.matrix_adjugate).matrix_elem a b).measurable

open scoped Matrix.Norms.L2Operator in
/-- `G ↦ ‖(G Gᵀ)⁻¹‖` is measurable. -/
theorem iwsm_measurable_specNorm_inv_gram {r k : ℕ} :
    Measurable (fun G : Fin r → Fin k → ℝ => specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹) := by
  have h1 : Measurable (fun G : Fin r → Fin k → ℝ =>
      Matrix.of.symm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹) := by
    refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    simp only [Matrix.of_symm_apply]
    exact iwsm_measurable_inv_gram_entry a b
  have h2 : Continuous (fun M : Fin r → Fin r → ℝ => ‖Matrix.of M‖) :=
    continuous_norm.comp continuous_id
  exact h2.measurable.comp h1

open scoped Matrix.Norms.L2Operator in
lemma iwsm_specNorm_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n ℝ) : 0 ≤ specNorm A := norm_nonneg _

open scoped Matrix.Norms.L2Operator in
lemma iwsm_specNorm_fin_zero (A : Matrix (Fin 0) (Fin 0) ℝ) : specNorm A = 0 := by
  unfold specNorm
  rw [Subsingleton.elim A 0, norm_zero]

end GaussianMatrix

open GaussianMatrix

theorem solution {r k p : ℕ} (hp : 1 ≤ p) (hp18 : p ≤ 18)
    (hrk : r + 2 * p ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ p)
      (gaussianMatrix r k) ∧
    ∫ G, specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ p ∂(gaussianMatrix r k)
      ≤ (Real.exp 1 ^ 2 * ((k : ℝ) + r) / (2 * ((k : ℝ) - r) ^ 2)) ^ p := by
  rcases Nat.eq_zero_or_pos r with hr0 | hr1
  · -- `r = 0`: the Gram matrix is `0 × 0`, so the integrand vanishes
    subst hr0
    have hf : (fun G : Fin 0 → Fin k → ℝ => specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ p)
        = fun _ => 0 := by
      funext G
      rw [iwsm_specNorm_fin_zero, zero_pow (by omega)]
    rw [hf]
    refine ⟨integrable_zero _ _ _, ?_⟩
    rw [integral_zero]
    positivity
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hrk' : r ≤ k := by omega
  have hkr : 2 * (p : ℝ) ≤ (k : ℝ) - r := by
    have : ((r + 2 * p : ℕ) : ℝ) ≤ k := by exact_mod_cast hrk
    push_cast at this; linarith
  have hr1R : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  set f : (Fin r → Fin k → ℝ) → ℝ :=
    fun G => specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ p with hf_def
  have hmeas : Measurable f := (iwsm_measurable_specNorm_inv_gram (r := r) (k := k)).pow_const p
  have hnn : 0 ≤ᵐ[gaussianMatrix r k] f :=
    Filter.Eventually.of_forall fun G => pow_nonneg (iwsm_specNorm_nonneg _) p
  set e : ℝ := ((k : ℝ) - r + 1) / 2 with he_def
  set B : ℝ := ((k : ℝ) + r) / 2 with hB_def
  have hB0 : 0 < B := by rw [hB_def]; positivity
  have hG0 : 0 < Real.Gamma ((k : ℝ) - r + 2) := Real.Gamma_pos_of_pos (by linarith)
  set C : ℝ := (1 / Real.Gamma ((k : ℝ) - r + 2)) * B ^ e with hC_def
  have hC : 0 < C := by rw [hC_def]; positivity
  set m : ℝ := ((k : ℝ) - r + 1) / (2 * p) with hm_def
  have hp0 : (0 : ℝ) < p := by linarith
  have hm : 1 < m := by
    rw [hm_def, one_lt_div (by positivity)]; linarith
  have htail : ∀ τ : ℝ, 0 < τ → (gaussianMatrix r k) {G | τ < f G}
      ≤ ENNReal.ofReal (C * τ ^ (-m)) := by
    intro τ hτ
    have hsub : {G | τ < f G} ⊆ {G | sMin (Matrix.of G)ᵀ ^ 2 ≤ τ ^ (-(p : ℝ)⁻¹)} := by
      intro G hG
      simp only [Set.mem_ofPred_eq, hf_def] at hG ⊢
      rw [specNorm_inv_gram_eq] at hG
      set s2 := sMin (Matrix.of G)ᵀ ^ 2
      have hs2 : 0 < s2 := by
        rcases (sq_nonneg (sMin (Matrix.of G)ᵀ)).lt_or_eq with h | h
        · exact h
        · exfalso
          have : s2 = 0 := h.symm
          rw [this, div_zero, zero_pow (by omega)] at hG
          linarith
      have hlt : τ ^ (p : ℝ)⁻¹ < 1 / s2 := by
        by_contra hcon
        rw [not_lt] at hcon
        have h1 : (1 / s2) ^ p ≤ (τ ^ (p : ℝ)⁻¹) ^ p :=
          pow_le_pow_left₀ (by positivity) hcon p
        rw [Real.rpow_inv_natCast_pow hτ.le (by omega)] at h1
        linarith
      have hτp : 0 < τ ^ (p : ℝ)⁻¹ := Real.rpow_pos_of_pos hτ _
      rw [Real.rpow_neg hτ.le]
      rw [lt_div_iff₀ hs2] at hlt
      have h2 : s2 ≤ 1 / τ ^ (p : ℝ)⁻¹ := by rw [le_div_iff₀ hτp]; linarith
      rwa [one_div] at h2
    refine (measure_mono hsub).trans
      ((wishart_lambda_min_tail hr1 hrk' _ (Real.rpow_pos_of_pos hτ _)).trans ?_)
    apply ENNReal.ofReal_le_ofReal
    apply le_of_eq
    rw [mul_div_assoc, ← hB_def, Real.mul_rpow (Real.rpow_pos_of_pos hτ _).le hB0.le,
      ← Real.rpow_mul hτ.le]
    have hexp : -(p : ℝ)⁻¹ * e = -m := by rw [he_def, hm_def]; field_simp
    rw [hexp, hC_def]
    ring
  obtain ⟨hI, hle⟩ := integral_le_of_tail_bound (gaussianMatrix r k) f hmeas.aemeasurable hnn
    C m hC hm htail
  refine ⟨hI, hle.trans ?_⟩
  have hx : ((k - r : ℕ) : ℝ) = (k : ℝ) - r := Nat.cast_sub hrk'
  have hB8 := tw_inverse_moment_numeric hp hp18 (show 2 * p ≤ k - r by omega)
  rw [hx] at hB8
  have hd : (k : ℝ) - r + 1 ≠ 0 := by linarith
  have hd2 : (k : ℝ) - r + 1 - 2 * p ≠ 0 := by linarith
  have h1m : 1 / m = 2 * p / ((k : ℝ) - r + 1) := by rw [hm_def, one_div_div]
  have hCm : C ^ (1 / m) = (1 / Real.Gamma ((k : ℝ) - r + 2)) ^ (2 * (p : ℝ) / ((k : ℝ) - r + 1))
      * B ^ p := by
    rw [hC_def, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hB0.le, h1m]
    congr 1
    rw [show e * (2 * (p : ℝ) / ((k : ℝ) - r + 1)) = ((p : ℕ) : ℝ) by
      rw [he_def]; field_simp, Real.rpow_natCast]
  have hmm : m / (m - 1) = 1 + 2 * (p : ℝ) / ((k : ℝ) - r + 1 - 2 * p) := by
    have hm1 : m - 1 ≠ 0 := by linarith
    rw [hm_def]
    field_simp
    ring
  calc C ^ (1 / m) * m / (m - 1)
      = ((1 + 2 * (p : ℝ) / ((k : ℝ) - r + 1 - 2 * p))
          * (1 / Real.Gamma ((k : ℝ) - r + 2)) ^ (2 * (p : ℝ) / ((k : ℝ) - r + 1))) * B ^ p := by
        rw [mul_div_assoc, hmm, hCm]; ring
    _ ≤ (Real.exp 1 / ((k : ℝ) - r)) ^ (2 * p) * B ^ p :=
        mul_le_mul_of_nonneg_right hB8 (by positivity)
    _ = (Real.exp 1 ^ 2 * ((k : ℝ) + r) / (2 * ((k : ℝ) - r) ^ 2)) ^ p := by
        rw [pow_mul, ← mul_pow, hB_def]
        congr 1
        have : (k : ℝ) - r ≠ 0 := by linarith
        field_simp
