-- Prove2me | solution 1 for BosonicLearn.fugacityFamily_promiseClass
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T07:38:36.224795+00:00
-- url     : https://prove2.me/submissions/34dc767d-f663-4d1c-8c82-a59d0b6d0e44
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_fugacityFamily
import Definitions.Def_BosonicLearn_Gsupp
import Definitions.Def_BosonicLearn_IsPassive
import Definitions.Def_BosonicLearn_promiseClass
import Theorems.Thm_BosonicLearn_lemma_2
import Theorems.Thm_BosonicLearn_fugacity_promiseClass

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

open BosonicLearn

noncomputable section

/-- A Hermitian matrix of operator norm at most `c` lies between `-c` and `c` in the Loewner order. -/
private lemma opnorm_form {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian) (c : ℝ)
    (h : WHMultiplicativity.schattenNorm ⊤ X ≤ c) :
    (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef ∧
      (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X).PosSemidef := by
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖ ≤ c := by
    simpa [WHMultiplicativity.schattenNorm] using h
  have key : ∀ v : Fin n → ℂ, |(star v ⬝ᵥ (X *ᵥ v)).re| ≤ c * ∑ i, ‖v i‖ ^ 2 := by
    intro v
    set w : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v with hw
    have h1 : inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w) = star v ⬝ᵥ (X *ᵥ v) := by
      rw [hw, Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    have h2 : ‖inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w)‖ ≤ c * ‖w‖ ^ 2 := by
      calc ‖inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w)‖
          ≤ ‖w‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X w‖ := norm_inner_le_norm _ _
        _ ≤ ‖w‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖ * ‖w‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ ‖w‖ * (c * ‖w‖) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)) (norm_nonneg _)
        _ = c * ‖w‖ ^ 2 := by ring
    have h3 : ‖w‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    rw [h1, h3] at h2
    exact (Complex.abs_re_le_norm _).trans h2
  have hsq : ∀ v : Fin n → ℂ, star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    simp only [dotProduct, Pi.star_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  have him : ∀ v : Fin n → ℂ, (star v ⬝ᵥ (X *ᵥ v)).im = 0 := fun v =>
    hX.im_star_dotProduct_mulVec_self v
  have hc1 : (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  constructor
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hc1.sub hX) fun v => ?_
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      hsq, Complex.nonneg_iff]
    have hk := abs_le.mp (key v)
    constructor
    · simp only [Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      linarith [hk.2]
    · rw [Complex.sub_im, him v, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_im, sub_zero]
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hc1.add hX) fun v => ?_
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      hsq, Complex.nonneg_iff]
    have hk := abs_le.mp (key v)
    constructor
    · simp only [Complex.add_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      linarith [hk.1]
    · rw [Complex.add_im, him v, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_im, add_zero]

theorem solution (n : ℕ) (ν ξ : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hξ0 : 0 < ξ)
    (hξ1 : ξ < 1 / 32) (X : Herm0 n) (hX : X ∈ Gsupp n) :
    ∃ ρ : State (Occupation (Fin n)), ρ.coefficients = fugacityCoeff (fugacityFamily ν ξ X) ∧
      IsPassive ρ ∧ ρ ∈ promiseClass n ν := by
  have hXh : (X : Matrix (Fin n) (Fin n) ℂ).IsHermitian := X.2.1
  have hop : WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ) ≤ 4 := hX
  obtain ⟨hminus, hplus⟩ := opnorm_form (X : Matrix (Fin n) (Fin n) ℂ) hXh 4 hop
  have h14 : 0 < 1 - 4 * ξ := by linarith
  have h14' : 1 - 4 * ξ ≠ 0 := h14.ne'
  have h1ν : 1 + ν ≠ 0 := by positivity
  set r : ℝ := ν / ((1 - 4 * ξ) * (1 + ν)) with hr
  have hrpos : 0 < r := by positivity
  have hrt : r * (1 - 4 * ξ) = ν / (1 + ν) := by
    rw [hr]
    field_simp
  have hr1 : r * (1 + 4 * ξ) < 1 := by
    rw [hr, div_mul_eq_mul_div, div_lt_one (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hν1 hξ0.le, mul_pos hξ0 hν0]
  have hRdef : fugacityFamily ν ξ X =
      ((r : ℝ) : ℂ) • (1 + ((ξ : ℝ) : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)) := rfl
  have e1 : fugacityFamily ν ξ X - ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      ((r * ξ : ℝ) : ℂ) • (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (X : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hRdef, ← hrt]
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hRν : (fugacityFamily ν ξ X -
      ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
    rw [e1]
    exact hplus.smul (Complex.zero_le_real.mpr (by positivity))
  have hRpsd : (fugacityFamily ν ξ X).PosSemidef := by
    have e : fugacityFamily ν ξ X = (fugacityFamily ν ξ X -
        ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) +
        ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [sub_add_cancel]
    rw [e]
    exact hRν.add (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by positivity)))
  have e2 : 1 - fugacityFamily ν ξ X =
      ((1 - r * (1 + 4 * ξ) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        ((r * ξ : ℝ) : ℂ) • (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
          (X : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hRdef]
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hR1 : (1 - fugacityFamily ν ξ X).PosDef := by
    rw [e2]
    exact (Matrix.PosDef.one.smul (by exact_mod_cast (sub_pos.mpr hr1))).add_posSemidef
      (hminus.smul (Complex.zero_le_real.mpr (by positivity)))
  obtain ⟨ρ, hρ, hpas⟩ := (lemma_2 (n := n)).1 (fugacityFamily ν ξ X) hRpsd hR1
  exact ⟨ρ, hρ, hpas, fugacity_promiseClass (fugacityFamily ν ξ X) hRpsd hR1 ν hν0 hRν ρ hρ⟩
