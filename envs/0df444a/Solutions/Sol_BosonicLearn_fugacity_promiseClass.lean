-- Prove2me | solution 1 for BosonicLearn.fugacity_promiseClass
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T19:50:49.621705+00:00
-- url     : https://prove2.me/submissions/558d4603-6700-461b-be11-62321e11cda2

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_promiseClass
import Theorems.Thm_BosonicLearn_fugacity_isGaussianState

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix
open scoped ComplexOrder

open BosonicLearn

noncomputable section

/-- If `0 ≺ A ⪯ c·1` then `A⁻¹ ⪰ c⁻¹·1`. -/
private lemma inv_ge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (c : ℝ) (hc : 0 < c)
    (hAc : (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A).PosSemidef) :
    (A⁻¹ - ((c⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hAh : Aᴴ = A := hA.isHermitian.eq
  have hAih : (A⁻¹)ᴴ = A⁻¹ := hA.isHermitian.inv.eq
  have hc1 : (((c⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hA.isHermitian.inv.sub hc1) fun v => ?_
  set x : Fin n → ℂ := A⁻¹ *ᵥ v with hx
  have hAx : A *ᵥ x = v := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hAdet, Matrix.one_mulVec]
  -- the three scalars
  set N : ℂ := star v ⬝ᵥ v with hN
  set P : ℂ := star v ⬝ᵥ (A⁻¹ *ᵥ v) with hP
  set Qv : ℂ := star v ⬝ᵥ (A *ᵥ v) with hQv
  have h1 : star x ⬝ᵥ (A *ᵥ v) = N := by
    rw [Matrix.dotProduct_mulVec, ← hAh, ← Matrix.star_mulVec, hAx]
  have h2 : star x ⬝ᵥ v = P := by
    rw [hx, Matrix.star_mulVec, hAih, ← Matrix.dotProduct_mulVec]
  have hpos := hA.posSemidef.dotProduct_mulVec_nonneg (x - ((c⁻¹ : ℝ) : ℂ) • v)
  have hexp : star (x - ((c⁻¹ : ℝ) : ℂ) • v) ⬝ᵥ (A *ᵥ (x - ((c⁻¹ : ℝ) : ℂ) • v)) =
      P - ((c⁻¹ : ℝ) : ℂ) * N - ((c⁻¹ : ℝ) : ℂ) * N + ((c⁻¹ : ℝ) : ℂ) * ((c⁻¹ : ℝ) : ℂ) * Qv := by
    have hs : star (x - ((c⁻¹ : ℝ) : ℂ) • v) = star x - ((c⁻¹ : ℝ) : ℂ) • star v := by
      funext i
      simp
    rw [hs]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hAx, h1, h2, ← hN, ← hQv]
    ring
  rw [hexp] at hpos
  have hcmp := hAc.dotProduct_mulVec_nonneg v
  have hcmp' : star v ⬝ᵥ ((((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A) *ᵥ v) =
      ((c : ℝ) : ℂ) * N - Qv := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul]
  rw [hcmp'] at hcmp
  have hci : (0 : ℂ) ≤ ((c⁻¹ : ℝ) : ℂ) * ((c⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    exact Complex.zero_le_real.mpr (by positivity)
  have hsum := add_nonneg hpos (mul_nonneg hci hcmp)
  have hcc : ((c⁻¹ : ℝ) : ℂ) * ((c : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne']
    simp
  have hfin : star v ⬝ᵥ ((A⁻¹ - ((c⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) =
      P - ((c⁻¹ : ℝ) : ℂ) * N - ((c⁻¹ : ℝ) : ℂ) * N + ((c⁻¹ : ℝ) : ℂ) * ((c⁻¹ : ℝ) : ℂ) * Qv +
        ((c⁻¹ : ℝ) : ℂ) * ((c⁻¹ : ℝ) : ℂ) * (((c : ℝ) : ℂ) * N - Qv) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul]
    linear_combination (-(((c⁻¹ : ℝ) : ℂ)) * N) * hcc
  rw [hfin]
  exact hsum

/-- The real `2n × 2n` form of a positive semidefinite complex matrix is positive semidefinite. -/
private lemma realify_posSemidef {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef) :
    (Matrix.fromBlocks (H.map Complex.re) (-(H.map Complex.im)) (H.map Complex.im)
      (H.map Complex.re) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ).PosSemidef := by
  have hsym : ∀ j k, H k j = star (H j k) := by
    intro j k
    have := congrFun (congrFun hH.isHermitian.eq j) k
    rw [Matrix.conjTranspose_apply] at this
    rw [← this, star_star]
  have hre : ∀ j k, (H k j).re = (H j k).re := fun j k => by rw [hsym j k]; simp
  have him : ∀ j k, (H k j).im = -(H j k).im := fun j k => by rw [hsym j k]; simp
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.fromBlocks_transpose]
    congr 1
    · ext j k; simp [hre k j]
    · ext j k; simp [him k j]
    · ext j k; simp [him k j]
    · ext j k; simp [hre k j]
  · -- the quadratic form is `Re (v† H v)` for `v = a + i b`
    set v : Fin n → ℂ := fun j => (x (Sum.inl j) : ℂ) + Complex.I * (x (Sum.inr j) : ℂ) with hv
    have hnn := hH.dotProduct_mulVec_nonneg v
    have hval : star x ⬝ᵥ ((Matrix.fromBlocks (H.map Complex.re) (-(H.map Complex.im))
        (H.map Complex.im) (H.map Complex.re) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) *ᵥ x) =
        (star v ⬝ᵥ (H *ᵥ v)).re := by
      simp only [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.map_apply, Matrix.neg_apply, Pi.star_apply, star_trivial, Complex.re_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, Finset.mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hv, Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
        Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
      ring
    rw [hval]
    exact (Complex.nonneg_iff.mp hnn).1

theorem solution {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) (ν : ℝ) (hν : 0 < ν)
    (hRν : (R - ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef)
    (ρ : State (Occupation (Fin n))) (hρ : ρ.coefficients = fugacityCoeff R) :
    ρ ∈ promiseClass n ν := by
  obtain ⟨ρ₀, hρ₀, hG⟩ := fugacity_isGaussianState R hR hR1
  have hρeq : ρ₀ = ρ := by
    obtain ⟨c₀, d₀⟩ := ρ₀
    obtain ⟨c, d⟩ := ρ
    simp only at hρ hρ₀
    subst hρ
    subst hρ₀
    rfl
  rw [hρeq] at hG
  refine ⟨0, _, hG, ?_⟩
  have h1ν : (0 : ℝ) < 1 + ν := by linarith
  -- `(1 − R)⁻¹ ⪰ (1 + ν)·1`
  have hunit : IsUnit (1 - R).det := (Matrix.isUnit_iff_isUnit_det _).mp hR1.isUnit
  have hAc : ((((1 + ν)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (1 - R)).PosSemidef := by
    have e : (((1 + ν)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (1 - R) =
        R - ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      have hsc : ((ν / (1 + ν) : ℝ) : ℂ) = 1 - (((1 + ν)⁻¹ : ℝ) : ℂ) := by
        have : ν / (1 + ν) = 1 - (1 + ν)⁻¹ := by field_simp; ring
        rw [this]; push_cast; ring
      rw [hsc, sub_smul, one_smul]
      abel
    rw [e]
    exact hRν
  have hinv := inv_ge (1 - R) hR1 ((1 + ν)⁻¹) (inv_pos.mpr h1ν) hAc
  rw [inv_inv] at hinv
  -- `C − (1 + 2ν)·1 = 2((1 − R)⁻¹ − (1 + ν)·1)`
  have hCeq : (1 + R) * (1 - R)⁻¹ = (2 : ℂ) • (1 - R)⁻¹ - 1 := by
    have h1 : (1 + R) = (2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (1 - R) := by
      rw [two_smul]; abel
    rw [h1, Matrix.sub_mul, Matrix.mul_nonsing_inv _ hunit, Matrix.smul_mul, Matrix.one_mul]
  set C : Matrix (Fin n) (Fin n) ℂ := (1 + R) * (1 - R)⁻¹ with hCdef
  have hCpsd : (C - ((1 + 2 * ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
    have e : C - ((1 + 2 * ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
        ((2 : ℝ) : ℂ) • ((1 - R)⁻¹ - ((1 + ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      rw [hCeq]
      ext a b
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e]
    exact hinv.smul (Complex.zero_le_real.mpr (by norm_num))
  have hreal := realify_posSemidef _ hCpsd
  have e : (1 / 2 : ℝ) • Matrix.fromBlocks (C.map Complex.re) (-(C.map Complex.im))
        (C.map Complex.im) (C.map Complex.re) -
      (1 / 2 + ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) =
      (1 / 2 : ℝ) • Matrix.fromBlocks
        ((C - ((1 + 2 * ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).map Complex.re)
        (-((C - ((1 + 2 * ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).map Complex.im))
        ((C - ((1 + 2 * ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).map Complex.im)
        ((C - ((1 + 2 * ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).map Complex.re) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      by_cases hab : a = b <;>
      simp [hab] <;> ring
  rw [e]
  exact hreal.smul (by norm_num)
