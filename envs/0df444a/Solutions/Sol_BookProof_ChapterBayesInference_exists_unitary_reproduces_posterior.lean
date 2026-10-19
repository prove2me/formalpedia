-- Prove2me | solution 1 for BookProof.ChapterBayesInference.exists_unitary_reproduces_posterior
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:53:24.17267+00:00
-- url     : https://prove2.me/submissions/4414feb3-78ec-4740-a829-3b997ce9061a

import Mathlib
import Definitions.Def_ChapterBayesInference
-- Generated from ChapterBayesInference.lean — theorem BookProof.ChapterBayesInference.exists_unitary_reproduces_posterior
open BookProof.ChapterBayesInference


open scoped BigOperators


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

variable {prior : X → ℝ} {L : X → Y → ℝ}
open Matrix in
theorem householder_col {n : Type*} [Fintype n] [DecidableEq n] (v : n → ℂ)
    (hv : star v ⬝ᵥ v = 1) (i₀ : n) (hreal : star (v i₀) = v i₀) :
    ∃ U ∈ Matrix.unitaryGroup n ℂ, ∀ i, U i i₀ = v i := by
  by_cases h1 : v i₀ = 1
  · -- then v is the basis vector
    have hrest : ∀ i, i ≠ i₀ → v i = 0 := by
      intro i hi
      have hsum : ∑ k, star (v k) * v k = 1 := hv
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), h1] at hsum
      simp only [star_one, mul_one, add_eq_left] at hsum
      have hnn : ∀ k ∈ Finset.univ.erase i₀, 0 ≤ (star (v k) * v k).re := fun k _ => by
        rw [show star (v k) * v k = ((Complex.normSq (v k) : ℝ) : ℂ) by
          rw [Complex.normSq_eq_conj_mul_self]; rfl]
        simp [Complex.normSq_nonneg]
      have hre := congrArg Complex.re hsum
      rw [Complex.re_sum, Complex.zero_re] at hre
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hre i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
      rw [show star (v i) * v i = ((Complex.normSq (v i) : ℝ) : ℂ) by
          rw [Complex.normSq_eq_conj_mul_self]; rfl] at this
      simpa using this
    refine ⟨1, one_mem _, fun i => ?_⟩
    by_cases hi : i = i₀
    · subst hi; simp [h1]
    · simp [Matrix.one_apply, hi, hrest i hi]
  · set e : n → ℂ := Pi.single i₀ 1 with he
    set w : n → ℂ := e - v with hw
    set c : ℂ := star w ⬝ᵥ w with hc
    have hcval : c = 2 * (1 - v i₀) := by
      rw [hc, hw]
      simp only [star_sub, sub_dotProduct, dotProduct_sub, he]
      simp only [dotProduct, Pi.star_apply, Pi.single_apply]
      simp only [apply_ite (star : ℂ → ℂ), star_one, star_zero, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have : ∑ x, star (v x) * v x = 1 := hv
      rw [this, hreal]; ring
    have hc0 : c ≠ 0 := by
      rw [hcval]; intro h
      apply h1
      have := mul_eq_zero.1 h
      rcases this with h | h
      · norm_num at h
      · exact (sub_eq_zero.1 h).symm
    set a : ℂ := 2 / c with ha
    have hstar_a : star a = a := by
      rw [ha, hcval, star_div₀, star_mul, star_sub, hreal]; simp only [star_ofNat, star_one]; ring
    set M : Matrix n n ℂ := vecMulVec w (star w) with hM
    have hMH : Mᴴ = M := by rw [hM, conjTranspose_vecMulVec, star_star]
    have hMM : M * M = c • M := by
      rw [hM, vecMulVec_mul_vecMulVec, vecMulVec_smul]
    refine ⟨1 - a • M, ?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      have hs : star (1 - a • M) = 1 - a • M := by
        rw [Matrix.star_eq_conjTranspose, conjTranspose_sub, conjTranspose_one,
          conjTranspose_smul, hstar_a, hMH]
      rw [hs, sub_mul, mul_sub, mul_sub, one_mul, mul_one, smul_mul_smul_comm, hMM, smul_smul]
      have hac : a * a * c = 2 * a := by rw [ha]; field_simp
      rw [hac, one_mul, show (2 * a) • M = a • M + a • M by rw [two_mul, add_smul]]
      abel
    · intro i
      have hkey : a * (1 - v i₀) = 1 := by rw [ha, hcval]; field_simp
      have hentry : (1 - a • M) i i₀ = (1 : Matrix n n ℂ) i i₀ - a * (w i * star (w i₀)) := by
        rw [Matrix.sub_apply, Matrix.smul_apply, hM, vecMulVec_apply, smul_eq_mul]; rfl
      have hwi0 : star (w i₀) = 1 - v i₀ := by
        rw [hw, Pi.sub_apply, he, Pi.single_eq_same, star_sub, star_one, hreal]
      rw [hentry, hwi0]
      by_cases hi : i = i₀
      · subst hi
        rw [Matrix.one_apply_eq, hw, Pi.sub_apply, he, Pi.single_eq_same]
        linear_combination (v i - 1) * hkey
      · rw [Matrix.one_apply_ne hi, hw, Pi.sub_apply, he, Pi.single_eq_of_ne hi]
        linear_combination (v i) * hkey

theorem solution
    (hprior : ∀ x, 0 ≤ prior x) (hprior_sum : ∑ x, prior x = 1)
    (hL : ∀ x y, 0 ≤ L x y) (hL_row : ∀ x, ∑ y, L x y = 1)
    (i₀ : X × Y) :
    ∃ U : Matrix (X × Y) (X × Y) ℂ, U ∈ Matrix.unitaryGroup (X × Y) ℂ ∧
      (∀ x y, ‖U (x, y) i₀‖ ^ 2 = joint prior L x y) ∧
      ∀ y, 0 < evidence prior L y → ∀ x,
        posterior prior L y x =
          ‖U (x, y) i₀‖ ^ 2 / ∑ x', ‖U (x', y) i₀‖ ^ 2 := by
  have hj : ∀ x y, 0 ≤ joint prior L x y := fun x y => mul_nonneg (hprior x) (hL x y)
  set v : X × Y → ℂ := fun p => ((Real.sqrt (joint prior L p.1 p.2) : ℝ) : ℂ) with hvdef
  have hnorm : ∀ p : X × Y, ‖v p‖ ^ 2 = joint prior L p.1 p.2 := by
    intro p
    rw [hvdef]; simp only
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hj _ _)]
  have hv : star v ⬝ᵥ v = 1 := by
    have : ∀ p : X × Y, star (v p) * v p = ((joint prior L p.1 p.2 : ℝ) : ℂ) := by
      intro p
      rw [hvdef]; simp only
      rw [show star ((Real.sqrt (joint prior L p.1 p.2) : ℝ) : ℂ) =
        ((Real.sqrt (joint prior L p.1 p.2) : ℝ) : ℂ) from Complex.conj_ofReal _, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hj _ _)]
    simp only [dotProduct, Pi.star_apply, this]
    rw [← Complex.ofReal_sum, Fintype.sum_prod_type]
    simp only [joint]
    rw [show ∑ x, ∑ y, prior x * L x y = ∑ x, prior x by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.mul_sum, hL_row, mul_one], hprior_sum]
    simp
  have hreal : star (v i₀) = v i₀ := Complex.conj_ofReal _
  obtain ⟨U, hU, hcol⟩ := householder_col v hv i₀ hreal
  refine ⟨U, hU, fun x y => ?_, fun y hy x => ?_⟩
  · rw [hcol]; exact hnorm (x, y)
  · simp only [hcol]
    rw [show ∑ x', ‖v (x', y)‖ ^ 2 = evidence prior L y by
      simp only [hnorm, joint, evidence]]
    rw [hnorm (x, y)]
    rfl
