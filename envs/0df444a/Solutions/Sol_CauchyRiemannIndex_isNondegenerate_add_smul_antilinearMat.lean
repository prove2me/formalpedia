-- Prove2me | solution 1 for CauchyRiemannIndex.isNondegenerate_add_smul_antilinearMat
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T16:40:15.339725+00:00
-- url     : https://prove2.me/submissions/ace3edeb-4749-4d41-96a9-d898ef1cd63a

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.Deriv.Basic
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_symplectic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul



/-!
# Nondegeneracy of `T + σ B_γ` for large `σ`
-/

namespace CauchyRiemannIndex

open Matrix

noncomputable section

lemma antilinearMat_isSymm (b : ℂ) : (antilinearMat b).IsSymm := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [antilinearMat, Matrix.transpose_apply, Matrix.fromBlocks]

lemma crw_hasDerivAt_mulVec (Ψ : ℝ → Mat 1) (Ψ' : Mat 1) (t : ℝ) (h : HasDerivAt Ψ Ψ' t)
    (v : Fin 1 ⊕ Fin 1 → ℝ) : HasDerivAt (fun t => Ψ t *ᵥ v) (Ψ' *ᵥ v) t := by
  letI : NormedAddCommGroup (Mat 1) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Mat 1) := Matrix.normedSpace
  let L : Mat 1 →ₗ[ℝ] (Fin 1 ⊕ Fin 1 → ℝ) :=
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => Matrix.smul_mulVec c M v }
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t h

lemma crw_alg (a b a' b' X Y p₁ p₂ p₃ p₄ K m D σ : ℝ) (hσ : 0 < σ) (hp₁ : |p₁| ≤ K)
    (hp₂ : |p₂| ≤ K) (hp₃ : |p₃| ≤ K) (hp₄ : |p₄| ≤ K) (hab : m ^ 2 ≤ a ^ 2 + b ^ 2)
    (ha' : |a'| ≤ D) (hb' : |b'| ≤ D) (hXY : 0 < X ^ 2 + Y ^ 2)
    (hbig : 4 * K ^ 2 + 2 * σ * D < σ ^ 2 * m ^ 2) :
    0 < -b' * X ^ 2 + 2 * a' * X * Y + b' * Y ^ 2 +
      2 * (-b * X + a * Y) * (-(p₃ * X + p₄ * Y + σ * (b * X - a * Y))) +
      2 * (a * X + b * Y) * (p₁ * X + p₂ * Y + σ * (a * X + b * Y)) := by
  have sq_le : ∀ p : ℝ, |p| ≤ K → p ^ 2 ≤ K ^ 2 := fun p hp =>
    sq_le_sq' (abs_le.1 hp).1 (abs_le.1 hp).2
  have hp₁' := sq_le p₁ hp₁
  have hp₂' := sq_le p₂ hp₂
  have hp₃' := sq_le p₃ hp₃
  have hp₄' := sq_le p₄ hp₄
  obtain ⟨u₁, hu₁d⟩ : ∃ u, u = p₁ * X + p₂ * Y := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂d⟩ : ∃ u, u = p₃ * X + p₄ * Y := ⟨_, rfl⟩
  obtain ⟨B₁, hB₁d⟩ : ∃ u, u = a * X + b * Y := ⟨_, rfl⟩
  obtain ⟨B₂, hB₂d⟩ : ∃ u, u = b * X - a * Y := ⟨_, rfl⟩
  have hBB : B₁ ^ 2 + B₂ ^ 2 = (a ^ 2 + b ^ 2) * (X ^ 2 + Y ^ 2) := by
    rw [hB₁d, hB₂d]; ring
  have hu₁ : u₁ ^ 2 ≤ 2 * K ^ 2 * (X ^ 2 + Y ^ 2) := by
    have : u₁ ^ 2 ≤ (p₁ ^ 2 + p₂ ^ 2) * (X ^ 2 + Y ^ 2) := by
      rw [hu₁d]; linarith [sq_nonneg (p₁ * Y - p₂ * X)]
    have hK2 : p₁ ^ 2 + p₂ ^ 2 ≤ 2 * K ^ 2 := by linarith
    linarith [mul_le_mul_of_nonneg_right hK2 hXY.le]
  have hu₂ : u₂ ^ 2 ≤ 2 * K ^ 2 * (X ^ 2 + Y ^ 2) := by
    have : u₂ ^ 2 ≤ (p₃ ^ 2 + p₄ ^ 2) * (X ^ 2 + Y ^ 2) := by
      rw [hu₂d]; linarith [sq_nonneg (p₃ * Y - p₄ * X)]
    have hK2 : p₃ ^ 2 + p₄ ^ 2 ≤ 2 * K ^ 2 := by linarith
    linarith [mul_le_mul_of_nonneg_right hK2 hXY.le]
  have hP1 : -(u₁ ^ 2 + u₂ ^ 2) - σ ^ 2 * (B₁ ^ 2 + B₂ ^ 2) ≤
      σ * (2 * (u₁ * B₁ + u₂ * B₂)) := by
    linarith [sq_nonneg (u₁ + σ * B₁), sq_nonneg (u₂ + σ * B₂)]
  have hP3 : -(2 * D) * (X ^ 2 + Y ^ 2) ≤ -b' * X ^ 2 + 2 * a' * X * Y + b' * Y ^ 2 := by
    have h1 : -(D * (X ^ 2 + Y ^ 2)) ≤ b' * (Y ^ 2 - X ^ 2) := by
      rcases abs_le.1 hb' with ⟨h1, h2⟩
      linarith [mul_nonneg (by linarith : 0 ≤ b' + D) (sq_nonneg Y),
        mul_nonneg (by linarith : 0 ≤ D - b') (sq_nonneg X)]
    have h2 : -(D * (X ^ 2 + Y ^ 2)) ≤ 2 * a' * X * Y := by
      rcases abs_le.1 ha' with ⟨h1, h2⟩
      linarith [mul_nonneg (by linarith : 0 ≤ D + a') (sq_nonneg (X + Y)),
        mul_nonneg (by linarith : 0 ≤ D - a') (sq_nonneg (X - Y))]
    linarith
  have hval : -b' * X ^ 2 + 2 * a' * X * Y + b' * Y ^ 2 +
      2 * (-b * X + a * Y) * (-(p₃ * X + p₄ * Y + σ * (b * X - a * Y))) +
      2 * (a * X + b * Y) * (p₁ * X + p₂ * Y + σ * (a * X + b * Y)) =
      2 * (u₁ * B₁ + u₂ * B₂) + 2 * σ * (B₁ ^ 2 + B₂ ^ 2) +
        (-b' * X ^ 2 + 2 * a' * X * Y + b' * Y ^ 2) := by
    rw [hu₁d, hu₂d, hB₁d, hB₂d]; ring
  rw [hval]
  have h4 : σ ^ 2 * m ^ 2 * (X ^ 2 + Y ^ 2) ≤ σ ^ 2 * (B₁ ^ 2 + B₂ ^ 2) := by
    rw [hBB, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hab hXY.le) (by positivity)
  have h5 : 0 < (σ ^ 2 * m ^ 2 - 4 * K ^ 2 - 2 * σ * D) * (X ^ 2 + Y ^ 2) :=
    mul_pos (by linarith) hXY
  have key : 0 < σ * (2 * (u₁ * B₁ + u₂ * B₂) + 2 * σ * (B₁ ^ 2 + B₂ ^ 2) +
      (-b' * X ^ 2 + 2 * a' * X * Y + b' * Y ^ 2)) := by
    linarith [mul_le_mul_of_nonneg_left hP3 hσ.le]
  exact (pos_iff_pos_of_mul_pos key).1 hσ

/-- For a pointwise symmetric `T` with entries bounded by `K` and a `C¹` loop `γ` with
`m ≤ |γ|` and `|γ'| ≤ D`, the loop `T + σ · antilinearMat γ` is nondegenerate whenever
`4K² + 2σD < σ²m²`. -/
theorem isNondegenerate_add_smul_antilinearMat_aux (T : ℝ → Mat 1) (hT : ∀ t, (T t).IsSymm)
    (K : ℝ) (hK : ∀ t i j, |T t i j| ≤ K) (γ γ' : ℝ → ℂ) (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hper : Function.Periodic γ 1) (m D : ℝ) (hm0 : 0 ≤ m) (hm : ∀ t, m ≤ ‖γ t‖)
    (hD : ∀ t, ‖γ' t‖ ≤ D) (σ : ℝ) (hσ : 0 < σ)
    (hbig : 4 * K ^ 2 + 2 * σ * D < σ ^ 2 * m ^ 2) :
    IsNondegenerate (fun t => T t + σ • antilinearMat (γ t)) := by
  intro Ψ hΨ hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hv1 : Ψ 1 *ᵥ v = v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv.symm
  set M : ℝ → Mat 1 := fun t => T t + σ • antilinearMat (γ t) with hMdef
  have hMs : ∀ t, (M t).IsSymm := fun t => (hT t).add ((antilinearMat_isSymm _).smul σ)
  -- η t ≠ 0
  have hne : ∀ t, Ψ t *ᵥ v ≠ 0 := by
    intro t h0
    have hs := fundamentalSolution_symplectic 1 M hMs Ψ hΨ t
    have hd : (Ψ t).det ≠ 0 :=
      (SymplecticGroup.symplectic_det hs).ne_zero
    exact hv0 (Matrix.eq_zero_of_mulVec_eq_zero hd h0)
  set i₁ : Fin 1 ⊕ Fin 1 := Sum.inl 0
  set i₂ : Fin 1 ⊕ Fin 1 := Sum.inr 0
  let x : ℝ → ℝ := fun t => (Ψ t *ᵥ v) i₁
  let y : ℝ → ℝ := fun t => (Ψ t *ᵥ v) i₂
  -- the derivative of η
  have hη : ∀ t, HasDerivAt (fun t => Ψ t *ᵥ v) ((J₀ 1 * M t) *ᵥ (Ψ t *ᵥ v)) t := by
    intro t
    have := crw_hasDerivAt_mulVec Ψ _ t (hΨ.2 t) v
    rwa [← Matrix.mulVec_mulVec] at this
  have hcomp : ∀ (u : Fin 1 ⊕ Fin 1 → ℝ) (t : ℝ),
      ((J₀ 1 * M t) *ᵥ u) i₁ = -(T t i₂ i₁ * u i₁ + T t i₂ i₂ * u i₂ +
        σ * ((γ t).im * u i₁ - (γ t).re * u i₂)) ∧
      ((J₀ 1 * M t) *ᵥ u) i₂ = T t i₁ i₁ * u i₁ + T t i₁ i₂ * u i₂ +
        σ * ((γ t).re * u i₁ + (γ t).im * u i₂) := by
    intro u t
    simp only [hMdef, i₁, i₂, J₀, Matrix.J, antilinearMat, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton, Matrix.mul_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, smul_eq_mul,
      Matrix.zero_apply, Matrix.one_apply_eq, Matrix.neg_apply, Fin.default_eq_zero]
    constructor <;> ring
  have hx : ∀ t, HasDerivAt x (((J₀ 1 * M t) *ᵥ (Ψ t *ᵥ v)) i₁) t := fun t =>
    hasDerivAt_pi.1 (hη t) i₁
  have hy : ∀ t, HasDerivAt y (((J₀ 1 * M t) *ᵥ (Ψ t *ᵥ v)) i₂) t := fun t =>
    hasDerivAt_pi.1 (hη t) i₂
  have hre : ∀ t, HasDerivAt (fun t => (γ t).re) (γ' t).re t := fun t =>
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hγ t)
  have him : ∀ t, HasDerivAt (fun t => (γ t).im) (γ' t).im t := fun t =>
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hγ t)
  let q : ℝ → ℝ := fun t =>
    -(γ t).im * (x t * x t) + 2 * (γ t).re * x t * y t + (γ t).im * (y t * y t)
  have hq : ∀ t, ∃ q', HasDerivAt q q' t ∧ 0 < q' := by
    intro t
    have hd := ((((him t).neg.mul ((hx t).mul (hx t))).add
      ((((hre t).const_mul 2).mul (hx t)).mul (hy t))).add ((him t).mul ((hy t).mul (hy t))))
    refine ⟨_, hd, ?_⟩
    obtain ⟨e1, e2⟩ := hcomp (Ψ t *ᵥ v) t
    rw [e1, e2]
    have hXY : 0 < x t ^ 2 + y t ^ 2 := by
      by_contra hc
      push_neg at hc
      have hX : x t = 0 := by nlinarith [sq_nonneg (x t), sq_nonneg (y t)]
      have hY : y t = 0 := by nlinarith [sq_nonneg (x t), sq_nonneg (y t)]
      apply hne t
      funext i
      rcases i with i | i <;> fin_cases i
      · exact hX
      · exact hY
    have hab : m ^ 2 ≤ (γ t).re ^ 2 + (γ t).im ^ 2 := by
      have h1 : ‖γ t‖ ^ 2 = (γ t).re ^ 2 + (γ t).im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [← h1]
      exact pow_le_pow_left₀ hm0 (hm t) 2
    have h := crw_alg (γ t).re (γ t).im (γ' t).re (γ' t).im (x t) (y t) (T t i₁ i₁) (T t i₁ i₂)
      (T t i₂ i₁) (T t i₂ i₂) K m D σ hσ (hK t _ _) (hK t _ _) (hK t _ _) (hK t _ _) hab
      ((Complex.abs_re_le_norm _).trans (hD t)) ((Complex.abs_im_le_norm _).trans (hD t)) hXY hbig
    simp only [x, y, Pi.mul_apply, Pi.neg_apply] at h ⊢
    convert h using 1
    ring
  -- strict monotonicity contradicts periodicity
  choose q' hq' hpos using hq
  have hmono : StrictMono q := strictMono_of_deriv_pos fun t => by
    rw [(hq' t).deriv]; exact hpos t
  have h01 : q 0 < q 1 := hmono zero_lt_one
  have hγ1 : γ 1 = γ 0 := by simpa using hper 0
  have hη1 : Ψ 1 *ᵥ v = Ψ 0 *ᵥ v := by rw [hv1, hΨ.1, Matrix.one_mulVec]
  have : q 1 = q 0 := by simp only [q, x, y, hγ1, hη1]
  linarith

end

end CauchyRiemannIndex

open CauchyRiemannIndex

open Matrix

theorem solution (T : ℝ → Mat 1) (hT : ∀ t, (T t).IsSymm)
    (K : ℝ) (hK : ∀ t i j, |T t i j| ≤ K) (γ γ' : ℝ → ℂ) (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hper : Function.Periodic γ 1) (m D : ℝ) (hm0 : 0 ≤ m) (hm : ∀ t, m ≤ ‖γ t‖)
    (hD : ∀ t, ‖γ' t‖ ≤ D) (σ : ℝ) (hσ : 0 < σ)
    (hbig : 4 * K ^ 2 + 2 * σ * D < σ ^ 2 * m ^ 2) :
    IsNondegenerate (fun t => T t + σ • antilinearMat (γ t)) :=
  CauchyRiemannIndex.isNondegenerate_add_smul_antilinearMat_aux T hT K hK γ γ' hγ hper m D hm0 hm hD σ hσ hbig
