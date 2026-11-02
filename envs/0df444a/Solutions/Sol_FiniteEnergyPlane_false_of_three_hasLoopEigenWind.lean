-- Prove2me | solution 1 for FiniteEnergyPlane.false_of_three_hasLoopEigenWind
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T21:57:16.60492+00:00
-- url     : https://prove2.me/submissions/28629087-8ee1-433e-9988-99934efba7d7

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_isLoopEigen_apply_ne_zero
import Theorems.Thm_FiniteEnergyPlane_loopEigen_apply_ne_smul_of_hasLoopEigenWind
import Theorems.Thm_FiniteEnergyPlane_hasDerivAt_im_conj_mul_of_eigenEq
import Theorems.Thm_FiniteEnergyPlane_exists_eigenEq_solution
import Theorems.Thm_FiniteEnergyPlane_mul_im_conj_pos_of_eigenEq
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul



namespace FiniteEnergyPlane

open scoped ContDiff

theorem false_of_three_hasLoopEigenWind_aux (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) {μ₁ μ₂ μ₃ : ℝ} {k : ℤ}
    (h₁₂ : μ₁ < μ₂) (h₂₃ : μ₂ < μ₃) (h₁ : HasLoopEigenWind Sinf μ₁ k)
    (h₂ : HasLoopEigenWind Sinf μ₂ k) (h₃ : HasLoopEigenWind Sinf μ₃ k) : False := by
  have hS : ∀ t, (Sinf t).IsSymm := hSinf.2.2
  obtain ⟨e₁, he₁⟩ := h₁.1
  obtain ⟨e₂, he₂⟩ := h₂.1
  obtain ⟨e₃, he₃⟩ := h₃.1
  have dif : ∀ {μ : ℝ} {e : ℝ → CauchyRiemannIndex.Vec 1}, IsLoopEigen Sinf μ e →
      Differentiable ℝ e := fun he => he.1.differentiable (by simp)
  have per : ∀ {μ : ℝ} {e : ℝ → CauchyRiemannIndex.Vec 1}, IsLoopEigen Sinf μ e →
      e 1 = e 0 := fun he => by simpa using he.2.1 0
  have vlin : ∀ (a b : ℝ) (v w : CauchyRiemannIndex.Vec 1),
      vecToC (a • v + b • w) = (a : ℂ) * vecToC v + (b : ℂ) * vecToC w := by
    intro a b v w
    apply Complex.ext <;> simp [vecToC]
  -- values of `e₂` are never real multiples of those of `e₁`, `e₃`
  have npar : ∀ {μ : ℝ} {e : ℝ → CauchyRiemannIndex.Vec 1}, IsLoopEigen Sinf μ e →
      μ ≠ μ₂ → HasLoopEigenWind Sinf μ k → ∀ t,
        (starRingEnd ℂ (vecToC (e₂ t)) * vecToC (e t)).im ≠ 0 := by
    intro μ e he hμ hk t h0
    have hne := isLoopEigen_apply_ne_zero Sinf hSinf.1 μ₂ e₂ he₂ t
    set c : ℝ := (starRingEnd ℂ (vecToC (e₂ t)) * vecToC (e t)).re /
      Complex.normSq (vecToC (e₂ t)) with hc
    apply loopEigen_apply_ne_smul_of_hasLoopEigenWind Sinf hSinf hSinf' (Ne.symm hμ) h₂ hk
      he₂ he t c
    have hn : Complex.normSq (vecToC (e₂ t)) ≠ 0 := by
      rw [Complex.normSq_eq_zero.ne]
      intro h
      apply hne
      ext i
      rcases i with i | i <;> fin_cases i
      · simpa [vecToC] using congrArg Complex.re h
      · simpa [vecToC] using congrArg Complex.im h
    simp only [vecToC, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply] at h0 hn hc
    ext i
    rcases i with i | i <;> obtain rfl : i = 0 := Subsingleton.elim _ _
    · show e t (Sum.inl 0) = c * e₂ t (Sum.inl 0)
      rw [hc, div_mul_eq_mul_div, eq_div_iff hn]
      linear_combination (-(e₂ t (Sum.inr 0))) * h0
    · show e t (Sum.inr 0) = c * e₂ t (Sum.inr 0)
      rw [hc, div_mul_eq_mul_div, eq_div_iff hn]
      linear_combination (e₂ t (Sum.inl 0)) * h0
  have np₁ := npar he₁ h₁₂.ne h₁
  have np₃ := npar he₃ h₂₃.ne' h₃
  -- the solution `x₁` for `μ₂` starting at `e₁ 0`
  obtain ⟨x₁, hx₁0, hx₁, hx₁e⟩ := exists_eigenEq_solution Sinf hSinf.1 μ₂ (e₁ 0)
  have G₁ := mul_im_conj_pos_of_eigenEq Sinf hS h₁₂.ne (dif he₁) he₁.2.2.2 (dif he₂) he₂.2.2.2
    hx₁ hx₁e hx₁0 (fun t _ => np₁ t)
  -- `e₃ 0 = a • e₂ 0 + b • e₁ 0`
  set u := vecToC (e₂ 0) with hu
  set v₁ := vecToC (e₁ 0) with hv₁
  set v₃ := vecToC (e₃ 0) with hv₃
  set D := (starRingEnd ℂ u * v₁).im with hD
  have hD0 : D ≠ 0 := np₁ 0
  set a : ℝ := (starRingEnd ℂ v₃ * v₁).im / D with ha
  set b : ℝ := (starRingEnd ℂ u * v₃).im / D with hb
  have hdec : e₃ 0 = a • e₂ 0 + b • e₁ 0 := by
    simp only [hu, hv₁, hv₃, hD, vecToC, Complex.mul_im, Complex.conj_re,
      Complex.conj_im] at ha hb hD0
    ext i
    rcases i with i | i <;> obtain rfl : i = 0 := Subsingleton.elim _ _
    · show e₃ 0 (Sum.inl 0) = a * e₂ 0 (Sum.inl 0) + b * e₁ 0 (Sum.inl 0)
      rw [ha, hb, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD0]
      ring
    · show e₃ 0 (Sum.inr 0) = a * e₂ 0 (Sum.inr 0) + b * e₁ 0 (Sum.inr 0)
      rw [ha, hb, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD0]
      ring
  -- the solution `x₃ = a e₂ + b x₁` for `μ₂` starting at `e₃ 0`
  set x₃ : ℝ → CauchyRiemannIndex.Vec 1 := fun t => a • e₂ t + b • x₁ t with hx₃
  have hx₃d : Differentiable ℝ x₃ := ((dif he₂).const_smul a).add (hx₁.const_smul b)
  have hx₃e : ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv x₃ t)) -
      Matrix.toEuclideanLin (Sinf t) (x₃ t) = μ₂ • x₃ t := by
    intro t
    have hd : HasDerivAt x₃ (a • deriv e₂ t + b • deriv x₁ t) t :=
      (((dif he₂) t).hasDerivAt.const_smul a).add ((hx₁ t).hasDerivAt.const_smul b)
    rw [hd.deriv]
    simp only [hx₃, map_add, map_smul]
    have h1 := he₂.2.2.2 t
    have h2 := hx₁e t
    linear_combination (norm := module) a • h1 + b • h2
  have hx₃0 : x₃ 0 = e₃ 0 := by
    show a • e₂ 0 + b • x₁ 0 = e₃ 0
    rw [hdec, hx₁0]
  have G₃ := mul_im_conj_pos_of_eigenEq Sinf hS h₂₃.ne' (dif he₃) he₃.2.2.2 (dif he₂)
    he₂.2.2.2 hx₃d hx₃e hx₃0 (fun t _ => np₃ t)
  -- the cross term of `e₂` and `x₁` is constant
  have hWd := fun t => hasDerivAt_im_conj_mul_of_eigenEq Sinf hS (dif he₂) he₂.2.2.2 hx₁ hx₁e t
  have hW : (starRingEnd ℂ (vecToC (e₂ 1)) * vecToC (x₁ 1)).im = D := by
    have h := is_const_of_deriv_eq_zero (fun s => (hWd s).differentiableAt)
      (fun s => by rw [(hWd s).deriv]; ring) 1 0
    rw [h, hx₁0]
  -- the cross term for `e₃, x₃` at `1` is `b²` times that for `e₁, x₁`
  have hrel : (starRingEnd ℂ (vecToC (e₃ 1)) * vecToC (x₃ 1)).im =
      b ^ 2 * (starRingEnd ℂ (vecToC (e₁ 1)) * vecToC (x₁ 1)).im := by
    rw [per he₃, hdec, per he₁]
    simp only [hx₃]
    rw [vlin, vlin, per he₂]
    rw [per he₂] at hW
    set y := vecToC (x₁ 1)
    rw [← hu, ← hv₁]
    rw [← hu] at hW
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, map_add, map_mul,
      Complex.conj_ofReal] at hW hD ⊢
    rw [← hW] at hD
    linear_combination (a * b) * hD
  rw [hrel, per he₁] at G₃
  rw [per he₁] at G₁
  have hpos : 0 < (starRingEnd ℂ (vecToC (e₁ 0)) * vecToC (x₁ 1)).im :=
    pos_of_mul_pos_right G₁ (sub_pos.2 h₁₂).le
  have : (μ₂ - μ₃) * (b ^ 2 * (starRingEnd ℂ (vecToC (e₁ 0)) * vecToC (x₁ 1)).im) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_neg.2 h₂₃).le (by positivity)
  linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open scoped ContDiff

theorem solution (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) {μ₁ μ₂ μ₃ : ℝ} {k : ℤ}
    (h₁₂ : μ₁ < μ₂) (h₂₃ : μ₂ < μ₃) (h₁ : HasLoopEigenWind Sinf μ₁ k)
    (h₂ : HasLoopEigenWind Sinf μ₂ k) (h₃ : HasLoopEigenWind Sinf μ₃ k) : False :=
  false_of_three_hasLoopEigenWind_aux Sinf hSinf hSinf' h₁₂ h₂₃ h₁ h₂ h₃
