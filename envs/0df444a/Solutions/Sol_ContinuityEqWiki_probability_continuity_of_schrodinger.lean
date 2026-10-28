-- Prove2me | solution 1 for ContinuityEqWiki.probability_continuity_of_schrodinger
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:21:41.676193+00:00
-- url     : https://prove2.me/submissions/5c6e1759-c6b0-4b20-8b45-7570fbc7997d

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

open ContinuityEqWiki

namespace LUHelpSch

theorem diff_dirC (f : Space → ℂ) (hf : ContDiff ℝ 2 f) (b : Space) :
    Differentiable ℝ (fun y => fderiv ℝ f y b) := fun y =>
  (((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) y).clm_apply
    (differentiableAt_const b)

theorem pd_conj (f : Space → ℂ) (hf : Differentiable ℝ f) (k : Fin 3) (y : Space) :
    partialDeriv k (fun z => (starRingEnd ℂ) (f z)) y = (starRingEnd ℂ) (partialDeriv k f y) := by
  have h : HasFDerivAt (⇑Complex.conjCLE ∘ f)
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f y)) y :=
    Complex.conjCLE.hasFDerivAt.comp y (hf y).hasFDerivAt
  unfold partialDeriv
  rw [show (fun z => (starRingEnd ℂ) (f z)) = ⇑Complex.conjCLE ∘ f from rfl, h.fderiv]
  rfl

theorem current_eq (hbar m : ℝ) (hm : m ≠ 0) (a : ℂ) :
    ((hbar : ℂ) / (2 * (m : ℂ) * Complex.I) * (a - (starRingEnd ℂ) a)).re = hbar / m * a.im := by
  rw [Complex.sub_conj]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hm' : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm
  have : (hbar : ℂ) / (2 * (m : ℂ) * Complex.I) * (((2 * a.im : ℝ) : ℂ) * Complex.I) =
      ((hbar / m * a.im : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [this, Complex.ofReal_re]

end LUHelpSch

open LUHelpSch in
theorem solution (hbar m : ℝ) (hhbar : 0 < hbar) (hm : 0 < m)
    (U : ℝ → Space → ℝ) (Ψ : ℝ → Space → ℂ) (hΨ : ContDiff ℝ 2 (Function.uncurry Ψ))
    (hS : SchrodingerEq hbar m U Ψ) :
    ∀ t x, div (probCurrent hbar m Ψ t) x + timeDeriv (probDensity Ψ) t x = 0 := by
  intro t x
  set ψ := Ψ t with hψdef
  have hψ : ContDiff ℝ 2 ψ :=
    hΨ.comp ((contDiff_const (c := t)).prodMk contDiff_id)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  -- current in terms of Im
  have hj : ∀ k, (fun y => probCurrent hbar m Ψ t y k) =
      fun y => hbar / m * ((starRingEnd ℂ) (ψ y) * partialDeriv k ψ y).im := by
    intro k
    funext y
    unfold probCurrent
    rw [pd_conj ψ hψd k y]
    have : ψ y * (starRingEnd ℂ) (partialDeriv k ψ y) =
        (starRingEnd ℂ) ((starRingEnd ℂ) (ψ y) * partialDeriv k ψ y) := by
      simp [map_mul]
    rw [← hψdef, this, current_eq hbar m hm.ne']
  -- derivative of each current component
  have hdj : ∀ k, partialDeriv k (fun y => probCurrent hbar m Ψ t y k) x =
      hbar / m * ((starRingEnd ℂ) (ψ x) *
        partialDeriv k (fun y => partialDeriv k ψ y) x).im := by
    intro k
    rw [hj k]
    have hc : HasFDerivAt (fun y => (starRingEnd ℂ) (ψ y))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ ψ x)) x :=
      Complex.conjCLE.hasFDerivAt.comp x (hψd x).hasFDerivAt
    have hd : HasFDerivAt (fun y => partialDeriv k ψ y)
        (fderiv ℝ (fun y => partialDeriv k ψ y) x) x :=
      (diff_dirC ψ hψ _ x).hasFDerivAt
    have hp := hc.mul hd
    have hi := (Complex.imCLM.hasFDerivAt).comp x hp
    have hf := hi.const_mul (hbar / m)
    unfold partialDeriv at hf ⊢
    rw [show (fun y => hbar / m * ((starRingEnd ℂ) (ψ y) * fderiv ℝ ψ y (Pi.single k 1)).im) =
      fun y => hbar / m * (⇑Complex.imCLM ∘ ((fun y => (starRingEnd ℂ) (ψ y)) *
        fun y => fderiv ℝ ψ y (Pi.single k 1))) y from rfl, hf.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, smul_eq_mul, Complex.imCLM_apply, Pi.mul_apply]
    congr 1
    simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hdiv : div (probCurrent hbar m Ψ t) x =
      hbar / m * ((starRingEnd ℂ) (ψ x) * laplacian ψ x).im := by
    unfold div laplacian
    simp_rw [hdj]
    rw [Finset.mul_sum, Complex.im_sum, Finset.mul_sum]
  -- time derivative of density
  set φ' := timeDeriv Ψ t x with hφ'
  have hφ : HasDerivAt (fun s => Ψ s x) φ' t := by
    have h1 : DifferentiableAt ℝ (Function.uncurry Ψ ∘ fun s => (s, x)) t :=
      ((hΨ.differentiable (by norm_num)) _).comp t
        ((differentiableAt_id).prodMk (differentiableAt_const x))
    exact h1.hasDerivAt
  have hρ : timeDeriv (probDensity Ψ) t x =
      ((starRingEnd ℂ) φ' * ψ x + (starRingEnd ℂ) (ψ x) * φ').re := by
    have h1 := hφ.star
    have h2 := h1.mul hφ
    have h3 := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt t h2
    unfold timeDeriv probDensity
    have : (fun s => Complex.normSq (Ψ s x)) =
        ⇑Complex.reCLM ∘ ((fun s => star (Ψ s x)) * fun s => Ψ s x) := by
      funext s
      simp [Complex.normSq_apply, Complex.mul_re]
    rw [this, h3.deriv]
    simp [hψdef]
  -- Schrödinger, split into real and imaginary parts
  have hSx := hS t x
  rw [← hφ'] at hSx
  have hc : (hbar : ℂ) ^ 2 / (2 * (m : ℂ)) = ((hbar ^ 2 / (2 * m) : ℝ) : ℂ) := by push_cast; ring
  rw [hc, ← hψdef] at hSx
  have hre := congrArg Complex.re hSx
  have him := congrArg Complex.im hSx
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
    Complex.neg_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im] at hre him
  rw [hdiv, hρ]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.add_re]
  have hh : hbar ≠ 0 := hhbar.ne'
  have hmm : m ≠ 0 := hm.ne'
  refine (mul_eq_zero.1 ?_).resolve_left hh
  linear_combination (-2 * (ψ x).re) * him + (2 * (ψ x).im) * hre
