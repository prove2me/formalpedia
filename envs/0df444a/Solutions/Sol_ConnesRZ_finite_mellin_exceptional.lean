-- Prove2me | solution 1 for ConnesRZ.finite_mellin_exceptional
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-06T21:16:50.276481+00:00
-- url     : https://prove2.me/submissions/43e6a226-854a-4278-bb4e-5770fdfd9f9c

import Definitions.Def_ConnesRZ_weil_defs

open Complex MeasureTheory

noncomputable section
namespace ConnesRZInterpolation

open ConnesRZ

def testSpace : Submodule ℂ (ℝ → ℂ) where
  carrier := {g | IsTest g}
  zero_mem' := ⟨contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  add_mem' := fun hg hh => ⟨hg.1.add hh.1, hg.2.add hh.2⟩
  smul_mem' := fun c g hg => ⟨hg.1.const_smul c, by
    change HasCompactSupport (fun t => c * g t)
    exact hg.2.mul_left⟩

lemma weighted_integrable (g : ℝ → ℂ) (hg : IsTest g) (z : ℂ) :
    Integrable (fun t : ℝ => g t * Complex.exp ((z - 1 / 2) * t)) := by
  have hc : Continuous (fun t : ℝ => g t * Complex.exp ((z - 1 / 2) * t)) := by
    exact hg.1.continuous.mul (Complex.continuous_exp.comp (by fun_prop))
  exact hc.integrable_of_hasCompactSupport hg.2.mul_right

lemma mellin_add (g h : ℝ → ℂ) (hg : IsTest g) (hh : IsTest h) (z : ℂ) :
    mellinHat (g + h) z = mellinHat g z + mellinHat h z := by
  unfold mellinHat
  simp only [Pi.add_apply, add_mul]
  exact integral_add (weighted_integrable g hg z) (weighted_integrable h hh z)

lemma mellin_smul (c : ℂ) (g : ℝ → ℂ) (z : ℂ) :
    mellinHat (c • g) z = c * mellinHat g z := by
  simp only [mellinHat, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

def mellinEval (z : ℂ) : testSpace →ₗ[ℂ] ℂ where
  toFun g := mellinHat g.1 z
  map_add' g h := mellin_add g.1 h.1 g.2 h.2 z
  map_smul' c g := by simpa [smul_eq_mul] using mellin_smul c g.1 z

lemma isTest_deriv (g : ℝ → ℂ) (hg : IsTest g) : IsTest (deriv g) :=
  ⟨(contDiff_infty_iff_deriv.mp hg.1).2, hg.2.deriv⟩

lemma mellin_deriv (g : ℝ → ℂ) (hg : IsTest g) (z : ℂ) :
    mellinHat (deriv g) z = -(z - 1 / 2) * mellinHat g z := by
  let k := z - 1 / 2
  have hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => Complex.exp (k * u))
      (k * Complex.exp (k * t)) t := by
    intro t
    have h := hasDerivAt_exp_smul_const' (𝕂 := ℂ) (𝔸 := ℂ) k (t : ℂ)
    simpa [← Complex.exp_eq_exp_ℂ, smul_eq_mul, mul_comm] using h.comp_ofReal
  have hgd : ∀ t : ℝ, HasDerivAt g (deriv g t) t := fun t =>
    (hg.1.differentiable (by simp)).differentiableAt.hasDerivAt
  have hi : Integrable (fun t : ℝ =>
      deriv g t * Complex.exp (k * t) + k * (g t * Complex.exp (k * t))) :=
    (weighted_integrable (deriv g) (isTest_deriv g hg) z).add
      ((weighted_integrable g hg z).const_mul k)
  have hz : (∫ t : ℝ, deriv g t * Complex.exp (k * t) +
      k * (g t * Complex.exp (k * t))) = 0 := by
    apply integral_eq_zero_of_hasDerivAt_of_integrable ?_ hi (weighted_integrable g hg z)
    intro t
    convert (hgd t).mul (hd t) using 1 <;> first | rfl | ring
  rw [integral_add (weighted_integrable (deriv g) (isTest_deriv g hg) z)
    ((weighted_integrable g hg z).const_mul k), integral_const_mul] at hz
  change mellinHat (deriv g) z + k * mellinHat g z = 0 at hz
  change mellinHat (deriv g) z = -k * mellinHat g z
  linear_combination hz

end ConnesRZInterpolation


open Complex MeasureTheory ConnesRZ ConnesRZInterpolation

noncomputable section
namespace ConnesRZDecay

def envelope (g : ℝ → ℂ) (t : ℝ) : ℝ := ‖g t‖ * Real.exp (|t| / 2)
def envelopeMass (g : ℝ → ℂ) : ℝ := ∫ t : ℝ, envelope g t

lemma envelope_integrable (g : ℝ → ℂ) (hg : IsTest g) : Integrable (envelope g) := by
  have hc : Continuous (envelope g) := hg.1.continuous.norm.mul (by fun_prop)
  exact hc.integrable_of_hasCompactSupport hg.2.norm.mul_right

lemma envelopeMass_nonneg (g : ℝ → ℂ) : 0 ≤ envelopeMass g := by
  apply integral_nonneg
  intro t
  exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

lemma kernel_bound (z : ℂ) (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) (t : ℝ) :
    ‖Complex.exp ((z - 1 / 2) * t)‖ ≤ Real.exp (|t| / 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  norm_num
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    nlinarith
  · rw [abs_of_neg (lt_of_not_ge ht)]
    nlinarith

lemma mellin_bound (g : ℝ → ℂ) (hg : IsTest g) (z : ℂ)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) : ‖mellinHat g z‖ ≤ envelopeMass g := by
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono (weighted_integrable g hg z).norm (envelope_integrable g hg)
  intro t
  change ‖g t * Complex.exp ((z - 1 / 2) * t)‖ ≤ ‖g t‖ * Real.exp (|t| / 2)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (kernel_bound z hz0 hz1 t) (norm_nonneg _)

lemma strip_decay (g : ℝ → ℂ) (hg : IsTest g) (z : ℂ)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    |z.im| * ‖mellinHat g z‖ ≤ envelopeMass (deriv g) := by
  have hb := mellin_bound (deriv g) (isTest_deriv g hg) z hz0 hz1
  rw [mellin_deriv g hg z, norm_mul, norm_neg] at hb
  have hi : |z.im| ≤ ‖z - 1 / 2‖ := by
    simpa using Complex.abs_im_le_norm (z - 1 / 2)
  exact (mul_le_mul_of_nonneg_right hi (norm_nonneg _)).trans hb

end ConnesRZDecay

open Set in
/-- Only finitely many critical zeros can have a transform value above a fixed
positive threshold. This is the exceptional-set step in Burnol's argument. -/
theorem solution (g : ℝ → ℂ) (hg : IsTest g)
    (ε : ℝ) (hε : 0 < ε) :
    {z : ℂ | IsCriticalZero z ∧ ε ≤ ‖mellinHat g z‖}.Finite := by
  let B : ℝ := ConnesRZDecay.envelopeMass (deriv g) / ε
  let K : Set ℂ := (Icc 0 1) ×ℂ (Icc (-B) B)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  apply hK.inter_riemannZetaZeros_finite.subset
  rintro z ⟨hz, he⟩
  have hd := ConnesRZDecay.strip_decay g hg z hz.2.1.le hz.2.2.le
  have hi : |z.im| ≤ B := by
    apply (le_div_iff₀ hε).mpr
    exact (mul_le_mul_of_nonneg_left he (abs_nonneg _)).trans hd
  refine ⟨⟨⟨hz.2.1.le, hz.2.2.le⟩, (abs_le.mp hi)⟩, hz.1⟩
