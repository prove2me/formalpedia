-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_gradient_frame_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T19:38:20.099042+00:00
-- url     : https://prove2.me/submissions/c6bf2933-1e3a-47a1-90f7-447ebf449223

import Definitions.Def_BirkhoffGlobalSection_CanonicalPositiveFrame
import Definitions.Def_BirkhoffGlobalSection_MovingFrameAlgebra
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Tactic


namespace HryniewiczCriterion.FrameTransition
open HryniewiczCriterion

noncomputable def rawContactFrame (g x : R4) : Fin 2 → R4 :=
  ![quatQ2 x - (dot4 g (quatQ2 x) / dot4 g x) • x,
    quatQ1 x - (dot4 g (quatQ1 x) / dot4 g x) • x]

noncomputable def gradientCoordinates (g w : R4) : Fin 2 → ℝ :=
  ![-dot4 (quatQ1 g) w, dot4 (quatQ2 g) w]

/-- The gradient/contact transition has positive angular cross product. -/
lemma transition_cross_identity (g x : R4) (z : Fin 2 → ℝ) (hr : dot4 g x ≠ 0) :
    dot4 g x *
      (z 0 * gradientCoordinates g (z 0 • rawContactFrame g x 0 + z 1 • rawContactFrame g x 1) 1 -
       z 1 * gradientCoordinates g (z 0 • rawContactFrame g x 0 + z 1 • rawContactFrame g x 1) 0) =
    (dot4 g x) ^ 2 * ((z 0) ^ 2 + (z 1) ^ 2) +
      (dot4 g (quatQ2 x) * z 0 + dot4 g (quatQ1 x) * z 1) ^ 2 := by
  simp only [gradientCoordinates, rawContactFrame, dot4, Fin.sum_univ_four, quatQ1, quatQ2,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [dot4, Fin.sum_univ_four] at hr
  field_simp
  <;> ring

lemma transition_cross_pos (g x : R4) (z : Fin 2 → ℝ)
    (hr : 0 < dot4 g x) (hz : z ≠ 0) :
    0 < z 0 * gradientCoordinates g (z 0 • rawContactFrame g x 0 + z 1 • rawContactFrame g x 1) 1 -
       z 1 * gradientCoordinates g (z 0 • rawContactFrame g x 0 + z 1 • rawContactFrame g x 1) 0 := by
  have hzz : 0 < (z 0) ^ 2 + (z 1) ^ 2 := by
    by_contra h
    have h0 : z 0 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
    have h1 : z 1 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
    apply hz
    ext i; fin_cases i <;> assumption
  have hp : 0 < (dot4 g x) ^ 2 * ((z 0) ^ 2 + (z 1) ^ 2) +
      (dot4 g (quatQ2 x) * z 0 + dot4 g (quatQ1 x) * z 1) ^ 2 :=
    add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_pos hr) hzz) (sq_nonneg _)
  rw [← transition_cross_identity g x z hr.ne'] at hp
  exact pos_of_mul_pos_right hp hr.le

end HryniewiczCriterion.FrameTransition

-- Generic Hamiltonian/frame matrix calculations adapted with credit to Mazecto,
-- accepted homogeneous_frame_flow_split and submission 893234ef-5ec2-4f4b-b415-f79ec1030002.
-- The C2 local completion and projected-flow assembly are derived for this contribution.

namespace HryniewiczCriterion.CanonicalMatrix
open HryniewiczCriterion Matrix

def col (F : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) : R4 := fun k => F k i

lemma transpose_omega_mul_apply (F : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    (F.transpose * omegaMat * F) i j = omega0 (col F i) (col F j) := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, omegaMat, omega0, col]; ring

lemma inverse_identities (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : F.transpose * omegaMat * F = omegaMat) :
    F⁻¹ * F = 1 ∧ F * F⁻¹ = 1 ∧ F⁻¹ * symplJ4 = symplJ4 * F.transpose := by
  have hJΩ : symplJ4 * omegaMat = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [symplJ4, omegaMat, Matrix.mul_apply, Fin.sum_univ_four]
  have hΩJ : omegaMat * symplJ4 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [symplJ4, omegaMat, Matrix.mul_apply, Fin.sum_univ_four]
  let G := symplJ4 * F.transpose * omegaMat
  have hGF : G * F = 1 := by
    dsimp [G]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc F.transpose, hF, hJΩ]
  have hInv : F⁻¹ = G := Matrix.inv_eq_left_inv hGF
  refine ⟨by rw [hInv, hGF], ?_, ?_⟩
  · rw [hInv]; exact mul_eq_one_comm.mp hGF
  · rw [hInv]
    dsimp [G]
    rw [Matrix.mul_assoc, hΩJ, Matrix.mul_one]

lemma omega0_lin_right (u a b c d : R4) (p q r s : ℝ) :
    omega0 u (p • a + q • b + r • c + s • d) =
      p * omega0 u a + q * omega0 u b + r * omega0 u c + s * omega0 u d := by
  simp [omega0]; ring

lemma mulVec_eq_cols (F : Matrix (Fin 4) (Fin 4) ℝ) (c : R4) :
    F.mulVec c = c 0 • col F 0 + c 1 • col F 1 + c 2 • col F 2 + c 3 • col F 3 := by
  ext i; simp [mulVec, dotProduct, Fin.sum_univ_four, col]; ring

lemma frame_coordinates_pairing (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : F.transpose * omegaMat * F = omegaMat) (v : R4) :
    omega0 (col F 0) v = (F⁻¹.mulVec v) 1 ∧
      omega0 (col F 1) v = -(F⁻¹.mulVec v) 0 := by
  let c := F⁻¹.mulVec v
  have hc : F.mulVec c = v := by
    dsimp [c]
    rw [Matrix.mulVec_mulVec, (inverse_identities F hF).2.1, Matrix.one_mulVec]
  have hp : ∀ i j, omega0 (col F i) (col F j) = omegaMat i j := by
    intro i j
    rw [← transpose_omega_mul_apply, hF]
  have h0 : omega0 (col F 0) v = c 1 := by
    calc _ = omega0 (col F 0) (F.mulVec c) := congrArg (omega0 (col F 0)) hc.symm
         _ = c 1 := by rw [mulVec_eq_cols, omega0_lin_right]; simp [hp, omegaMat]
  have h1 : omega0 (col F 1) v = -c 0 := by
    calc _ = omega0 (col F 1) (F.mulVec c) := congrArg (omega0 (col F 1)) hc.symm
         _ = -c 0 := by rw [mulVec_eq_cols, omega0_lin_right]; simp [hp, omegaMat]
  exact ⟨h0, h1⟩

lemma reconstruct_transverse (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : F.transpose * omegaMat * F = omegaMat) (v : R4)
    (h0 : omega0 (col F 0) v = 0) (h1 : omega0 (col F 1) v = 0) :
    v = (F⁻¹.mulVec v) 2 • col F 2 + (F⁻¹.mulVec v) 3 • col F 3 := by
  have hp := frame_coordinates_pairing F hF v
  have hc0 : (F⁻¹.mulVec v) 0 = 0 := by linarith [hp.2]
  have hc1 : (F⁻¹.mulVec v) 1 = 0 := by linarith [hp.1]
  have hc : F.mulVec (F⁻¹.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, (inverse_identities F hF).2.1, Matrix.one_mulVec]
  rw [mulVec_eq_cols, hc0, hc1] at hc
  simpa using hc.symm

lemma inverse_mulVec_col (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : F.transpose * omegaMat * F = omegaMat) (j : Fin 4) :
    F⁻¹.mulVec (col F j) = Pi.single j 1 := by
  change col (F⁻¹ * F) j = _
  rw [(inverse_identities F hF).1]
  ext i; simp [col, Matrix.one_apply, Pi.single_apply, eq_comm]

lemma omega0_sub_smul_right (u v w : R4) (a : ℝ) :
    omega0 u (v - a • w) = omega0 u v - a * omega0 u w := by
  simp [omega0]; ring

lemma projected_reconstruction (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : F.transpose * omegaMat * F = omegaMat) (v : R4)
    (hv : omega0 (col F 1) v = 0) :
    v - omega0 (col F 0) v • col F 1 =
      (F⁻¹.mulVec v) 2 • col F 2 + (F⁻¹.mulVec v) 3 • col F 3 := by
  have hp01 : omega0 (col F 0) (col F 1) = 1 := by
    rw [← transpose_omega_mul_apply, hF]; rfl
  have hp11 : omega0 (col F 1) (col F 1) = 0 := by
    rw [← transpose_omega_mul_apply, hF]; rfl
  let q := v - omega0 (col F 0) v • col F 1
  have hq0 : omega0 (col F 0) q = 0 := by
    dsimp [q]; rw [omega0_sub_smul_right, hp01]; ring
  have hq1 : omega0 (col F 1) q = 0 := by
    dsimp [q]; rw [omega0_sub_smul_right, hp11, hv]; ring
  have hc2 : (F⁻¹.mulVec q) 2 = (F⁻¹.mulVec v) 2 := by
    simp [q, Matrix.mulVec_sub, Matrix.mulVec_smul, inverse_mulVec_col F hF, Pi.single_apply]
  have hc3 : (F⁻¹.mulVec q) 3 = (F⁻¹.mulVec v) 3 := by
    simp [q, Matrix.mulVec_sub, Matrix.mulVec_smul, inverse_mulVec_col F hF, Pi.single_apply]
  simpa only [hc2, hc3] using reconstruct_transverse F hF q hq0 hq1

end HryniewiczCriterion.CanonicalMatrix


set_option backward.isDefEq.respectTransparency false

namespace BirkhoffGlobalSection.CanonicalCoordinates
open BirkhoffGlobalSection HryniewiczCriterion
open scoped ContDiff
noncomputable section
def toHrynCLM : Phase →L[ℝ] R4 :=
  ContinuousLinearMap.pi fun i =>
    ![ContinuousLinearMap.proj 0, -ContinuousLinearMap.proj 2,
      ContinuousLinearMap.proj 1, -ContinuousLinearMap.proj 3] i

def fromHrynCLM : R4 →L[ℝ] Phase :=
  ContinuousLinearMap.pi fun i =>
    ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 2,
      -ContinuousLinearMap.proj 1, -ContinuousLinearMap.proj 3] i

lemma toHrynCLM_apply (v : Phase) : toHrynCLM v = toHryn v := by
  ext i; fin_cases i <;> simp [toHrynCLM, toHryn]
lemma fromHrynCLM_apply (v : R4) : fromHrynCLM v = fromHryn v := by
  ext i; fin_cases i <;> simp [fromHrynCLM, fromHryn]

lemma from_to (v : Phase) : fromHryn (toHryn v) = v := by
  ext i; fin_cases i <;> simp [fromHryn, toHryn]
lemma to_from (v : R4) : toHryn (fromHryn v) = v := by
  ext i; fin_cases i <;> simp [fromHryn, toHryn]


def coordinateEquiv : Phase ≃L[ℝ] R4 where
  toLinearEquiv := { toHrynCLM.toLinearMap with
    invFun := fromHrynCLM
    left_inv := by
      intro v
      change fromHrynCLM (toHrynCLM v) = v
      rw [toHrynCLM_apply, fromHrynCLM_apply, from_to]
    right_inv := by
      intro v
      change toHrynCLM (fromHrynCLM v) = v
      rw [fromHrynCLM_apply, toHrynCLM_apply, to_from] }
  continuous_toFun := toHrynCLM.continuous
  continuous_invFun := fromHrynCLM.continuous

lemma coordinateEquiv_apply (v : Phase) : coordinateEquiv v = toHryn v := toHrynCLM_apply v
lemma coordinateEquiv_symm_apply (v : R4) : coordinateEquiv.symm v = fromHryn v :=
  fromHrynCLM_apply v

lemma coordinateEquiv_coe : (coordinateEquiv : Phase →L[ℝ] R4) = toHrynCLM := by
  ext v i; rfl
lemma coordinateEquiv_symm_coe : (coordinateEquiv.symm : R4 →L[ℝ] Phase) = fromHrynCLM := by
  ext v i; rfl

lemma pullback_fderiv (G : Phase → ℝ) (y : R4) :
    fderiv ℝ (fun z => G (fromHryn z)) y =
      (fderiv ℝ G (fromHryn y)).comp fromHrynCLM := by
  have h := coordinateEquiv.symm.comp_right_fderiv (f := G) (x := y)
  simpa only [Function.comp_def, coordinateEquiv_symm_apply, coordinateEquiv_symm_coe] using h

lemma fromHrynCLM_single (i : Fin 4) :
    fromHrynCLM (Pi.single i 1) =
      ![Pi.single 0 1, -Pi.single 2 1, Pi.single 1 1, -Pi.single 3 1] i := by
  ext j; fin_cases i <;> fin_cases j <;> simp [fromHrynCLM, Pi.single_apply]


end
end BirkhoffGlobalSection.CanonicalCoordinates

namespace HryniewiczCriterion.FrameTransition
open HryniewiczCriterion Matrix
noncomputable section

def toComplex (z : Fin 2 → ℝ) : ℂ := ⟨z 0, z 1⟩
def fromComplex (z : ℂ) : Fin 2 → ℝ := ![z.re, z.im]
def covectorGradient (L : R4 →L[ℝ] ℝ) : R4 := fun i => L (Pi.single i 1)
def dotCLM (g : R4) : R4 →L[ℝ] ℝ := ∑ i, g i • ContinuousLinearMap.proj i
def gradientCLM (g : R4) : R4 →L[ℝ] ℂ :=
  (dotCLM (-quatQ1 g)).smulRight (1 : ℂ) + (dotCLM (quatQ2 g)).smulRight Complex.I

def gauge (g : R4) (F : Matrix (Fin 4) (Fin 4) ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight (gradientCLM g (CanonicalMatrix.col F 2)) +
  Complex.imCLM.smulRight (gradientCLM g (CanonicalMatrix.col F 3))

lemma dotCLM_apply (g w : R4) : dotCLM g w = dot4 g w := by
  simp [dotCLM, dot4]

lemma gradientCLM_apply (g w : R4) :
    gradientCLM g w = toComplex (gradientCoordinates g w) := by
  apply Complex.ext <;> simp [gradientCLM, dotCLM_apply, toComplex,
    gradientCoordinates, dot4, Fin.sum_univ_four, Complex.real_smul] <;> ring

lemma covector_apply (L : R4 →L[ℝ] ℝ) (w : R4) : L w = dot4 (covectorGradient L) w := by
  have hw : w = ∑ i, w i • (Pi.single i 1 : R4) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  simp [map_smul, dot4, covectorGradient, mul_comm]

lemma gauge_apply (g : R4) (F : Matrix (Fin 4) (Fin 4) ℝ) (z : ℂ) :
    gauge g F z = gradientCLM g (z.re • CanonicalMatrix.col F 2 + z.im • CanonicalMatrix.col F 3) := by
  simp [gauge, map_add, map_smul]

lemma homogFrame_col1 (H : R4 → ℝ) (y : R4) :
    CanonicalMatrix.col (homogFrame H y) 1 =
      (omega0 y (HryniewiczCriterion.hamiltonianVectorField H y))⁻¹ •
        HryniewiczCriterion.hamiltonianVectorField H y := rfl

lemma homogFrame_col23 (H : R4 → ℝ) (y : R4) (i : Fin 2) :
    CanonicalMatrix.col (homogFrame H y) i.succ.succ =
      (euclidNorm y)⁻¹ • rawContactFrame (covectorGradient (fderiv ℝ H y)) y i := by
  fin_cases i <;> ext j <;>
    simp [CanonicalMatrix.col, homogFrame, xiFrame1, xiFrame2, xiFrameRaw,
      rawContactFrame, ← covector_apply]

lemma gradientCLM_hamiltonian (H : R4 → ℝ) (y : R4) :
    gradientCLM (covectorGradient (fderiv ℝ H y))
      (HryniewiczCriterion.hamiltonianVectorField H y) = 0 := by
  apply Complex.ext <;> simp [gradientCLM_apply, toComplex, gradientCoordinates,
    covectorGradient, HryniewiczCriterion.hamiltonianVectorField, partialDeriv,
    quatQ1, quatQ2, dot4, Fin.sum_univ_four] <;> ring

lemma gauge_positive (H : R4 → ℝ) (y : R4)
    (hr : 0 < fderiv ℝ H y y) (z : ℂ) (hz : z ≠ 0) :
    0 < (star z * gauge (covectorGradient (fderiv ℝ H y)) (homogFrame H y) z).im := by
  have hy : y ≠ 0 := by intro he; rw [he, map_zero] at hr; linarith
  have hnorm : 0 < (euclidNorm y)⁻¹ := by
    apply inv_pos.mpr
    apply Real.sqrt_pos.mpr
    change 0 < ∑ i, y i * y i
    by_contra he
    have hs : ∑ i, y i * y i = 0 := le_antisymm (not_lt.mp he)
      (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
    apply hy
    ext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (y i))).mp hs i (Finset.mem_univ _)
    simpa using hi
  have hz' : fromComplex z ≠ 0 := by
    intro he
    apply hz
    apply Complex.ext
    · exact congrFun he 0
    · exact congrFun he 1
  have hp := transition_cross_pos (covectorGradient (fderiv ℝ H y)) y (fromComplex z)
    (by rwa [← covector_apply]) hz'
  rw [gauge_apply]
  have h2 := homogFrame_col23 H y 0
  have h3 := homogFrame_col23 H y 1
  simp only [Fin.reduceSucc] at h2 h3
  rw [h2, h3]
  have he : z.re • ((euclidNorm y)⁻¹ • rawContactFrame (covectorGradient (fderiv ℝ H y)) y 0) +
      z.im • ((euclidNorm y)⁻¹ • rawContactFrame (covectorGradient (fderiv ℝ H y)) y 1) =
      (euclidNorm y)⁻¹ • (z.re • rawContactFrame (covectorGradient (fderiv ℝ H y)) y 0 +
      z.im • rawContactFrame (covectorGradient (fderiv ℝ H y)) y 1) := by
    simp only [smul_add, smul_smul]; congr 1 <;> congr 1 <;> ring
  rw [he, map_smul, gradientCLM_apply]
  simpa [Complex.mul_im, Complex.star_def, Complex.real_smul, toComplex, fromComplex,
    mul_sub, mul_add, mul_comm, mul_left_comm, mul_assoc] using mul_pos hnorm hp
end
end HryniewiczCriterion.FrameTransition

namespace HryniewiczCriterion.FrameTransition
open HryniewiczCriterion Matrix
noncomputable section

lemma gauge_continuous (g : ℝ → R4) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ∀ i, Continuous fun t => g t i) (hF : ∀ i j, Continuous fun t => F t i j) :
    Continuous fun t => gauge (g t) (F t) := by
  have hGc : ∀ j, Continuous fun t => gradientCLM (g t) (CanonicalMatrix.col (F t) j) := by
    intro j
    simp only [gradientCLM_apply, toComplex, gradientCoordinates, dot4, Fin.sum_univ_four,
      quatQ1, quatQ2, CanonicalMatrix.col, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  unfold gauge
  fun_prop

lemma gradient_projection (H : R4 → ℝ) (y w : R4)
    (hF : (homogFrame H y).transpose * omegaMat * homogFrame H y = omegaMat)
    (hw : fderiv ℝ H y w = 0) :
    gradientCLM (covectorGradient (fderiv ℝ H y)) w =
      gauge (covectorGradient (fderiv ℝ H y)) (homogFrame H y)
        (toComplex (fun i : Fin 2 => ((homogFrame H y)⁻¹.mulVec w) i.succ.succ)) := by
  have hω : omega0 (CanonicalMatrix.col (homogFrame H y) 1) w = 0 := by
    rw [homogFrame_col1]
    have hsmul : ∀ (c : ℝ) (u : R4), omega0 (c • u) w = c * omega0 u w := by
      intros; simp [omega0]; ring
    rw [hsmul]
    have hX : omega0 (HryniewiczCriterion.hamiltonianVectorField H y) w = - fderiv ℝ H y w := by
      rw [covector_apply]
      simp [omega0, HryniewiczCriterion.hamiltonianVectorField, partialDeriv,
        dot4, covectorGradient, Fin.sum_univ_four]
      ring
    rw [hX, hw]; simp
  have he := CanonicalMatrix.projected_reconstruction (homogFrame H y) hF w hω
  have he' := congrArg (gradientCLM (covectorGradient (fderiv ℝ H y))) he
  rw [map_sub, map_smul, homogFrame_col1, map_smul, gradientCLM_hamiltonian,
    smul_zero, smul_zero, sub_zero] at he'
  rw [gauge_apply]
  exact he'

lemma lower_coordinates_transport
    (F₀ F R : Matrix (Fin 4) (Fin 4) ℝ)
    (hF₀ : F₀.transpose * omegaMat * F₀ = omegaMat)
    (hF : F.transpose * omegaMat * F = omegaMat)
    (v : R4) (hv : omega0 (CanonicalMatrix.col F₀ 1) v = 0)
    (c : ℝ) (hR : R.mulVec (CanonicalMatrix.col F₀ 1) = c • CanonicalMatrix.col F 1) :
    (fun i : Fin 2 => (F⁻¹.mulVec (R.mulVec v)) i.succ.succ) =
      Matrix.mulVec (fun i j : Fin 2 => (F⁻¹ * R * F₀) i.succ.succ j.succ.succ)
        (fun i : Fin 2 => (F₀⁻¹.mulVec v) i.succ.succ) := by
  let η := F⁻¹ * R * F₀
  let z := F₀⁻¹.mulVec v
  have hz0 : z 0 = 0 := by
    have h := (CanonicalMatrix.frame_coordinates_pairing F₀ hF₀ v).2
    dsimp [z]; linarith
  have hη : η.mulVec z = F⁻¹.mulVec (R.mulVec v) := by
    dsimp [η, z]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc,
      (CanonicalMatrix.inverse_identities F₀ hF₀).2.1, Matrix.mul_one]
  have hcol : CanonicalMatrix.col η 1 = c • Pi.single 1 1 := by
    change (F⁻¹ * R).mulVec (CanonicalMatrix.col F₀ 1) = _
    rw [← Matrix.mulVec_mulVec, hR, Matrix.mulVec_smul, CanonicalMatrix.inverse_mulVec_col F hF]
  have hη2 : η 2 1 = 0 := by simpa [CanonicalMatrix.col] using congrFun hcol 2
  have hη3 : η 3 1 = 0 := by simpa [CanonicalMatrix.col] using congrFun hcol 3
  change (fun i : Fin 2 => (F⁻¹.mulVec (R.mulVec v)) i.succ.succ) =
    Matrix.mulVec (fun i j : Fin 2 => η i.succ.succ j.succ.succ) (fun i : Fin 2 => z i.succ.succ)
  ext i
  rw [← hη]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_two]
  fin_cases i
  · change η 2 0 * z 0 + η 2 1 * z 1 + η 2 2 * z 2 + η 2 3 * z 3 = _
    simp [hz0, hη2]
  · change η 3 0 * z 0 + η 3 1 * z 1 + η 3 2 * z 2 + η 3 3 * z 3 = _
    simp [hz0, hη3]


end
end HryniewiczCriterion.FrameTransition

namespace BirkhoffGlobalSection.CanonicalCoordinates
open BirkhoffGlobalSection HryniewiczCriterion HryniewiczCriterion.FrameTransition

lemma gradient_pullback (G : Phase → ℝ) (y : Phase) :
    covectorGradient (fderiv ℝ (fun z => G (fromHryn z)) (toHryn y)) =
      toHryn (TangentialHessian.grad G y) := by
  rw [pullback_fderiv, from_to]
  have hb : ∀ i : Fin 4, BirkhoffGlobalSection.coordinateVector i = Pi.single i 1 := by
    intro i; ext j; simp [BirkhoffGlobalSection.coordinateVector, Pi.single_apply, eq_comm]
  ext i; fin_cases i <;>
    simp [covectorGradient, ContinuousLinearMap.comp_apply, fromHrynCLM_single,
      toHryn, TangentialHessian.grad, partialDerivative, hb]

lemma gradient_coordinates_pullback (G : Phase → ℝ) (y w : Phase) :
    gradientCLM (covectorGradient (fderiv ℝ (fun z => G (fromHryn z)) (toHryn y))) (toHryn w) =
      toComplex (transverseFrameCoordinates (TangentialHessian.grad G y) w) := by
  rw [gradient_pullback, gradientCLM_apply]
  apply Complex.ext <;>
    simp [toComplex, gradientCoordinates, transverseFrameCoordinates, TangentialHessian.frame,
      TangentialHessian.qJ, TangentialHessian.qK, toHryn, quatQ1, quatQ2, dot4,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

end BirkhoffGlobalSection.CanonicalCoordinates

open BirkhoffGlobalSection HryniewiczCriterion
open scoped ContDiff

 theorem solution (G : Phase → ℝ) (x : ℝ → Phase) (T : ℝ)
    (hxc : Continuous x) (hG : ∀ t, ContDiffAt ℝ 2 G (x t))
    (hr : ∀ t, 0 < fderiv ℝ G (x t) (x t)) (hperiod : x T = x 0)
    (hFsp : ∀ t, (canonicalRadialFrame G x t).transpose * omegaMat *
      canonicalRadialFrame G x t = omegaMat)
    (hFc : ∀ i j, Continuous fun t => canonicalRadialFrame G x t i j) :
    ∃ A : ℝ → (ℂ →L[ℝ] ℂ), Continuous A ∧ A T = A 0 ∧
      (∀ t z, z ≠ 0 → 0 < (star z * A t z).im) ∧
      (∀ t w, fderiv ℝ G (x t) w = 0 →
        (⟨transverseFrameCoordinates (TangentialHessian.grad G (x t)) w 0,
           transverseFrameCoordinates (TangentialHessian.grad G (x t)) w 1⟩ : ℂ) =
        A t ⟨((canonicalRadialFrame G x t)⁻¹.mulVec (toHryn w)) 2,
             ((canonicalRadialFrame G x t)⁻¹.mulVec (toHryn w)) 3⟩) := by
  let H : R4 → ℝ := fun y => G (fromHryn y)
  let y : ℝ → R4 := fun t => toHryn (x t)
  let g : ℝ → R4 := fun t => FrameTransition.covectorGradient (fderiv ℝ H (y t))
  let A : ℝ → (ℂ →L[ℝ] ℂ) := fun t =>
    FrameTransition.gauge (g t) (canonicalRadialFrame G x t)
  have hyc : Continuous y := by
    simpa only [y, Function.comp_def, CanonicalCoordinates.toHrynCLM_apply] using
      CanonicalCoordinates.toHrynCLM.continuous.comp hxc
  have hH : ∀ t, ContDiffAt ℝ 2 H (y t) := by
    intro t
    have hGc : ContDiffAt ℝ 2 G (CanonicalCoordinates.fromHrynCLM (y t)) := by
      simpa only [y, CanonicalCoordinates.fromHrynCLM_apply, CanonicalCoordinates.from_to] using hG t
    have hh := hGc.comp (y t) CanonicalCoordinates.fromHrynCLM.contDiff.contDiffAt
    simpa only [H, Function.comp_def, CanonicalCoordinates.fromHrynCLM_apply] using hh
  have hdc : Continuous fun t => fderiv ℝ H (y t) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((hH t).continuousAt_fderiv (by norm_num)).comp hyc.continuousAt
  have hgc : ∀ i, Continuous fun t => g t i := by
    intro i
    exact hdc.clm_apply continuous_const
  have hrad : ∀ t, 0 < fderiv ℝ H (y t) (y t) := by
    intro t
    simpa only [H, y, CanonicalCoordinates.pullback_fderiv, CanonicalCoordinates.from_to,
      ContinuousLinearMap.comp_apply, CanonicalCoordinates.fromHrynCLM_apply] using hr t
  refine ⟨A, FrameTransition.gauge_continuous g _ hgc hFc, ?_, ?_, ?_⟩
  · simp only [A, g, y, canonicalRadialFrame, hperiod]
  · intro t z hz
    exact FrameTransition.gauge_positive H (y t) (hrad t) z hz
  · intro t w hw
    have hwt : fderiv ℝ H (y t) (toHryn w) = 0 := by
      simpa only [H, y, CanonicalCoordinates.pullback_fderiv, CanonicalCoordinates.from_to,
        ContinuousLinearMap.comp_apply, CanonicalCoordinates.fromHrynCLM_apply] using hw
    have he := FrameTransition.gradient_projection H (y t) (toHryn w) (hFsp t) hwt
    rw [CanonicalCoordinates.gradient_coordinates_pullback] at he
    exact he