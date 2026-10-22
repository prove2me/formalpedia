-- Prove2me | solution 1 for BirkhoffGlobalSection.regular_frame_angle_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T18:13:31.925534+00:00
-- url     : https://prove2.me/submissions/cbf19e32-b374-4f2f-9d17-546b58c8c8d9

import Mathlib
import Definitions.Def_BirkhoffGlobalSection_AmbientRotation
import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel


/-!
# Algebraic core of the ambient/transverse angle comparison

In quaternionic frame coordinates, the variational map of a regular Hamiltonian orbit has
the block shape recorded by the hypotheses below (`Λ`: Hamiltonian direction, `p q r t`:
transverse block with determinant `s`, `b20 b30`: the coupling of the gradient direction
into the transverse plane, `b12 b13` determined by symplecticity). The product
`det C · conj ζ · z₀` of the complex determinant, the conjugated transported transverse
coordinates and the initial ones is never a nonpositive real: after multiplying by
`|A|²` it factors into two numbers with positive real part.
-/

namespace BirkhoffGlobalSection.FrameAngle


open ComplexConjugate

/-- A product of two complex numbers with positive real parts is not a nonpositive real. -/
theorem not_nonpos_real_of_mul {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    ¬ ((u * v).im = 0 ∧ (u * v).re ≤ 0) := by
  rintro ⟨him, hre⟩
  simp only [Complex.mul_im, Complex.mul_re] at him hre
  -- from `him`, v.im * u.re = - u.im * v.re
  have h1 : u.re * (u.re * v.re - u.im * v.im) = v.re * (u.re ^ 2 + u.im ^ 2) := by
    linear_combination (-u.im) * him
  have h2 : 0 < v.re * (u.re ^ 2 + u.im ^ 2) := by positivity
  have h3 := mul_nonpos_of_nonneg_of_nonpos hu.le hre
  linarith

/-- The algebraic core. -/
theorem core {Λ s b00 b10 b12 b13 b20 b30 p q r t x y : ℝ} (hΛ : 0 < Λ) (hs : 0 < s)
    (h00 : b00 * Λ = s) (hdet : p * t - q * r = s)
    (hc : b00 * b12 = b30 * p - b20 * r) (hd : b00 * b13 = b30 * q - b20 * t)
    (hz : (⟨x, y⟩ : ℂ) ≠ 0) :
    let D : ℂ := (⟨(b00 + Λ) / 2, b10 / 2⟩ : ℂ) * ⟨(p + t) / 2, (r - q) / 2⟩
      - (⟨b13 / 2, b12 / 2⟩ : ℂ) * ⟨b20 / 2, b30 / 2⟩
    let ζ : ℂ := ⟨p * x + q * y, r * x + t * y⟩
    ¬ ((D * conj ζ * ⟨x, y⟩).im = 0 ∧ (D * conj ζ * ⟨x, y⟩).re ≤ 0) := by
  intro D ζ
  set A : ℂ := ⟨(p + t) / 2, (r - q) / 2⟩ with hA
  have hb00 : 0 < b00 := by
    by_contra h; push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hΛ.le; linarith
  have hxy : 0 < x ^ 2 + y ^ 2 := by
    rcases (show x ≠ 0 ∨ y ≠ 0 by
      by_contra h; push Not at h; exact hz (by simp [Complex.ext_iff, h.1, h.2])) with h | h
    · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; positivity
    · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; positivity
  have hApos : 0 < (p + t) ^ 2 + (q - r) ^ 2 := by
    have e : 4 * s = (p + t) ^ 2 + (q - r) ^ 2 - (p - t) ^ 2 - (q + r) ^ 2 := by
      rw [← hdet]; ring
    have := sq_nonneg (p - t); have := sq_nonneg (q + r)
    linarith
  -- the two factors
  have hP1 : 0 < (D * conj A).re := by
    have key : 8 * b00 * (D * conj A).re =
        (b00 ^ 2 + b00 * Λ) * ((p + t) ^ 2 + (q - r) ^ 2)
          + ((p * b30 - r * b20) ^ 2 + (q * b30 - t * b20) ^ 2 + s * (b30 ^ 2 + b20 ^ 2)) := by
      simp only [D, hA, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.conj_re, Complex.conj_im]
      linear_combination (b20 * q - b20 * r + b30 * p + b30 * t) * hc
        + (-b20 * p - b20 * t + b30 * q - b30 * r) * hd + (b20 ^ 2 + b30 ^ 2) * hdet
    have : 0 < 8 * b00 * (D * conj A).re := by
      rw [key]; positivity
    exact pos_of_mul_pos_right this (by positivity)
  have hP2 : 0 < (A * conj ζ * ⟨x, y⟩).re := by
    have key : 2 * (A * conj ζ * ⟨x, y⟩).re =
        (p * x + q * y) ^ 2 + (r * x + t * y) ^ 2 + (p * t - q * r) * (x ^ 2 + y ^ 2) := by
      simp only [ζ, hA, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [hdet] at key
    have h1 := sq_nonneg (p * x + q * y); have h2 := sq_nonneg (r * x + t * y)
    have h3 : 0 < s * (x ^ 2 + y ^ 2) := by positivity
    linarith
  have hfac : D * conj ζ * ⟨x, y⟩ * (A * conj A) = (D * conj A) * (A * conj ζ * ⟨x, y⟩) := by ring
  have hAA : A * conj A = ((((p + t) ^ 2 + (q - r) ^ 2) / 4 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_apply]
    simp only [hA]; push_cast; ring
  intro ⟨him, hre⟩
  have h := not_nonpos_real_of_mul hP1 hP2
  rw [← hfac, hAA] at h
  apply h
  set k : ℝ := ((p + t) ^ 2 + (q - r) ^ 2) / 4
  have hk : 0 < k := by positivity
  constructor
  · rw [Complex.im_mul_ofReal, him, zero_mul]
  · rw [Complex.re_mul_ofReal]; exact mul_nonpos_of_nonpos_of_nonneg hre hk.le

end BirkhoffGlobalSection.FrameAngle


/-!
# Pointwise ambient/transverse phase comparison

For a linear map `Y` preserving `ω`, carrying `I g` to `I h` (`g`, `h` nonzero gradients),
and a vector `v ⊥ g` with nonzero transverse coordinates, the complex number
`det C(Y) · conj(z_h(Y v)) · z_g(v)` is not a nonpositive real.

Proof: pass to the quaternionic frames `Φ_x = (x, I x, J x, K x)` (`Φᵀ Φ = |x|²`), where
`b = Φ_hᵀ Y Φ_g` has the block shape of `FrameAngle.core`.
-/

namespace BirkhoffGlobalSection.FrameAngle

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian ComplexConjugate

/-- The quaternionic frame `(x, I x, J x, K x)`. -/
def fr (x : Phase) : Fin 4 → Phase :=
  ![x, ![x 2, x 3, -x 0, -x 1], ![x 1, -x 0, -x 3, x 2], ![-x 3, x 2, -x 1, x 0]]

theorem qI_mulVec (x : Phase) : qI.mulVec x = ![x 2, x 3, -x 0, -x 1] := by
  ext i; fin_cases i <;> simp [qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem qJ_mulVec (x : Phase) : qJ.mulVec x = ![x 1, -x 0, -x 3, x 2] := by
  ext i; fin_cases i <;> simp [qJ, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem qK_mulVec (x : Phase) : qK.mulVec x = ![-x 3, x 2, -x 1, x 0] := by
  ext i; fin_cases i <;> simp [qK, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

def nrm (x : Phase) : ℝ := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2

theorem nrm_pos {x : Phase} (hx : x ≠ 0) : 0 < nrm x := by
  unfold nrm
  by_contra h; push Not at h
  apply hx; ext i
  have h0 := sq_nonneg (x 0); have h1 := sq_nonneg (x 1)
  have h2 := sq_nonneg (x 2); have h3 := sq_nonneg (x 3)
  fin_cases i <;> simp <;> nlinarith

theorem tfc_eq (x w : Phase) : transverseFrameCoordinates x w = ![w ⬝ᵥ fr x 2, w ⬝ᵥ fr x 3] := by
  have h1 : frame x 1 = fr x 2 := by simp [frame, qJ_mulVec, fr]
  have h2 : frame x 2 = fr x 3 := by simp [frame, qK_mulVec, fr]
  simp only [transverseFrameCoordinates, h1, h2]

/-- Matrix entries of a linear map. -/
def ent (Y : Phase →L[ℝ] Phase) (k l : Fin 4) : ℝ := Y (coordinateVector l) k

theorem apply_eq (Y : Phase →L[ℝ] Phase) (w : Phase) (k : Fin 4) :
    Y w k = ∑ l, ent Y k l * w l := by
  have hw : w = ∑ l, w l • coordinateVector l := by
    ext i; simp [coordinateVector, Finset.sum_apply, Pi.smul_apply]
  conv_lhs => rw [hw]
  simp [map_sum, map_smul, Finset.sum_apply, ent, mul_comm]

theorem pointwise (g h v : Phase) (hg : g ≠ 0) (hh : h ≠ 0) (Y : Phase →L[ℝ] Phase)
    (hS : ∀ a b, phaseSymplecticForm (Y a) (Y b) = phaseSymplecticForm a b)
    (hL : Y (qI.mulVec g) = qI.mulVec h) (hv : v ⬝ᵥ g = 0)
    (hz : transverseFrameCoordinates g v ≠ 0) :
    ¬ ((ambientRotationDet Y
        * conj ⟨transverseFrameCoordinates h (Y v) 0, transverseFrameCoordinates h (Y v) 1⟩
        * ⟨transverseFrameCoordinates g v 0, transverseFrameCoordinates g v 1⟩).im = 0 ∧
      (ambientRotationDet Y
        * conj ⟨transverseFrameCoordinates h (Y v) 0, transverseFrameCoordinates h (Y v) 1⟩
        * ⟨transverseFrameCoordinates g v 0, transverseFrameCoordinates g v 1⟩).re ≤ 0) := by
  have hng := nrm_pos hg
  have hnh := nrm_pos hh
  -- scalar form of `Y`
  have hY : ∀ w : Phase, Y w = fun k => ∑ l, ent Y k l * w l := fun w => funext (apply_eq Y w)
  set m := ent Y
  -- frame entries `b i j = fr h i ⬝ Y (fr g j)`
  let b : Fin 4 → Fin 4 → ℝ := fun i j => fr h i ⬝ᵥ Y (fr g j)
  have hb : ∀ i j, b i j = ∑ k, fr h i k * ∑ l, m k l * fr g j l := by
    intro i j; simp only [b, dotProduct, hY]
  -- symplectic relations in frame coordinates
  have hω : ∀ j k : Fin 4,
      (b 1 j * b 0 k - b 0 j * b 1 k + b 3 j * b 2 k - b 2 j * b 3 k) =
        nrm h * phaseSymplecticForm (fr g j) (fr g k) := by
    intro j k
    rw [← hS]
    simp only [hb, hY, phaseSymplecticForm, Fin.sum_univ_four, fr, nrm]
    simp
    ring
  -- the Hamiltonian direction
  have hL' : ∀ k, ∑ l, m k l * (qI.mulVec g) l = (qI.mulVec h) k := by
    intro k; rw [← hL, hY]
  have hfr1 : fr g 1 = qI.mulVec g := by rw [qI_mulVec]; simp [fr]
  have hcol : ∀ i, b i 1 = fr h i ⬝ᵥ ![h 2, h 3, -h 0, -h 1] := by
    intro i; simp only [b]; rw [hfr1, hL, qI_mulVec]
  have b01 : b 0 1 = 0 := by rw [hcol]; simp [fr, dotProduct, Fin.sum_univ_four]; ring
  have b11 : b 1 1 = nrm h := by rw [hcol]; simp [fr, dotProduct, Fin.sum_univ_four, nrm]; ring
  have b21 : b 2 1 = 0 := by rw [hcol]; simp [fr, dotProduct, Fin.sum_univ_four]; ring
  have b31 : b 3 1 = 0 := by rw [hcol]; simp [fr, dotProduct, Fin.sum_univ_four]; ring
  have e10 := hω 1 0
  have e12 := hω 1 2
  have e13 := hω 1 3
  have e02 := hω 0 2
  have e03 := hω 0 3
  have e23 := hω 2 3
  simp [phaseSymplecticForm, fr] at e10 e12 e13 e02 e03 e23
  rw [b01, b11, b21, b31] at e10 e12 e13
  have b02 : b 0 2 = 0 := by
    have : nrm h * b 0 2 = 0 := by linear_combination e12
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hnh.ne'
    · exact h'
  have b03 : b 0 3 = 0 := by
    have : nrm h * b 0 3 = 0 := by linear_combination e13
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hnh.ne'
    · exact h'
  have b00 : b 0 0 = nrm g := by
    have : nrm h * (b 0 0 - nrm g) = 0 := by unfold nrm at *; linear_combination e10
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hnh.ne'
    · linarith
  rw [b02] at e02; rw [b03] at e03; rw [b02, b03] at e23
  have hc : b 0 0 * b 1 2 = b 3 0 * b 2 2 - b 2 0 * b 3 2 := by linear_combination -e02
  have hd : b 0 0 * b 1 3 = b 3 0 * b 2 3 - b 2 0 * b 3 3 := by linear_combination -e03
  have hdet : b 2 2 * b 3 3 - b 2 3 * b 3 2 = nrm g * nrm h := by
    unfold nrm at *; linear_combination -e23
  -- transverse coordinates
  set x := v ⬝ᵥ fr g 2 with hx
  set y := v ⬝ᵥ fr g 3 with hy
  have hz0 : transverseFrameCoordinates g v = ![x, y] := by rw [tfc_eq]
  have hzt : transverseFrameCoordinates h (Y v) =
      ![(b 2 2 * x + b 2 3 * y) / nrm g, (b 3 2 * x + b 3 3 * y) / nrm g] := by
    have k2 : nrm g * (Y v ⬝ᵥ fr h 2) = (g ⬝ᵥ v) * b 2 0 + (fr g 1 ⬝ᵥ v) * b 2 1
        + x * b 2 2 + y * b 2 3 := by
      simp only [hx, hy, hb, hY, dotProduct, Fin.sum_univ_four, fr, nrm]; simp; ring
    have k3 : nrm g * (Y v ⬝ᵥ fr h 3) = (g ⬝ᵥ v) * b 3 0 + (fr g 1 ⬝ᵥ v) * b 3 1
        + x * b 3 2 + y * b 3 3 := by
      simp only [hx, hy, hb, hY, dotProduct, Fin.sum_univ_four, fr, nrm]; simp; ring
    have hgv : g ⬝ᵥ v = 0 := by rw [dotProduct_comm]; exact hv
    rw [hgv, b21] at k2; rw [hgv, b31] at k3
    have z2 : Y v ⬝ᵥ fr h 2 = (b 2 2 * x + b 2 3 * y) / nrm g := by
      rw [eq_div_iff hng.ne']; linear_combination k2
    have z3 : Y v ⬝ᵥ fr h 3 = (b 3 2 * x + b 3 3 * y) / nrm g := by
      rw [eq_div_iff hng.ne']; linear_combination k3
    rw [tfc_eq, z2, z3]
  -- the determinant in frame coordinates
  have hdetC : ((nrm g * nrm h : ℝ) : ℂ) * ambientRotationDet Y =
      (⟨(b 0 0 + b 1 1) / 2, (b 1 0 - b 0 1) / 2⟩ : ℂ) * ⟨(b 2 2 + b 3 3) / 2, (b 3 2 - b 2 3) / 2⟩
        - (⟨(b 0 2 + b 1 3) / 2, (b 1 2 - b 0 3) / 2⟩ : ℂ) * ⟨(b 2 0 + b 3 1) / 2, (b 3 0 - b 2 1) / 2⟩ := by
    apply Complex.ext
    · simp only [ambientRotationDet, ambientComplexLinearPart, Matrix.det_fin_two, Complex.mul_re,
        Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.sub_im]
      simp only [hb, fr, nrm, Fin.sum_univ_four]
      simp [m, ent, Fin.castAdd, Fin.natAdd, Fin.castLE]
      ring
    · simp only [ambientRotationDet, ambientComplexLinearPart, Matrix.det_fin_two, Complex.mul_re,
        Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.sub_im]
      simp only [hb, fr, nrm, Fin.sum_univ_four]
      simp [m, ent, Fin.castAdd, Fin.natAdd, Fin.castLE]
      ring
  rw [b01, b11, b02, b03, b21, b31] at hdetC
  simp only [sub_zero, zero_add, add_zero] at hdetC
  have hzne : (⟨x, y⟩ : ℂ) ≠ 0 := by
    intro e; apply hz; rw [hz0]
    have ex : x = 0 := by have := congrArg Complex.re e; simpa using this
    have ey : y = 0 := by have := congrArg Complex.im e; simpa using this
    ext i; fin_cases i <;> simp [ex, ey]
  have hcore := core (Λ := nrm h) (s := nrm g * nrm h) (b00 := b 0 0) (b10 := b 1 0)
    (b12 := b 1 2) (b13 := b 1 3) (b20 := b 2 0) (b30 := b 3 0) (p := b 2 2) (q := b 2 3)
    (r := b 3 2) (t := b 3 3) (x := x) (y := y) hnh (mul_pos hng hnh) (by rw [b00])
    hdet hc hd hzne
  simp only at hcore
  rw [← hdetC] at hcore
  rw [hz0, hzt]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  set Q := ambientRotationDet Y * conj (⟨(b 2 2 * x + b 2 3 * y) / nrm g,
    (b 3 2 * x + b 3 3 * y) / nrm g⟩ : ℂ) * ⟨x, y⟩ with hQ
  have hζ : (⟨b 2 2 * x + b 2 3 * y, b 3 2 * x + b 3 3 * y⟩ : ℂ) =
      ((nrm g : ℝ) : ℂ) * ⟨(b 2 2 * x + b 2 3 * y) / nrm g, (b 3 2 * x + b 3 3 * y) / nrm g⟩ := by
    apply Complex.ext <;> simp <;> field_simp
  have hk : ((nrm g * nrm h : ℝ) : ℂ) * ambientRotationDet Y
      * conj (⟨b 2 2 * x + b 2 3 * y, b 3 2 * x + b 3 3 * y⟩ : ℂ) * ⟨x, y⟩
      = ((nrm g * nrm g * nrm h : ℝ) : ℂ) * Q := by
    rw [hζ, hQ, map_mul, Complex.conj_ofReal]; push_cast; ring
  rw [hk] at hcore
  rintro ⟨him, hre⟩
  apply hcore
  have hkpos : 0 < nrm g * nrm g * nrm h := by positivity
  constructor
  · rw [Complex.im_ofReal_mul, him, mul_zero]
  · rw [Complex.re_ofReal_mul]; exact mul_nonpos_of_nonneg_of_nonpos hkpos.le hre

end BirkhoffGlobalSection.FrameAngle


/-!
# Ambient determinant angle versus transverse polar angle

Along a regular Hamiltonian trajectory the variational flow `Y t` is symplectic and carries
the Hamiltonian vector field `X(x 0)` to `X(x t)`. By `FrameAngle.pointwise` the phase
`α t - θ t + θ 0` therefore never reaches `α 0 + π` (mod nothing: by continuity), which gives
`α T - α 0 ≤ θ T - θ 0 + π`.
-/

namespace BirkhoffGlobalSection.FrameAngle

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian ComplexConjugate
open scoped ContDiff

theorem clm_apply_eq (L : Phase →L[ℝ] ℝ) (w : Phase) :
    L w = ∑ i, w i * L (coordinateVector i) := by
  have hw : w = ∑ i, w i • coordinateVector i := by
    ext i; simp [coordinateVector, Finset.sum_apply, Pi.smul_apply]
  conv_lhs => rw [hw]
  simp [map_sum, map_smul]

theorem grad_dot (F : Phase → ℝ) (y w : Phase) : fderiv ℝ F y w = w ⬝ᵥ grad F y := by
  rw [clm_apply_eq]; simp [dotProduct, grad, partialDerivative]

theorem grad_ne_zero {F : Phase → ℝ} {y : Phase} (h : fderiv ℝ F y ≠ 0) : grad F y ≠ 0 := by
  intro hg; apply h; ext w; rw [grad_dot, hg]; simp

theorem ham_eq (F : Phase → ℝ) (y : Phase) :
    hamiltonianVectorField F y = qI.mulVec (grad F y) := by
  rw [qI_mulVec]; ext i; fin_cases i <;> simp [hamiltonianVectorField, grad]

theorem omega_ham (F : Phase → ℝ) (y w : Phase) :
    phaseSymplecticForm (hamiltonianVectorField F y) w = fderiv ℝ F y w := by
  rw [clm_apply_eq]
  simp [hamiltonianVectorField, partialDerivative, phaseSymplecticForm, Fin.sum_univ_four]
  ring

/-- Nondegeneracy of `ω`. -/
theorem eq_zero_of_omega {d : Phase} (h : ∀ u, phaseSymplecticForm d u = 0) : d = 0 := by
  have h0 := h (coordinateVector 0); have h1 := h (coordinateVector 1)
  have h2 := h (coordinateVector 2); have h3 := h (coordinateVector 3)
  simp [phaseSymplecticForm, coordinateVector] at h0 h1 h2 h3
  ext i; fin_cases i <;> simp <;> linarith

/-- The linearized Hamiltonian field is `ω`-skew. -/
theorem omega_skew {F : Phase → ℝ} {y : Phase} (hF : ContDiffAt ℝ ∞ F y) (v w : Phase) :
    phaseSymplecticForm (fderiv ℝ (hamiltonianVectorField F) y v) w
      + phaseSymplecticForm v (fderiv ℝ (hamiltonianVectorField F) y w) = 0 := by
  have hF2 : ContDiffAt ℝ 2 F y := hF.of_le (WithTop.coe_le_coe.mpr le_top)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hF2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcomp : ∀ i : Fin 4, DifferentiableAt ℝ (fun x => fderiv ℝ F x (coordinateVector i)) y :=
    fun i => hd.clm_apply (differentiableAt_const _)
  have hD : ∀ i (u : Phase), fderiv ℝ (fun x => fderiv ℝ F x (coordinateVector i)) y u =
      fderiv ℝ (fderiv ℝ F) y u (coordinateVector i) := by
    intro i u; rw [fderiv_clm_apply hd (differentiableAt_const _)]; simp
  have hX : ∀ u, fderiv ℝ (hamiltonianVectorField F) y u =
      ![fderiv ℝ (fderiv ℝ F) y u (coordinateVector 2), fderiv ℝ (fderiv ℝ F) y u (coordinateVector 3),
        -fderiv ℝ (fderiv ℝ F) y u (coordinateVector 0),
        -fderiv ℝ (fderiv ℝ F) y u (coordinateVector 1)] := by
    intro u
    have hdiff : ∀ i : Fin 4, DifferentiableAt ℝ (fun x => hamiltonianVectorField F x i) y := by
      intro i; fin_cases i
      · exact hcomp 2
      · exact hcomp 3
      · exact (hcomp 0).neg
      · exact (hcomp 1).neg
    rw [fderiv_pi hdiff]
    ext i; fin_cases i
    · simp [hamiltonianVectorField, partialDerivative, hD]
    · simp [hamiltonianVectorField, partialDerivative, hD]
    · simp [hamiltonianVectorField, partialDerivative, hD]
    · simp [hamiltonianVectorField, partialDerivative, hD]
  have hsymm := hF2.isSymmSndFDerivAt (by simp)
  set D := fderiv ℝ (fderiv ℝ F) y
  have lin : ∀ a b : Phase, D a b = ∑ i, b i * D a (coordinateVector i) :=
    fun a b => clm_apply_eq (D a) b
  have key : D v w = D w v := hsymm v w
  rw [lin v w, lin w v] at key
  rw [hX v, hX w]
  simp [phaseSymplecticForm, Fin.sum_univ_four] at key ⊢
  linarith

/-- Derivative of the symplectic pairing along two curves. -/
theorem hasDerivAt_omega {u w : ℝ → Phase} {u' w' : Phase} {t : ℝ}
    (hu : HasDerivAt u u' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => phaseSymplecticForm (u s) (w s))
      (phaseSymplecticForm u' (w t) + phaseSymplecticForm (u t) w') t := by
  have c : ∀ (f : ℝ → Phase) (f' : Phase), HasDerivAt f f' t → ∀ i, HasDerivAt (fun s => f s i) (f' i) t :=
    fun f f' hf i => (hasDerivAt_pi.mp hf) i
  have := (((((c u u' hu 0).mul (c w w' hw 2)).sub ((c u u' hu 2).mul (c w w' hw 0))).add
    ((c u u' hu 1).mul (c w w' hw 3))).sub ((c u u' hu 3).mul (c w w' hw 1)))
  exact this.congr_deriv (by simp only [phaseSymplecticForm]; ring)

section flow

variable {F : Phase → ℝ} {x : ℝ → Phase} {Y : ℝ → (Phase →L[ℝ] Phase)}

theorem const_of_hasDerivAt_zero {f : ℝ → ℝ} (hf : ∀ t, HasDerivAt f 0 t) (t : ℝ) : f t = f 0 :=
  is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt) (fun s => (hf s).deriv) t 0

theorem variational_apply (hY : IsHamiltonianVariationalSolution F x Y) (a : Phase) (t : ℝ) :
    HasDerivAt (fun s => Y s a) (fderiv ℝ (hamiltonianVectorField F) (x t) (Y t a)) t := by
  have := (hY.2 t).clm_apply (hasDerivAt_const t a)
  simpa using this

theorem flow_symplectic (hreg : ∀ t, ContDiffAt ℝ ∞ F (x t))
    (hY : IsHamiltonianVariationalSolution F x Y) (t : ℝ) (a b : Phase) :
    phaseSymplecticForm (Y t a) (Y t b) = phaseSymplecticForm a b := by
  have hder : ∀ s, HasDerivAt (fun s => phaseSymplecticForm (Y s a) (Y s b)) 0 s := by
    intro s
    have := hasDerivAt_omega (variational_apply hY a s) (variational_apply hY b s)
    rwa [omega_skew (hreg s)] at this
  rw [const_of_hasDerivAt_zero hder t, hY.1]; rfl

theorem field_variational (hreg : ∀ t, ContDiffAt ℝ ∞ F (x t))
    (hx : ∀ t, HasDerivAt x (hamiltonianVectorField F (x t)) t) (t : ℝ) :
    HasDerivAt (fun s => hamiltonianVectorField F (x s))
      (fderiv ℝ (hamiltonianVectorField F) (x t) (hamiltonianVectorField F (x t))) t := by
  have hF2 : ContDiffAt ℝ 2 F (x t) := (hreg t).of_le (WithTop.coe_le_coe.mpr le_top)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) (x t) :=
    (hF2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcomp : ∀ i : Fin 4,
      DifferentiableAt ℝ (fun y => fderiv ℝ F y (coordinateVector i)) (x t) :=
    fun i => hd.clm_apply (differentiableAt_const _)
  have hX : DifferentiableAt ℝ (hamiltonianVectorField F) (x t) := by
    rw [differentiableAt_pi]; intro i; fin_cases i
    · exact hcomp 2
    · exact hcomp 3
    · exact (hcomp 0).neg
    · exact (hcomp 1).neg
  exact hX.hasFDerivAt.comp_hasDerivAt t (hx t)

/-- `Y t` carries the Hamiltonian vector field at `x 0` to the one at `x t`. -/
theorem flow_field (hreg : ∀ t, ContDiffAt ℝ ∞ F (x t))
    (hx : ∀ t, HasDerivAt x (hamiltonianVectorField F (x t)) t)
    (hY : IsHamiltonianVariationalSolution F x Y) (t : ℝ) :
    Y t (hamiltonianVectorField F (x 0)) = hamiltonianVectorField F (x t) := by
  -- `ω(X(x s), Y s w)` is constant
  have hc : ∀ w, phaseSymplecticForm (hamiltonianVectorField F (x t)) (Y t w) = fderiv ℝ F (x 0) w := by
    intro w
    have hder : ∀ s, HasDerivAt
        (fun s => phaseSymplecticForm (hamiltonianVectorField F (x s)) (Y s w)) 0 s := by
      intro s
      have := hasDerivAt_omega (field_variational hreg hx s) (variational_apply hY w s)
      rwa [omega_skew (hreg s)] at this
    have := const_of_hasDerivAt_zero hder t
    rw [this, hY.1]; exact omega_ham F (x 0) w
  -- `Y t` is surjective
  have hinj : Function.Injective (Y t) := by
    intro a b hab
    have : a - b = 0 := eq_zero_of_omega fun u => by
      obtain ⟨u', -⟩ : ∃ u', True := ⟨u, trivial⟩
      have h1 := flow_symplectic hreg hY t (a - b) u
      rw [map_sub, hab, sub_self] at h1
      simp [phaseSymplecticForm] at h1 ⊢; linarith
    exact sub_eq_zero.mp this
  have hsurj : Function.Surjective (Y t) :=
    (LinearMap.injective_iff_surjective (f := (Y t : Phase →ₗ[ℝ] Phase))).mp hinj
  have : Y t (hamiltonianVectorField F (x 0)) - hamiltonianVectorField F (x t) = 0 := by
    apply eq_zero_of_omega
    intro u
    obtain ⟨w, rfl⟩ := hsurj u
    have h1 := flow_symplectic hreg hY t (hamiltonianVectorField F (x 0)) w
    have h2 := hc w
    rw [omega_ham] at h1
    simp only [phaseSymplecticForm, Pi.sub_apply] at h1 h2 ⊢
    linarith
  exact sub_eq_zero.mp this

end flow

theorem ambientRotationDet_id : ambientRotationDet (ContinuousLinearMap.id ℝ Phase) = 1 := by
  simp [ambientRotationDet, ambientComplexLinearPart, Matrix.det_fin_two, coordinateVector,
    Fin.castAdd, Fin.natAdd, Fin.castLE, Complex.ext_iff]

/-- Phase of the comparison quantity. -/
theorem phase_eq (ρ σ σ0 a b c : ℝ) :
    (⟨ρ * Real.cos a, ρ * Real.sin a⟩ : ℂ) * conj ⟨σ * Real.cos b, σ * Real.sin b⟩
      * ⟨σ0 * Real.cos c, σ0 * Real.sin c⟩ =
      ⟨ρ * σ * σ0 * Real.cos (a - b + c), ρ * σ * σ0 * Real.sin (a - b + c)⟩ := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Real.cos_add, Real.sin_add, Real.cos_sub,
      Real.sin_sub] <;> ring

end BirkhoffGlobalSection.FrameAngle

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian
  BirkhoffGlobalSection.FrameAngle ComplexConjugate in
open scoped ContDiff in
theorem regular_frame_angle_comparison'
    (F : Phase → ℝ) (S : Set Phase) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn F S x T)
    (hregular : ∀ t : ℝ, ContDiffAt ℝ ∞ F (x t) ∧ fderiv ℝ F (x t) ≠ 0)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution F x Y)
    (α : ℝ → ℝ) (hα : IsAmbientRotationAngle Y α)
    (v : Phase) (hv : fderiv ℝ F (x 0) v = 0)
    (htrans : transverseFrameCoordinates (TangentialHessian.grad F (x 0)) v ≠ 0)
    (θ : ℝ → ℝ) (hθ : Continuous θ)
    (hpol : ∀ t : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
          transverseFrameCoordinates (TangentialHessian.grad F (x t)) (Y t v) =
            ![ρ * Real.cos (θ t), ρ * Real.sin (θ t)]) :
    α T - α 0 ≤ θ T - θ 0 + Real.pi := by
  have hreg : ∀ t, ContDiffAt ℝ ∞ F (x t) := fun t => (hregular t).1
  -- the pointwise obstruction at every time
  have hpt : ∀ t, ¬ ((ambientRotationDet (Y t)
        * conj ⟨transverseFrameCoordinates (grad F (x t)) (Y t v) 0,
            transverseFrameCoordinates (grad F (x t)) (Y t v) 1⟩
        * ⟨transverseFrameCoordinates (grad F (x 0)) v 0,
            transverseFrameCoordinates (grad F (x 0)) v 1⟩).im = 0 ∧
      (ambientRotationDet (Y t)
        * conj ⟨transverseFrameCoordinates (grad F (x t)) (Y t v) 0,
            transverseFrameCoordinates (grad F (x t)) (Y t v) 1⟩
        * ⟨transverseFrameCoordinates (grad F (x 0)) v 0,
            transverseFrameCoordinates (grad F (x 0)) v 1⟩).re ≤ 0) := by
    intro t
    refine pointwise (grad F (x 0)) (grad F (x t)) v (grad_ne_zero (hregular 0).2)
      (grad_ne_zero (hregular t).2) (Y t) (flow_symplectic hreg hY t) ?_ ?_ htrans
    · rw [← ham_eq, ← ham_eq]; exact flow_field hreg hx.2.2.1 hY t
    · rw [← grad_dot]; exact hv
  -- polar data
  obtain ⟨σ0, hσ0, hz0⟩ := hpol 0
  have hY0 : Y 0 v = v := by rw [hY.1]; rfl
  rw [hY0] at hz0
  obtain ⟨ρ0, hρ0, hdet0⟩ := hα.2 0
  rw [hY.1, ambientRotationDet_id] at hdet0
  have hsin0 : Real.sin (α 0) = 0 := by
    have := congrArg Complex.im hdet0; simp at this
    rcases this with h | h
    · linarith
    · exact h
  have hcos0 : 0 < Real.cos (α 0) := by
    have := congrArg Complex.re hdet0; simp at this
    by_contra h; push Not at h; nlinarith [mul_nonpos_of_nonneg_of_nonpos hρ0.le h]
  -- the continuous phase
  set h : ℝ → ℝ := fun t => α t - θ t + θ 0 with hh
  have hcont : Continuous h := (hα.1.sub hθ).add continuous_const
  by_contra hcon
  push Not at hcon
  have hT : 0 < T := hx.1
  have hmem : α 0 + Real.pi ∈ Set.Icc (h 0) (h T) := by
    constructor
    · simp only [hh]; linarith [Real.pi_pos]
    · simp only [hh]; linarith
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc hT.le hcont.continuousOn hmem
  apply hpt t
  obtain ⟨ρ, hρ, hdet⟩ := hα.2 t
  obtain ⟨σ, hσ, hzt⟩ := hpol t
  rw [hdet, hzt, hz0]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [phase_eq]
  have : α t - θ t + θ 0 = α 0 + Real.pi := ht
  rw [this, Real.cos_add_pi, Real.sin_add_pi, hsin0]
  constructor
  · simp
  · simp only
    have : 0 < ρ * σ * σ0 := by positivity
    nlinarith

open BirkhoffGlobalSection in
open scoped ContDiff in
theorem solution
    (F : Phase → ℝ) (S : Set Phase) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn F S x T)
    (hregular : ∀ t : ℝ, ContDiffAt ℝ ∞ F (x t) ∧ fderiv ℝ F (x t) ≠ 0)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution F x Y)
    (α : ℝ → ℝ) (hα : IsAmbientRotationAngle Y α)
    (v : Phase) (hv : fderiv ℝ F (x 0) v = 0)
    (htrans : transverseFrameCoordinates (TangentialHessian.grad F (x 0)) v ≠ 0)
    (θ : ℝ → ℝ) (hθ : Continuous θ)
    (hpol : ∀ t : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
          transverseFrameCoordinates (TangentialHessian.grad F (x t)) (Y t v) =
            ![ρ * Real.cos (θ t), ρ * Real.sin (θ t)])
    (hdet1 : ContDiffOn ℝ 1 (fun t => ambientRotationDet (Y t)) Set.univ)
    (hz1 : ContDiffOn ℝ 1
      (fun t => transverseFrameCoordinates (TangentialHessian.grad F (x t)) (Y t v))
      Set.univ)
    (hzne : ∀ t : ℝ,
      transverseFrameCoordinates (TangentialHessian.grad F (x t)) (Y t v) ≠ 0) :
    α T - α 0 ≤ θ T - θ 0 + 2 * Real.pi := by
  have h := regular_frame_angle_comparison' F S x T hx hregular Y hY α hα v hv htrans θ hθ hpol
  linarith [Real.pi_pos]
