-- Prove2me | solution 1 for BirkhoffGlobalSection.canonical_model_frame_data
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T17:19:06.240537+00:00
-- url     : https://prove2.me/submissions/5ed9789b-6b0b-4e21-b0d6-bba5a70829c8

import Definitions.Def_BirkhoffGlobalSection_CanonicalPositiveFrame
import Definitions.Def_BirkhoffGlobalSection_RegularizationModel
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.SpecialFunctions.Sqrt

-- Generic symplectic frame algebra reused with credit to Mazecto,
-- accepted submission 893234ef-5ec2-4f4b-b415-f79ec1030002.
open HryniewiczCriterion Matrix Complex
namespace HryniewiczCriterion
lemma clm_apply_eq_sum (L : R4 →L[ℝ] ℝ) (v : R4) :
    L v = v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1) +
      v 2 * L (Pi.single 2 1) + v 3 * L (Pi.single 3 1) := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : R4) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_smul, Fin.sum_univ_four, smul_eq_mul]

/-- The linear map `L ↦ J ∇L`: `jvec L = (-L e₁, L e₀, -L e₃, L e₂)`. -/
noncomputable def jvec : (R4 →L[ℝ] ℝ) →L[ℝ] R4 :=
  ContinuousLinearMap.pi fun i =>
    ![-(ContinuousLinearMap.apply ℝ ℝ (Pi.single 1 1 : R4)),
      ContinuousLinearMap.apply ℝ ℝ (Pi.single 0 1 : R4),
      -(ContinuousLinearMap.apply ℝ ℝ (Pi.single 3 1 : R4)),
      ContinuousLinearMap.apply ℝ ℝ (Pi.single 2 1 : R4)] i

lemma jvec_apply (L : R4 →L[ℝ] ℝ) :
    jvec L = ![-L (Pi.single 1 1), L (Pi.single 0 1), -L (Pi.single 3 1), L (Pi.single 2 1)] := by
  ext i; fin_cases i <;> simp [jvec]

lemma hamiltonianVectorField_eq (H : R4 → ℝ) :
    hamiltonianVectorField H = fun y => jvec (fderiv ℝ H y) := by
  funext y; rw [jvec_apply]; rfl

lemma omega0_jvec_left (L : R4 →L[ℝ] ℝ) (q : R4) : omega0 (jvec L) q = -L q := by
  rw [clm_apply_eq_sum L q, jvec_apply]; simp [omega0]; ring

lemma omega0_jvec_right (L : R4 →L[ℝ] ℝ) (p : R4) : omega0 p (jvec L) = L p := by
  rw [clm_apply_eq_sum L p, jvec_apply]; simp [omega0] <;> ring

lemma apply_jvec_add (L M : R4 →L[ℝ] ℝ) : L (jvec M) + M (jvec L) = 0 := by
  rw [clm_apply_eq_sum L, clm_apply_eq_sum M, jvec_apply, jvec_apply]; simp; ring

lemma apply_jvec_self (L : R4 →L[ℝ] ℝ) : L (jvec L) = 0 := by
  have := apply_jvec_add L L; linarith

lemma liouvilleForm_eq (x v : R4) : liouvilleForm x v = omega0 x v / 2 := by
  simp [liouvilleForm, omega0]

lemma omega0_antisymm (u v : R4) : omega0 u v = -omega0 v u := by
  simp [omega0]; ring

lemma omega0_self (u : R4) : omega0 u u = 0 := by
  simp [omega0]; ring

lemma omega0_lin_right (u a b c d : R4) (p q r s : ℝ) :
    omega0 u (p • a + q • b + r • c + s • d) =
      p * omega0 u a + q * omega0 u b + r * omega0 u c + s * omega0 u d := by
  simp [omega0]; ring

lemma omega0_lin_left (u a b : R4) (p q : ℝ) :
    omega0 (p • a + q • b) u = p * omega0 a u + q * omega0 b u := by
  simp [omega0]; ring

lemma omega0_smul_smul (u v : R4) (p q : ℝ) : omega0 (p • u) (q • v) = p * q * omega0 u v := by
  simp [omega0]; ring

/-- A symplectic pair `Z₁, Z₂` together with an `ω₀`-orthogonal symplectic pair `a, b`
spans `ℝ⁴`; every `v` that is `ω₀`-orthogonal to `a, b` lies in `span (Z₁, Z₂)`. -/
lemma eq_frame_of_omega0 (Z₁ Z₂ a b v : R4) (h12 : omega0 Z₁ Z₂ = 1)
    (h1a : omega0 Z₁ a = 0) (h1b : omega0 Z₁ b = 0) (h2a : omega0 Z₂ a = 0)
    (h2b : omega0 Z₂ b = 0) (hab : omega0 a b ≠ 0)
    (hva : omega0 v a = 0) (hvb : omega0 v b = 0) :
    v = omega0 v Z₂ • Z₁ + omega0 Z₁ v • Z₂ := by
  set w : Fin 4 → R4 := ![Z₁, Z₂, a, b] with hw
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    replace hg : g 0 • Z₁ + g 1 • Z₂ + g 2 • a + g 3 • b = 0 := by
      simpa [Fin.sum_univ_four, hw] using hg
    have e1 := congrArg (omega0 Z₁) hg
    have e2 := congrArg (omega0 Z₂) hg
    have e3 := congrArg (omega0 a) hg
    have e4 := congrArg (omega0 b) hg
    rw [omega0_lin_right] at e1 e2 e3 e4
    have z : ∀ u : R4, omega0 u 0 = 0 := fun u => by simp [omega0]
    rw [z] at e1 e2 e3 e4
    rw [omega0_self, h12, h1a, h1b] at e1
    rw [omega0_antisymm Z₂ Z₁, h12, omega0_self, h2a, h2b] at e2
    rw [omega0_antisymm a Z₁, omega0_antisymm a Z₂, h1a, h2a, omega0_self] at e3
    rw [omega0_antisymm b Z₁, omega0_antisymm b Z₂, omega0_antisymm b a, h1b, h2b,
      omega0_self] at e4
    have g1 : g 1 = 0 := by linarith
    have g0 : g 0 = 0 := by linarith
    have g3 : g 3 = 0 := by
      have : g 3 * omega0 a b = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hab
    have g2 : g 2 = 0 := by
      have : g 2 * omega0 a b = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hab
    intro i; fin_cases i <;> assumption
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hv : v ∈ Submodule.span ℝ (Set.range w) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
  replace hc : c 0 • Z₁ + c 1 • Z₂ + c 2 • a + c 3 • b = v := by
    simpa [Fin.sum_univ_four, hw] using hc
  -- pair with `a` and `b` to kill the last two coefficients
  have ea : omega0 v a = c 0 * omega0 Z₁ a + c 1 * omega0 Z₂ a + c 2 * omega0 a a +
      c 3 * omega0 b a := by
    rw [← hc, omega0_antisymm, omega0_lin_right]
    rw [omega0_antisymm a Z₁, omega0_antisymm a Z₂, omega0_antisymm a b, omega0_self]; ring
  have eb : omega0 v b = c 0 * omega0 Z₁ b + c 1 * omega0 Z₂ b + c 2 * omega0 a b +
      c 3 * omega0 b b := by
    rw [← hc, omega0_antisymm, omega0_lin_right]
    rw [omega0_antisymm b Z₁, omega0_antisymm b Z₂, omega0_antisymm b a, omega0_self]; ring
  rw [h1a, h2a, omega0_self, omega0_antisymm b a, hva] at ea
  rw [h1b, h2b, omega0_self, hvb] at eb
  have c3 : c 3 = 0 := by
    have : c 3 * omega0 a b = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hab
  have c2 : c 2 = 0 := by
    have : c 2 * omega0 a b = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hab
  have hv2 : v = c 0 • Z₁ + c 1 • Z₂ := by rw [← hc, c2, c3]; simp
  have k0 : omega0 v Z₂ = c 0 := by
    rw [hv2, omega0_lin_left, omega0_self, h12]; ring
  have k1 : omega0 Z₁ v = c 1 := by
    rw [hv2, omega0_antisymm, omega0_lin_left, omega0_self, omega0_antisymm Z₂ Z₁, h12]; ring
  rw [k0, k1]; exact hv2

/-- In the situation of `eq_frame_of_omega0`, `ω₀` on two such vectors is the
determinant of their `(Z₁, Z₂)`-coordinates. -/
lemma omega0_eq_det_of_frame (Z₁ Z₂ a b v w : R4) (h12 : omega0 Z₁ Z₂ = 1)
    (h1a : omega0 Z₁ a = 0) (h1b : omega0 Z₁ b = 0) (h2a : omega0 Z₂ a = 0)
    (h2b : omega0 Z₂ b = 0) (hab : omega0 a b ≠ 0)
    (hva : omega0 v a = 0) (hvb : omega0 v b = 0)
    (hwa : omega0 w a = 0) (hwb : omega0 w b = 0) :
    omega0 v w = omega0 v Z₂ * omega0 Z₁ w - omega0 w Z₂ * omega0 Z₁ v := by
  have hv := eq_frame_of_omega0 Z₁ Z₂ a b v h12 h1a h1b h2a h2b hab hva hvb
  have hw := eq_frame_of_omega0 Z₁ Z₂ a b w h12 h1a h1b h2a h2b hab hwa hwb
  set p := omega0 v Z₂; set q := omega0 Z₁ v
  set r := omega0 w Z₂; set s := omega0 Z₁ w
  rw [hv, hw]
  simp only [omega0] at h12 ⊢
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (p * s - r * q) * h12

end HryniewiczCriterion

namespace HryniewiczCriterion

variable {H : R4 → ℝ}

/-! ### Pointwise frame identities -/

lemma ne_zero_of_dH_pos {y : R4} (hy : 0 < fderiv ℝ H y y) : y ≠ 0 := by
  rintro rfl; simp at hy

lemma dot4_pos {y : R4} (hy : y ≠ 0) : 0 < dot4 y y := by
  by_contra h
  push Not at h
  apply hy
  have hs : ∀ i, y i * y i = 0 := by
    intro i
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ y j * y j := fun j _ => mul_self_nonneg _
    have hsum : ∑ j, y j * y j = 0 := le_antisymm h (Finset.sum_nonneg hnn)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum i (Finset.mem_univ _)
  ext i; simpa using hs i

lemma euclidNorm_sq (y : R4) : euclidNorm y * euclidNorm y = dot4 y y := by
  have : 0 ≤ dot4 y y := Finset.sum_nonneg fun j _ => mul_self_nonneg (y j)
  exact Real.mul_self_sqrt this

lemma dH_xiFrameRaw {y : R4} (hy : 0 < fderiv ℝ H y y) (Q : R4 → R4) :
    fderiv ℝ H y (xiFrameRaw H Q y) = 0 := by
  simp only [xiFrameRaw, map_sub, map_smul, smul_eq_mul]
  field_simp; ring

lemma omega0_xiFrameRaw_self (Q : R4 → R4) (hQ : ∀ y, omega0 y (Q y) = 0) (y : R4) :
    omega0 y (xiFrameRaw H Q y) = 0 := by
  have := hQ y
  simp only [xiFrameRaw, omega0] at this ⊢
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination this

lemma omega0_quatQ1 (y : R4) : omega0 y (quatQ1 y) = 0 := by
  simp [omega0, quatQ1]; ring

lemma omega0_quatQ2 (y : R4) : omega0 y (quatQ2 y) = 0 := by
  simp [omega0, quatQ2]; ring

lemma omega0_raw21 (y : R4) :
    omega0 (xiFrameRaw H quatQ2 y) (xiFrameRaw H quatQ1 y) = dot4 y y := by
  simp [xiFrameRaw, omega0, quatQ1, quatQ2, dot4, Fin.sum_univ_four]; ring

lemma omega0_xiFrame12 {y : R4} (hy : 0 < fderiv ℝ H y y) :
    omega0 (xiFrame1 H y) (xiFrame2 H y) = 1 := by
  have hpos := dot4_pos (ne_zero_of_dH_pos hy)
  have hn := euclidNorm_sq y
  have hne : euclidNorm y ≠ 0 := by
    intro h; rw [h] at hn; linarith
  rw [xiFrame1, xiFrame2, omega0_smul_smul, omega0_raw21, ← hn]
  field_simp

lemma omega0_xiFrame_y {y : R4} (Q : R4 → R4) (hQ : ∀ y, omega0 y (Q y) = 0) :
    omega0 ((euclidNorm y)⁻¹ • xiFrameRaw H Q y) y = 0 := by
  rw [omega0_antisymm]
  simp only [omega0] at *
  have := omega0_xiFrameRaw_self (H := H) Q hQ y
  simp only [omega0] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination (-(euclidNorm y)⁻¹) * this

lemma omega0_xiFrame_X {y : R4} (hy : 0 < fderiv ℝ H y y) (Q : R4 → R4) :
    omega0 ((euclidNorm y)⁻¹ • xiFrameRaw H Q y) (hamiltonianVectorField H y) = 0 := by
  rw [omega0_antisymm, hamiltonianVectorField_eq]
  simp only
  rw [omega0_jvec_left, map_smul, dH_xiFrameRaw hy]; simp

lemma omega0_y_X (y : R4) : omega0 y (hamiltonianVectorField H y) = fderiv ℝ H y y := by
  rw [hamiltonianVectorField_eq]; exact omega0_jvec_right _ _

lemma liouville_X (y : R4) :
    liouvilleForm y (hamiltonianVectorField H y) = fderiv ℝ H y y / 2 := by
  rw [liouvilleForm_eq, omega0_y_X]

/-! ### The Reeb projection -/

lemma omega0_reeb_y {y : R4} (hy : 0 < fderiv ℝ H y y) (w : R4) :
    omega0 (reebProjection H y w) y = 0 := by
  have hl : liouvilleForm y (hamiltonianVectorField H y) ≠ 0 := by
    rw [liouville_X]; positivity
  have hlin : ∀ (u X : R4) (c : ℝ), liouvilleForm y (u - c • X) =
      liouvilleForm y u - c * liouvilleForm y X := by
    intro u X c; simp [liouvilleForm]; ring
  have : liouvilleForm y (reebProjection H y w) = 0 := by
    rw [reebProjection, hlin, div_mul_cancel₀ _ hl, sub_self]
  rw [omega0_antisymm, liouvilleForm_eq] at *
  linarith

lemma dH_reeb (y w : R4) :
    fderiv ℝ H y (reebProjection H y w) = fderiv ℝ H y w := by
  rw [reebProjection, map_sub, map_smul, hamiltonianVectorField_eq]
  simp [apply_jvec_self]

lemma omega0_X_left (y w : R4) :
    omega0 (hamiltonianVectorField H y) w = -fderiv ℝ H y w := by
  rw [hamiltonianVectorField_eq]; exact omega0_jvec_left _ _

lemma omega0_reeb_X (y w : R4) (hw : fderiv ℝ H y w = 0) :
    omega0 (reebProjection H y w) (hamiltonianVectorField H y) = 0 := by
  rw [omega0_antisymm, omega0_X_left, dH_reeb, hw]; simp

lemma omega0_reeb_reeb (y v w : R4) (hv : fderiv ℝ H y v = 0) (hw : fderiv ℝ H y w = 0) :
    omega0 (reebProjection H y v) (reebProjection H y w) = omega0 v w := by
  have h1 := omega0_X_left (H := H) y v
  have h2 := omega0_X_left (H := H) y w
  rw [hv] at h1; rw [hw] at h2
  set X := hamiltonianVectorField H y
  set a := liouvilleForm y v / liouvilleForm y X
  set b := liouvilleForm y w / liouvilleForm y X
  have hXX := omega0_self X
  have e : omega0 (v - a • X) (w - b • X) =
      omega0 v w - b * omega0 v X - a * omega0 X w + a * b * omega0 X X := by
    simp [omega0]; ring
  rw [reebProjection, reebProjection, e, h2, hXX, omega0_antisymm v X, h1]; ring

/-! ### Smoothness -/


end HryniewiczCriterion

namespace HryniewiczCriterion

lemma transpose_omega_mul_apply (F : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    (F.transpose * omegaMat * F) i j = omega0 (fun k => F k i) (fun k => F k j) := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, omegaMat, omega0]; ring


end HryniewiczCriterion


namespace HryniewiczCriterion
variable {H : R4 → ℝ}
noncomputable section
def frameW (y w : R4) (m : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => (![y, ![-w 1, w 0, -w 3, w 2],
    m • (quatQ2 y - dot4 w (quatQ2 y) • y), m • (quatQ1 y - dot4 w (quatQ1 y) • y)] j) i

lemma re_I_cdet_frameW (y w : R4) (m : ℝ) :
    (I * cdet (frameW y w m)).re = m * (2 * dot4 y y + 2 * dot4 y w +
      (w 0 * y 2 - w 1 * y 3 - w 2 * y 0 + w 3 * y 1) ^ 2 +
      (w 0 * y 3 + w 1 * y 2 - w 2 * y 1 - w 3 * y 0) ^ 2) / 4 := by
  simp [cdet, cA, frameW, det_fin_two, dot4, Fin.sum_univ_four, quatQ1, quatQ2, Matrix.vecHead,
    Matrix.vecTail, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

lemma homogFrame_eq_frameW {y : R4} (hy : 0 < fderiv ℝ H y y) :
    homogFrame H y = frameW y (fun i => partialDeriv H y i / fderiv ℝ H y y) (euclidNorm y)⁻¹ := by
  have hs := hy.ne'
  have hL : ∀ v, fderiv ℝ H y v / fderiv ℝ H y y =
      dot4 (fun i => partialDeriv H y i / fderiv ℝ H y y) v := by
    intro v; rw [clm_apply_eq_sum (fderiv ℝ H y) v]
    simp only [dot4, Fin.sum_univ_four, partialDeriv]; field_simp
  have hω : omega0 y (hamiltonianVectorField H y) = fderiv ℝ H y y := omega0_y_X y
  ext i j
  fin_cases j
  · rfl
  · simp only [homogFrame, frameW, Matrix.of_apply, hω]
    fin_cases i <;> simp [hamiltonianVectorField] <;> (try field_simp)
  · simp only [homogFrame, frameW, Matrix.of_apply, xiFrame1, xiFrameRaw, hL]
    rfl
  · simp only [homogFrame, frameW, Matrix.of_apply, xiFrame2, xiFrameRaw, hL]
    rfl

lemma re_I_cdet_homogFrame_pos {y : R4} (hy : 0 < fderiv ℝ H y y) :
    0 < (I * cdet (homogFrame H y)).re := by
  have hy0 : y ≠ 0 := ne_zero_of_dH_pos hy
  rw [homogFrame_eq_frameW hy, re_I_cdet_frameW]
  set w : R4 := fun i => partialDeriv H y i / fderiv ℝ H y y
  have hyw : dot4 y w = 1 := by
    have h1 : dot4 y w * fderiv ℝ H y y = fderiv ℝ H y y := by
      conv_rhs => rw [clm_apply_eq_sum (fderiv ℝ H y) y]
      simp only [w, dot4, Fin.sum_univ_four, partialDeriv]; field_simp
    have h2 := hy.ne'
    calc dot4 y w = dot4 y w * fderiv ℝ H y y / fderiv ℝ H y y := by field_simp
      _ = 1 := by rw [h1, div_self h2]
  have hm : 0 < (euclidNorm y)⁻¹ := by
    have : 0 < euclidNorm y := Real.sqrt_pos.2 (dot4_pos hy0)
    positivity
  have hd := dot4_pos hy0
  rw [hyw]
  positivity

lemma homogFrame_sp {y : R4} (hy : 0 < fderiv ℝ H y y) :
    (homogFrame H y).transpose * omegaMat * homogFrame H y = omegaMat := by
  set X0 := hamiltonianVectorField H y
  set c := (omega0 y X0)⁻¹
  have hωxX : omega0 y X0 = fderiv ℝ H y y := omega0_y_X y
  set Z1 := xiFrame1 H y
  set Z2 := xiFrame2 H y
  have h12 : omega0 Z1 Z2 = 1 := omega0_xiFrame12 hy
  have h1x : omega0 Z1 y = 0 := omega0_xiFrame_y quatQ2 omega0_quatQ2
  have h2x : omega0 Z2 y = 0 := omega0_xiFrame_y quatQ1 omega0_quatQ1
  have h1X : omega0 Z1 X0 = 0 := omega0_xiFrame_X hy quatQ2
  have h2X : omega0 Z2 X0 = 0 := omega0_xiFrame_X hy quatQ1
  have hxX0 : omega0 y X0 ≠ 0 := by rw [hωxX]; exact hy.ne'
  have hcol : ∀ j, (fun k => homogFrame H y k j) = ![y, c • X0, Z1, Z2] j := fun j => rfl
  have hsr : ∀ (u v : R4) (a : ℝ), omega0 u (a • v) = a * omega0 u v := by
    intros; simp [omega0]; ring
  have p01 : omega0 y (c • X0) = 1 := by rw [hsr]; exact inv_mul_cancel₀ hxX0
  have p10 : omega0 (c • X0) y = -1 := by rw [omega0_antisymm, p01]
  have p21 : omega0 Z1 (c • X0) = 0 := by rw [hsr, h1X, mul_zero]
  have p31 : omega0 Z2 (c • X0) = 0 := by rw [hsr, h2X, mul_zero]
  have p12 : omega0 (c • X0) Z1 = 0 := by rw [omega0_antisymm, p21, neg_zero]
  have p13 : omega0 (c • X0) Z2 = 0 := by rw [omega0_antisymm, p31, neg_zero]
  have p02 : omega0 y Z1 = 0 := by rw [omega0_antisymm, h1x, neg_zero]
  have p03 : omega0 y Z2 = 0 := by rw [omega0_antisymm, h2x, neg_zero]
  have p32 : omega0 Z2 Z1 = -1 := by rw [omega0_antisymm, h12]
  ext i j
  rw [transpose_omega_mul_apply, hcol, hcol]
  fin_cases i <;> fin_cases j <;>
    simp [omegaMat, omega0_self, p01, p10, p21, p31, p12, p13, p02, p03, p32, h12, h1x, h2x]

end
end HryniewiczCriterion

namespace BirkhoffGlobalSection.CanonicalModel
open BirkhoffGlobalSection
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

lemma radial_derivative_pullback (G : Phase → ℝ) (x : Phase)
    (hG : DifferentiableAt ℝ G x) :
    fderiv ℝ (fun y => G (fromHryn y)) (toHryn x) (toHryn x) =
      fderiv ℝ G x x := by
  have hGc : DifferentiableAt ℝ G (fromHrynCLM (toHryn x)) := by
    simpa only [fromHrynCLM_apply, from_to] using hG
  have he := fderiv_comp (toHryn x) hGc fromHrynCLM.differentiableAt
  have heq : (fun y => G (fromHryn y)) = G ∘ fromHrynCLM := by
    ext y; simp only [Function.comp_apply, fromHrynCLM_apply]
  rw [heq]
  rw [he, fromHrynCLM.fderiv]
  simp only [ContinuousLinearMap.comp_apply, fromHrynCLM_apply, from_to]

lemma frame_algebra (G : Phase → ℝ) (x : ℝ → Phase) (t : ℝ)
    (hG : DifferentiableAt ℝ G (x t)) (hr : 0 < fderiv ℝ G (x t) (x t)) :
    (canonicalRadialFrame G x t).transpose * omegaMat * canonicalRadialFrame G x t = omegaMat ∧
      0 < (Complex.I * cdet (canonicalRadialFrame G x t)).re := by
  have hpos : 0 < fderiv ℝ (fun y => G (fromHryn y)) (toHryn (x t)) (toHryn (x t)) := by
    rwa [radial_derivative_pullback G (x t) hG]
  exact ⟨homogFrame_sp hpos, re_I_cdet_homogFrame_pos hpos⟩

end
end BirkhoffGlobalSection.CanonicalModel

namespace HryniewiczCriterion
lemma homogFrame_entries_continuous (H : R4 → ℝ) (y : ℝ → R4)
    (hyc : Continuous y) (hdc : Continuous (fun t => fderiv ℝ H (y t)))
    (hr : ∀ t, 0 < fderiv ℝ H (y t) (y t)) :
    ∀ i j, Continuous fun t => homogFrame H (y t) i j := by
  have hyi : ∀ i, Continuous fun t => y t i := fun i => (continuous_apply i).comp hyc
  have hrad : Continuous fun t => fderiv ℝ H (y t) (y t) := hdc.clm_apply hyc
  have hnorm : Continuous fun t => euclidNorm (y t) := by
    apply Real.continuous_sqrt.comp
    simpa only [dot4, Pi.mul_apply] using continuous_finset_sum Finset.univ (fun i _ => (hyi i).mul (hyi i))
  have hn0 : ∀ t, euclidNorm (y t) ≠ 0 := by
    intro t
    exact (Real.sqrt_pos.mpr (dot4_pos (ne_zero_of_dH_pos (hr t)))).ne'
  have hX : ∀ i, Continuous fun t => hamiltonianVectorField H (y t) i := by
    intro i; fin_cases i <;>
      simp only [hamiltonianVectorField, partialDeriv, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons] <;> fun_prop
  have hω : ∀ t, omega0 (y t) (hamiltonianVectorField H (y t)) = fderiv ℝ H (y t) (y t) :=
    fun t => omega0_y_X (y t)
  have hradinv : Continuous fun t => (fderiv ℝ H (y t) (y t))⁻¹ :=
    hrad.inv₀ (fun t => (hr t).ne')
  have hnorminv : Continuous fun t => (euclidNorm (y t))⁻¹ := hnorm.inv₀ hn0
  have hQ1 : Continuous fun t => quatQ1 (y t) := by
    apply continuous_pi; intro i; fin_cases i <;> simp [quatQ1] <;> fun_prop
  have hQ2 : Continuous fun t => quatQ2 (y t) := by
    apply continuous_pi; intro i; fin_cases i <;> simp [quatQ2] <;> fun_prop
  have hXi1 : Continuous fun t => xiFrame1 H (y t) := by
    dsimp [xiFrame1, xiFrameRaw]
    exact hnorminv.smul (hQ2.sub (((hdc.clm_apply hQ2).div hrad (fun t => (hr t).ne')).smul hyc))
  have hXi2 : Continuous fun t => xiFrame2 H (y t) := by
    dsimp [xiFrame2, xiFrameRaw]
    exact hnorminv.smul (hQ1.sub (((hdc.clm_apply hQ1).div hrad (fun t => (hr t).ne')).smul hyc))
  intro i j
  fin_cases j
  · change Continuous fun t => y t i
    exact hyi i
  · change Continuous fun t => ((omega0 (y t) (hamiltonianVectorField H (y t)))⁻¹ •
        hamiltonianVectorField H (y t)) i
    simp only [hω, Pi.smul_apply, smul_eq_mul]
    exact hradinv.mul (hX i)
  · change Continuous fun t => xiFrame1 H (y t) i
    exact (continuous_apply i).comp hXi1
  · change Continuous fun t => xiFrame2 H (y t) i
    exact (continuous_apply i).comp hXi2
end HryniewiczCriterion

namespace BirkhoffGlobalSection.CanonicalModel
open BirkhoffGlobalSection
open scoped ContDiff

lemma canonical_frame_continuous (G : Phase → ℝ) (x : ℝ → Phase)
    (hxc : Continuous x) (hG : ∀ t, ContDiffAt ℝ 2 G (x t))
    (hr : ∀ t, 0 < fderiv ℝ G (x t) (x t)) :
    ∀ i j, Continuous fun t => canonicalRadialFrame G x t i j := by
  let H : R4 → ℝ := fun y => G (fromHryn y)
  let y : ℝ → R4 := fun t => toHryn (x t)
  have hyc : Continuous y := by
    simpa only [y, Function.comp_def, toHrynCLM_apply] using toHrynCLM.continuous.comp hxc
  have hH : ∀ t, ContDiffAt ℝ 2 H (y t) := by
    intro t
    have hGc : ContDiffAt ℝ 2 G (fromHrynCLM (y t)) := by
      simpa only [y, fromHrynCLM_apply, from_to] using hG t
    have hh := hGc.comp (y t) fromHrynCLM.contDiff.contDiffAt
    simpa only [H, Function.comp_def, fromHrynCLM_apply] using hh
  have hdc : Continuous fun t => fderiv ℝ H (y t) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((hH t).continuousAt_fderiv (by norm_num)).comp hyc.continuousAt
  have hrad : ∀ t, 0 < fderiv ℝ H (y t) (y t) := by
    intro t
    change 0 < fderiv ℝ (fun y => G (fromHryn y)) (toHryn (x t)) (toHryn (x t))
    rw [radial_derivative_pullback G (x t) ((hG t).differentiableAt (by norm_num))]
    exact hr t
  exact homogFrame_entries_continuous H y hyc hdc hrad

lemma hrynFlowMatrix_zero (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase) : hrynFlowMatrix Y 0 = 1 := by
  ext i j
  simp only [hrynFlowMatrix, hY0, ContinuousLinearMap.id_apply, to_from]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

lemma radial_frame_inverse_mul_self (G : Phase → ℝ) (x : ℝ → Phase) (t : ℝ)
    (hG : DifferentiableAt ℝ G (x t)) (hr : 0 < fderiv ℝ G (x t) (x t)) :
    (canonicalRadialFrame G x t)⁻¹ * canonicalRadialFrame G x t = 1 := by
  have hsp := (frame_algebra G x t hG hr).1
  have hΩ : omegaMat * omegaMat = -1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [omegaMat, Matrix.mul_apply, Fin.sum_univ_four]
  have h1 : (-(omegaMat * (canonicalRadialFrame G x t).transpose * omegaMat)) *
      canonicalRadialFrame G x t = 1 := by
    calc _ = -(omegaMat * ((canonicalRadialFrame G x t).transpose * omegaMat *
        canonicalRadialFrame G x t)) := by simp only [Matrix.neg_mul, Matrix.mul_assoc]
         _ = 1 := by rw [hsp, hΩ, neg_neg]
  rw [Matrix.inv_eq_left_inv h1, h1]

lemma canonical_transverse_zero (G : Phase → ℝ) (x : ℝ → Phase) (T : ℝ)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase)
    (hG : DifferentiableAt ℝ G (x 0)) (hr : 0 < fderiv ℝ G (x 0) (x 0)) :
    canonicalTransversePath G x T Y 0 = 1 := by
  have hInv := radial_frame_inverse_mul_self G x 0 hG hr
  ext i j
  simp only [canonicalTransversePath, zero_mul, hrynFlowMatrix_zero Y hY0,
    Matrix.mul_one, hInv]
  fin_cases i <;> fin_cases j <;> simp

end BirkhoffGlobalSection.CanonicalModel

namespace BirkhoffGlobalSection.CanonicalModel
open BirkhoffGlobalSection
open scoped ContDiff

lemma matrix_mul_continuous
    (A B : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (hA : ∀ i j, Continuous fun t => A t i j)
    (hB : ∀ i j, Continuous fun t => B t i j) :
    ∀ i j, Continuous fun t => (A t * B t) i j := by
  intro i j
  simpa only [Matrix.mul_apply, Pi.mul_apply] using
    continuous_finsetSum Finset.univ (fun k _ => (hA i k).mul (hB k j))

lemma matrix_inverse_continuous_of_symplectic
    (A : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (hA : ∀ i j, Continuous fun t => A t i j)
    (hsp : ∀ t, (A t).transpose * omegaMat * A t = omegaMat) :
    ∀ i j, Continuous fun t => (A t)⁻¹ i j := by
  have hΩ : omegaMat * omegaMat = -1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [omegaMat, Matrix.mul_apply, Fin.sum_univ_four]
  have hinv : ∀ t, (A t)⁻¹ = -(omegaMat * (A t).transpose * omegaMat) := by
    intro t
    apply Matrix.inv_eq_left_inv
    calc _ = -(omegaMat * ((A t).transpose * omegaMat * A t)) := by
            simp only [Matrix.neg_mul, Matrix.mul_assoc]
         _ = 1 := by rw [hsp t, hΩ, neg_neg]
  have hc := matrix_mul_continuous (fun t => omegaMat * (A t).transpose) (fun _ => omegaMat)
    (matrix_mul_continuous (fun _ => omegaMat) (fun t => (A t).transpose)
      (fun _ _ => continuous_const) (fun i j => hA j i))
    (fun _ _ => continuous_const)
  intro i j
  simp only [hinv, Matrix.neg_apply]
  exact (hc i j).neg

lemma canonical_transverse_continuous (G : Phase → ℝ) (x : ℝ → Phase) (T : ℝ)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hxc : Continuous x) (hYc : Continuous Y)
    (hG : ∀ t, ContDiffAt ℝ 2 G (x t)) (hr : ∀ t, 0 < fderiv ℝ G (x t) (x t)) :
    ∀ i j, Continuous fun τ => canonicalTransversePath G x T Y τ i j := by
  have hFc := canonical_frame_continuous G x hxc hG hr
  have hFsp : ∀ t, (canonicalRadialFrame G x t).transpose * omegaMat *
      canonicalRadialFrame G x t = omegaMat := fun t =>
    (frame_algebra G x t ((hG t).differentiableAt (by norm_num)) (hr t)).1
  have hFic := matrix_inverse_continuous_of_symplectic _ hFc hFsp
  have hYmat : ∀ i j, Continuous fun t => hrynFlowMatrix Y t i j := by
    intro i j
    have hc := (continuous_apply i).comp
      (toHrynCLM.continuous.comp (hYc.clm_apply (continuous_const :
        Continuous (fun _ : ℝ => fromHryn (Pi.single j 1)))))
    simpa only [hrynFlowMatrix, Function.comp_def, toHrynCLM_apply] using hc
  have hAc := matrix_mul_continuous
    (fun t => (canonicalRadialFrame G x t)⁻¹ * hrynFlowMatrix Y t)
    (fun _ => canonicalRadialFrame G x 0)
    (matrix_mul_continuous _ _ hFic hYmat) (fun _ _ => continuous_const)
  intro i j
  exact (hAc i.succ.succ j.succ.succ).comp (continuous_id.mul_const T)

end BirkhoffGlobalSection.CanonicalModel

namespace BirkhoffGlobalSection.CanonicalModel
open BirkhoffGlobalSection
open scoped ContDiff

/-- Six geometric conditions for the canonical positive model. The two
remaining conditions are determinant one and the positive generator. -/
lemma canonical_model_frame_data (G : Phase → ℝ) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn G {y | IsStrictlyConvexStarShapedAt G y} x T)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase)
    (hY : ∀ t : ℝ, HasDerivAt Y
      ((fderiv ℝ (BirkhoffGlobalSection.hamiltonianVectorField G) (x t)).comp (Y t)) t) :
    (∀ t, (canonicalRadialFrame G x t).transpose * omegaMat *
      canonicalRadialFrame G x t = omegaMat) ∧
    (∀ t, 0 < (Complex.I * cdet (canonicalRadialFrame G x t)).re) ∧
    (∀ i j, Continuous fun t => canonicalRadialFrame G x t i j) ∧
    (canonicalRadialFrame G x T = canonicalRadialFrame G x 0) ∧
    (∀ i j, ContinuousOn (fun τ => canonicalTransversePath G x T Y τ i j) (Set.Icc 0 1)) ∧
    canonicalTransversePath G x T Y 0 = 1 := by
  have hG : ∀ t, ContDiffAt ℝ 2 G (x t) := fun t => (hx.2.1 t).1.1 _ (by simp)
  have hr : ∀ t, 0 < fderiv ℝ G (x t) (x t) := fun t => (hx.2.1 t).2
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun t =>
    (hx.2.2.1 t).continuousAt
  have hYc : Continuous Y := continuous_iff_continuousAt.mpr fun t => (hY t).continuousAt
  refine ⟨(fun t => (frame_algebra G x t ((hG t).differentiableAt (by norm_num)) (hr t)).1),
    (fun t => (frame_algebra G x t ((hG t).differentiableAt (by norm_num)) (hr t)).2),
    canonical_frame_continuous G x hxc hG hr, ?_, ?_, ?_⟩
  · simp only [canonicalRadialFrame, hx.2.2.2]
  · intro i j
    exact (canonical_transverse_continuous G x T Y hxc hYc hG hr i j).continuousOn
  · exact canonical_transverse_zero G x T Y hY0 ((hG 0).differentiableAt (by norm_num)) (hr 0)

end BirkhoffGlobalSection.CanonicalModel

open BirkhoffGlobalSection

theorem solution (G : Phase → ℝ) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn G {y | IsStrictlyConvexStarShapedAt G y} x T)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase)
    (hY : ∀ t : ℝ, HasDerivAt Y
      ((fderiv ℝ (BirkhoffGlobalSection.hamiltonianVectorField G) (x t)).comp (Y t)) t) :
    (∀ t, (canonicalRadialFrame G x t).transpose * omegaMat *
      canonicalRadialFrame G x t = omegaMat) ∧
    (∀ t, 0 < (Complex.I * cdet (canonicalRadialFrame G x t)).re) ∧
    (∀ i j, Continuous fun t => canonicalRadialFrame G x t i j) ∧
    (canonicalRadialFrame G x T = canonicalRadialFrame G x 0) ∧
    (∀ i j, ContinuousOn (fun τ => canonicalTransversePath G x T Y τ i j) (Set.Icc 0 1)) ∧
    canonicalTransversePath G x T Y 0 = 1  := by
  exact BirkhoffGlobalSection.CanonicalModel.canonical_model_frame_data G x T hx Y hY0 hY
