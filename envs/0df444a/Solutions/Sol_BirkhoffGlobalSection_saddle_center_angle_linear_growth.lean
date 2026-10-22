-- Prove2me | solution 1 for BirkhoffGlobalSection.saddle_center_angle_linear_growth
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-01T21:28:16.247594+00:00
-- url     : https://prove2.me/submissions/a53ded56-964f-4592-8a07-e603c3868bf4

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation
import Theorems.Thm_BirkhoffGlobalSection_ambient_rotation_product_slit
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic


/-!
# Linear growth of the ambient angle for the saddle-center coefficient

Let `A = qI · B`. Its spectrum is `±iω, ±λ`, with eigenvectors `e₁, e₂, f₁, f₂`.

1. **Krein sign.** From `A e₁ = ω e₂` we get `B e₁ = -ω qI e₂`, so
   `B(e₁,e₁) = B(e₂,e₂) = ω κ` with `κ = -Ω(e₁,e₂)`, and `B(e₁,e₂) = 0`. The form `B` is
   positive definite on `{v₀ = 0}` (it equals `7v₁² + (v₁-v₂)² + v₃²` there). The plane
   `span(e₁,e₂)` meets that hyperplane, hence `κ > 0`.
2. **Symplectic normal form.** The elliptic and hyperbolic planes are `Ω`-orthogonal, and
   `Ω(f₁,f₂) ≠ 0` because the eigenvectors span. Rescaling gives a symplectic basis
   `u₁ = e₁/√κ`, `w₁ = -e₂/√κ`, `u₂`, `w₂`. Let `P` send the standard basis to it, with
   explicit inverse `Q`. Then `A P = P N` for the normal form `N`, and
   `Φ₀(t) = P ∘ M(t-a) ∘ Q` solves the equation, where `M(s)` rotates the `(q₁,p₁)` plane
   by `ωs` and boosts the `(q₂,p₂)` plane. Its ambient determinant is
   `cosh(λs) e^{iωs}`.
3. **Angle.** By `ambient_rotation_product_slit`, `Q₁ = d(P∘(M∘Q))·conj(dP)·conj(d(M∘Q))` and
   `Q₂ = d(M∘Q)·conj(dM)·conj(dQ)` lie in the slit plane, and
   `Q₁ Q₂ dM = dΦ₀ · conj(dP) conj(dQ) · |d(M∘Q)|² |dM|²`. Hence
   `α₀ = arg Q₁ + arg Q₂ + ω(t-a) - arg(conj(dP) conj(dQ))` is a continuous polar angle
   of `dΦ₀`. Its increment over `[a, a+L]` exceeds `ωL - 4π`.

The coordinate and determinant lemmas are copied from the accepted proof of
`BirkhoffGlobalSection.ambient_rotation_angle_exists`.
-/

open BirkhoffGlobalSection
open scoped Matrix

set_option autoImplicit false

/-! ### Coordinates -/

/-- The symplectic pairing `x ⬝ᵥ qI y` in coordinates. -/
private lemma omegaQ (x y : Phase) :
    x ⬝ᵥ TangentialHessian.qI.mulVec y = x 0 * y 2 + x 1 * y 3 - x 2 * y 0 - x 3 * y 1 := by
  simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

private lemma qI_apply (w : Phase) :
    TangentialHessian.qI.mulVec w = ![w 2, w 3, -w 0, -w 1] := by
  funext i; fin_cases i <;> simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The ambient determinant in terms of the matrix entries. -/
private lemma ambientRotationDet_eq (M : Phase →L[ℝ] Phase) :
    ambientRotationDet M =
      (⟨(M (coordinateVector 0) 0 + M (coordinateVector 2) 2) / 2,
          (M (coordinateVector 2) 0 - M (coordinateVector 0) 2) / 2⟩ : ℂ) *
        ⟨(M (coordinateVector 1) 1 + M (coordinateVector 3) 3) / 2,
          (M (coordinateVector 3) 1 - M (coordinateVector 1) 3) / 2⟩ -
      (⟨(M (coordinateVector 1) 0 + M (coordinateVector 3) 2) / 2,
          (M (coordinateVector 3) 0 - M (coordinateVector 1) 2) / 2⟩ : ℂ) *
        ⟨(M (coordinateVector 0) 1 + M (coordinateVector 2) 3) / 2,
          (M (coordinateVector 2) 1 - M (coordinateVector 0) 3) / 2⟩ := by
  unfold ambientRotationDet
  rw [Matrix.det_fin_two]
  rfl

private lemma continuous_mk' {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => (⟨f x, g x⟩ : ℂ)) := by
  have : (fun x => (⟨f x, g x⟩ : ℂ)) = fun x => (f x : ℂ) + (g x : ℂ) * Complex.I := by
    funext x; apply Complex.ext <;> simp
  rw [this]
  exact (Complex.continuous_ofReal.comp hf).add
    ((Complex.continuous_ofReal.comp hg).mul continuous_const)

/-- The ambient determinant is continuous on the space of linear maps. -/
private lemma continuous_det :
    Continuous (fun M : Phase →L[ℝ] Phase => ambientRotationDet M) := by
  have hc : ∀ k i : Fin 4, Continuous fun M : Phase →L[ℝ] Phase => M (coordinateVector k) i :=
    fun k i => (continuous_apply i).comp (continuous_id.clm_apply continuous_const)
  simp only [ambientRotationDet_eq]
  refine ((continuous_mk' ?_ ?_).mul (continuous_mk' ?_ ?_)).sub
    ((continuous_mk' ?_ ?_).mul (continuous_mk' ?_ ?_)) <;>
    first
    | exact ((hc _ _).add (hc _ _)).div_const _
    | exact ((hc _ _).sub (hc _ _)).div_const _


/-! ### The symplectic pairing -/

private lemma omega_add_left (x y z : Phase) :
    (x + y) ⬝ᵥ TangentialHessian.qI.mulVec z =
      x ⬝ᵥ TangentialHessian.qI.mulVec z + y ⬝ᵥ TangentialHessian.qI.mulVec z :=
  add_dotProduct _ _ _

private lemma omega_anti (x y : Phase) :
    y ⬝ᵥ TangentialHessian.qI.mulVec x = -(x ⬝ᵥ TangentialHessian.qI.mulVec y) := by
  rw [omegaQ, omegaQ]; ring

private lemma omega_self (x : Phase) : x ⬝ᵥ TangentialHessian.qI.mulVec x = 0 := by
  rw [omegaQ]; ring

private lemma qI_qI (v : Phase) :
    TangentialHessian.qI.mulVec (TangentialHessian.qI.mulVec v) = -v := by
  rw [qI_apply, qI_apply]
  funext k
  fin_cases k <;> simp

/-- The coefficient matrix of the saddle-center system. -/
private def Bm : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1]

/-- The Hamiltonian field `x ↦ qI (B x)` is infinitesimally symplectic. -/
private lemma hamiltonian_B (x y : Phase) :
    TangentialHessian.qI.mulVec (Bm.mulVec x) ⬝ᵥ TangentialHessian.qI.mulVec y +
      x ⬝ᵥ TangentialHessian.qI.mulVec (TangentialHessian.qI.mulVec (Bm.mulVec y)) = 0 := by
  rw [omegaQ, omegaQ]
  simp [Bm, TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

/-! ### A symplectic change of basis and its inverse -/

/-- The linear map sending the standard symplectic basis to `u₁, u₂, w₁, w₂`. -/
private noncomputable def Pmap (u1 u2 w1 w2 : Phase) : Phase →L[ℝ] Phase :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).smulRight u1 +
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1).smulRight u2 +
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2).smulRight w1 +
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3).smulRight w2

private lemma Pmap_apply (u1 u2 w1 w2 v : Phase) :
    Pmap u1 u2 w1 w2 v = v 0 • u1 + v 1 • u2 + v 2 • w1 + v 3 • w2 := by
  simp [Pmap]

/-- The linear functional `v ↦ g ⬝ᵥ v`. -/
private noncomputable def gradCLM (g : Phase) : Phase →L[ℝ] ℝ :=
  ∑ i : Fin 4, g i • ContinuousLinearMap.proj i

private lemma gradCLM_apply (g v : Phase) : gradCLM g v = g ⬝ᵥ v := by
  simp [gradCLM, dotProduct]

/-- Symplectic coordinates with respect to `u₁, u₂, w₁, w₂`. -/
private noncomputable def Qmap (u1 u2 w1 w2 : Phase) : Phase →L[ℝ] Phase :=
  ContinuousLinearMap.pi ![gradCLM (TangentialHessian.qI.mulVec w1),
    gradCLM (TangentialHessian.qI.mulVec w2), -gradCLM (TangentialHessian.qI.mulVec u1),
    -gradCLM (TangentialHessian.qI.mulVec u2)]

private lemma Qmap_apply (u1 u2 w1 w2 v : Phase) :
    Qmap u1 u2 w1 w2 v = ![v ⬝ᵥ TangentialHessian.qI.mulVec w1,
      v ⬝ᵥ TangentialHessian.qI.mulVec w2, -(v ⬝ᵥ TangentialHessian.qI.mulVec u1),
      -(v ⬝ᵥ TangentialHessian.qI.mulVec u2)] := by
  funext k
  fin_cases k <;> simp [Qmap, gradCLM_apply, dotProduct_comm]

section Basis

variable {u1 u2 w1 w2 : Phase}
  (h11 : u1 ⬝ᵥ TangentialHessian.qI.mulVec w1 = 1)
  (h22 : u2 ⬝ᵥ TangentialHessian.qI.mulVec w2 = 1)
  (hu12 : u1 ⬝ᵥ TangentialHessian.qI.mulVec u2 = 0)
  (hw12 : w1 ⬝ᵥ TangentialHessian.qI.mulVec w2 = 0)
  (hu1w2 : u1 ⬝ᵥ TangentialHessian.qI.mulVec w2 = 0)
  (hu2w1 : u2 ⬝ᵥ TangentialHessian.qI.mulVec w1 = 0)
include h11 h22 hu12 hw12 hu1w2 hu2w1

private lemma QP_id (v : Phase) : Qmap u1 u2 w1 w2 (Pmap u1 u2 w1 w2 v) = v := by
  rw [Qmap_apply, Pmap_apply]
  have a1 := omega_anti u1 u2; have a2 := omega_anti w1 w2
  have a3 := omega_anti u1 w2; have a4 := omega_anti u2 w1
  have a5 := omega_anti u1 w1; have a6 := omega_anti u2 w2
  have s1 := omega_self u1; have s2 := omega_self u2
  have s3 := omega_self w1; have s4 := omega_self w2
  funext k
  fin_cases k <;>
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
    rw [h11, h22, hu12, hw12, hu1w2, hu2w1] at * <;>
    simp only [a1, a2, a3, a4, a5, a6, s1, s2, s3, s4, h11, h22, hu12, hw12, hu1w2, hu2w1] <;>
    ring

private lemma PQ_id (v : Phase) : Pmap u1 u2 w1 w2 (Qmap u1 u2 w1 w2 v) = v := by
  have hinj : Function.Injective (Pmap u1 u2 w1 w2 : Phase →ₗ[ℝ] Phase) := by
    intro x y h
    have := congrArg (Qmap u1 u2 w1 w2) h
    simpa [QP_id h11 h22 hu12 hw12 hu1w2 hu2w1] using this
  obtain ⟨x, hx⟩ := LinearMap.injective_iff_surjective.1 hinj v
  have hx' : Pmap u1 u2 w1 w2 x = v := hx
  rw [← hx', QP_id h11 h22 hu12 hw12 hu1w2 hu2w1]

private lemma P_symp (v w : Phase) :
    Pmap u1 u2 w1 w2 v ⬝ᵥ TangentialHessian.qI.mulVec (Pmap u1 u2 w1 w2 w) =
      v ⬝ᵥ TangentialHessian.qI.mulVec w := by
  rw [Pmap_apply, Pmap_apply, omegaQ v w]
  have a1 := omega_anti u1 u2; have a2 := omega_anti w1 w2
  have a3 := omega_anti u1 w2; have a4 := omega_anti u2 w1
  have a5 := omega_anti u1 w1; have a6 := omega_anti u2 w2
  have s1 := omega_self u1; have s2 := omega_self u2
  have s3 := omega_self w1; have s4 := omega_self w2
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [a1, a2, a3, a4, a5, a6, s1, s2, s3, s4, h11, h22, hu12, hw12, hu1w2, hu2w1]
  ring

private lemma Q_symp (v w : Phase) :
    Qmap u1 u2 w1 w2 v ⬝ᵥ TangentialHessian.qI.mulVec (Qmap u1 u2 w1 w2 w) =
      v ⬝ᵥ TangentialHessian.qI.mulVec w := by
  rw [← P_symp h11 h22 hu12 hw12 hu1w2 hu2w1, PQ_id h11 h22 hu12 hw12 hu1w2 hu2w1,
    PQ_id h11 h22 hu12 hw12 hu1w2 hu2w1]

end Basis

/-! ### The normal-form flow -/

private noncomputable def Kc : Phase →L[ℝ] Phase :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, 0, ContinuousLinearMap.proj 2, 0]

private noncomputable def Ks : Phase →L[ℝ] Phase :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 2, 0, -ContinuousLinearMap.proj 0, 0]

private noncomputable def Ke : Phase →L[ℝ] Phase :=
  ContinuousLinearMap.pi ![0, ContinuousLinearMap.proj 1, 0, 0]

private noncomputable def Kf : Phase →L[ℝ] Phase :=
  ContinuousLinearMap.pi ![0, 0, 0, ContinuousLinearMap.proj 3]

/-- Rotation by `ω s` in the `(q₁,p₁)` plane, hyperbolic in the `(q₂,p₂)` plane. -/
private noncomputable def Mmap (ω lam s : ℝ) : Phase →L[ℝ] Phase :=
  Real.cos (ω * s) • Kc + Real.sin (ω * s) • Ks + Real.exp (lam * s) • Ke +
    Real.exp (-(lam * s)) • Kf

private lemma Mmap_apply (ω lam s : ℝ) (v : Phase) :
    Mmap ω lam s v = ![Real.cos (ω * s) * v 0 + Real.sin (ω * s) * v 2,
      Real.exp (lam * s) * v 1, -Real.sin (ω * s) * v 0 + Real.cos (ω * s) * v 2,
      Real.exp (-(lam * s)) * v 3] := by
  funext k
  fin_cases k <;> simp [Mmap, Kc, Ks, Ke, Kf] <;> ring

private lemma continuous_Mmap (ω lam a : ℝ) : Continuous fun t => Mmap ω lam (t - a) := by
  unfold Mmap
  fun_prop

private lemma Mmap_zero (ω lam : ℝ) : Mmap ω lam 0 = ContinuousLinearMap.id ℝ Phase := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [Mmap_apply]
  funext k
  fin_cases k <;> simp

private lemma M_symp (ω lam s : ℝ) (v w : Phase) :
    Mmap ω lam s v ⬝ᵥ TangentialHessian.qI.mulVec (Mmap ω lam s w) =
      v ⬝ᵥ TangentialHessian.qI.mulVec w := by
  rw [omegaQ, omegaQ, Mmap_apply, Mmap_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have hcs := Real.cos_sq_add_sin_sq (ω * s)
  have he : Real.exp (lam * s) * Real.exp (-(lam * s)) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (v 0 * w 2 - v 2 * w 0) * hcs + (v 1 * w 3 - v 3 * w 1) * he

/-- The normal-form coefficient: rotation generator plus hyperbolic generator. -/
private def Nvec (ω lam : ℝ) (x : Phase) : Phase :=
  ![ω * x 2, lam * x 1, -ω * x 0, -lam * x 3]

private lemma M_deriv (ω lam a t : ℝ) (z : Phase) :
    HasDerivAt (fun τ => Mmap ω lam (τ - a) z) (Nvec ω lam (Mmap ω lam (t - a) z)) t := by
  have hθ : HasDerivAt (fun τ => ω * (τ - a)) ω t := by
    simpa using ((hasDerivAt_id t).sub_const a).const_mul ω
  have hl : HasDerivAt (fun τ => lam * (τ - a)) lam t := by
    simpa using ((hasDerivAt_id t).sub_const a).const_mul lam
  have hc := (Real.hasDerivAt_cos _).comp t hθ
  have hs := (Real.hasDerivAt_sin _).comp t hθ
  have he1 := (Real.hasDerivAt_exp _).comp t hl
  have he2 := (Real.hasDerivAt_exp _).comp t hl.neg
  simp only [Function.comp_def] at hc hs he1 he2
  rw [hasDerivAt_pi]
  intro k
  fin_cases k
  · refine ((hc.mul_const (z 0)).add (hs.mul_const (z 2))).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · exact Filter.Eventually.of_forall fun τ => by simp [Mmap_apply]
    · simp [Nvec, Mmap_apply]; ring
  · refine (he1.mul_const (z 1)).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · exact Filter.Eventually.of_forall fun τ => by simp [Mmap_apply]
    · simp [Nvec, Mmap_apply]; ring
  · refine ((hs.neg.mul_const (z 0)).add (hc.mul_const (z 2))).congr_of_eventuallyEq ?_
      |>.congr_deriv ?_
    · exact Filter.Eventually.of_forall fun τ => by simp [Mmap_apply]
    · simp [Nvec, Mmap_apply]; ring
  · refine (he2.mul_const (z 3)).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · exact Filter.Eventually.of_forall fun τ => by simp [Mmap_apply]
    · simp [Nvec, Mmap_apply]; ring

private lemma M_det (ω lam s : ℝ) :
    ambientRotationDet (Mmap ω lam s) =
      ⟨(Real.exp (lam * s) + Real.exp (-(lam * s))) / 2 * Real.cos (ω * s),
        (Real.exp (lam * s) + Real.exp (-(lam * s))) / 2 * Real.sin (ω * s)⟩ := by
  rw [ambientRotationDet_eq]
  simp only [Mmap_apply]
  apply Complex.ext <;> simp [coordinateVector] <;> ring

/-! ### The intertwining relation -/

private lemma AP_eq {ω lam : ℝ} {u1 u2 w1 w2 : Phase}
    (hu1 : TangentialHessian.qI.mulVec (Bm.mulVec u1) = -ω • w1)
    (hw1 : TangentialHessian.qI.mulVec (Bm.mulVec w1) = ω • u1)
    (hu2 : TangentialHessian.qI.mulVec (Bm.mulVec u2) = lam • u2)
    (hw2 : TangentialHessian.qI.mulVec (Bm.mulVec w2) = -lam • w2) (v : Phase) :
    TangentialHessian.qI.mulVec (Bm.mulVec (Pmap u1 u2 w1 w2 v)) =
      Pmap u1 u2 w1 w2 (Nvec ω lam v) := by
  rw [Pmap_apply, Pmap_apply]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hu1, hw1, hu2, hw2]
  simp only [Nvec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  module

/-! ### Spectral facts from the hypotheses -/

private lemma B_quad_pos (v : Phase) (hv0 : v 0 = 0) (hv : v ≠ 0) :
    0 < v ⬝ᵥ Bm.mulVec v := by
  have key : v ⬝ᵥ Bm.mulVec v = 7 * v 1 ^ 2 + (v 1 - v 2) ^ 2 + v 3 ^ 2 := by
    simp [Bm, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hv0]
    ring
  rw [key]
  by_contra h
  push_neg at h
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 1 - v 2), sq_nonneg (v 3), sq_nonneg (v 1)]
  have h3 : v 3 = 0 := by nlinarith [sq_nonneg (v 1 - v 2), sq_nonneg (v 3), sq_nonneg (v 1)]
  have h2 : v 2 = 0 := by
    rw [h1] at h; nlinarith [sq_nonneg (v 2), sq_nonneg (v 3)]
  apply hv
  funext k
  fin_cases k <;> simp [hv0, h1, h2, h3]

private lemma of_qI_eq {y z : Phase} (h : TangentialHessian.qI.mulVec y = z) :
    y = -TangentialHessian.qI.mulVec z := by
  rw [← h, qI_qI, neg_neg]

/-! ### The theorem -/

theorem solution
    (ω lam : ℝ) (hω : 0 < ω) (hlam : 0 < lam)
    (e₁ e₂ f₁ f₂ : Phase)
    (he₁ : TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec e₁)) = ω • e₂)
    (he₂ : TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec e₂)) = -ω • e₁)
    (hf₁ : TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec f₁)) = lam • f₁)
    (hf₂ : TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec f₂)) = -lam • f₂)
    (hindep : LinearIndependent ℝ ![e₁, e₂, f₁, f₂]) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C₀ : ℝ, ∀ a L : ℝ,
      ∃ (Φ0 : ℝ → (Phase →L[ℝ] Phase)) (α0 : ℝ → ℝ),
        Φ0 a = ContinuousLinearMap.id ℝ Phase ∧
        (∀ t ∈ Set.Icc a (a + L), ∀ v : Phase,
          HasDerivAt (fun τ => Φ0 τ v)
            (TangentialHessian.qI.mulVec
              ((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
                Matrix (Fin 4) (Fin 4) ℝ).mulVec (Φ0 t v))) t) ∧
        ContinuousOn α0 (Set.Icc a (a + L)) ∧
        (∀ t ∈ Set.Icc a (a + L), ∃ ρ : ℝ, 0 < ρ ∧
          ambientRotationDet (Φ0 t) = ⟨ρ * Real.cos (α0 t), ρ * Real.sin (α0 t)⟩) ∧
        c₀ * L - C₀ < α0 (a + L) - α0 a := by
  have he1 : TangentialHessian.qI.mulVec (Bm.mulVec e₁) = ω • e₂ := he₁
  have he2 : TangentialHessian.qI.mulVec (Bm.mulVec e₂) = -ω • e₁ := he₂
  have hf1 : TangentialHessian.qI.mulVec (Bm.mulVec f₁) = lam • f₁ := hf₁
  have hf2 : TangentialHessian.qI.mulVec (Bm.mulVec f₂) = -lam • f₂ := hf₂
  -- the quadratic form on the elliptic plane
  have hBe1 := of_qI_eq he1
  have hBe2 := of_qI_eq he2
  set κ := -(e₁ ⬝ᵥ TangentialHessian.qI.mulVec e₂) with hκ
  have hB11 : e₁ ⬝ᵥ Bm.mulVec e₁ = ω * κ := by
    rw [hBe1, Matrix.mulVec_smul, dotProduct_neg, dotProduct_smul, smul_eq_mul, hκ]; ring
  have hB22 : e₂ ⬝ᵥ Bm.mulVec e₂ = ω * κ := by
    rw [hBe2, Matrix.mulVec_smul, dotProduct_neg, dotProduct_smul, smul_eq_mul,
      omega_anti e₁ e₂, hκ]; ring
  have hB12 : e₁ ⬝ᵥ Bm.mulVec e₂ = 0 := by
    rw [hBe2, Matrix.mulVec_smul, dotProduct_neg, dotProduct_smul, smul_eq_mul, omega_self]
    ring
  have hB21 : e₂ ⬝ᵥ Bm.mulVec e₁ = 0 := by
    rw [hBe1, Matrix.mulVec_smul, dotProduct_neg, dotProduct_smul, smul_eq_mul, omega_self]
    ring
  have hli := Fintype.linearIndependent_iff.1 hindep
  have he1ne : e₁ ≠ 0 := by simpa using hindep.ne_zero 0
  have hf1ne : f₁ ≠ 0 := by simpa using hindep.ne_zero 2
  -- the Krein sign: the form `B` is positive on the elliptic plane
  have hκpos : 0 < κ := by
    by_contra hκle
    push_neg at hκle
    set p := e₁ 0
    set q := e₂ 0
    set v := q • e₁ - p • e₂ with hv
    have hv0 : v 0 = 0 := by simp [hv, p, q]; ring
    have hvB : v ⬝ᵥ Bm.mulVec v = (q ^ 2 + p ^ 2) * (ω * κ) := by
      simp only [hv, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, hB11, hB22, hB12, hB21]
      ring
    by_cases hvz : v = 0
    · have hcoef := hli ![q, -p, 0, 0] (by
        simp only [Fin.sum_univ_four]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three]
        rw [← hvz, hv]; module)
      have hq : q = 0 := by simpa using hcoef 0
      have hp : p = 0 := by simpa using hcoef 1
      have := B_quad_pos e₁ hp he1ne
      rw [hB11] at this
      nlinarith
    · have := B_quad_pos v hv0 hvz
      rw [hvB] at this
      have hle : (q ^ 2 + p ^ 2) * (ω * κ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (mul_nonpos_of_nonneg_of_nonpos hω.le hκle)
      linarith
  -- symplectic orthogonality of the elliptic and hyperbolic planes
  have ham := hamiltonian_B
  have c11 : e₁ ⬝ᵥ TangentialHessian.qI.mulVec f₁ = 0 := by
    have h1 := ham e₁ f₁; have h2 := ham e₂ f₁
    rw [he1, hf1] at h1; rw [he2, hf1] at h2
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1 h2
    have h3 : (lam ^ 2 + ω ^ 2) * (e₁ ⬝ᵥ TangentialHessian.qI.mulVec f₁) = 0 := by
      linear_combination lam * h1 - ω * h2
    rcases mul_eq_zero.1 h3 with h | h
    · nlinarith
    · exact h
  have c21 : e₂ ⬝ᵥ TangentialHessian.qI.mulVec f₁ = 0 := by
    have h1 := ham e₁ f₁
    rw [he1, hf1] at h1
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, c11] at h1
    have : ω * (e₂ ⬝ᵥ TangentialHessian.qI.mulVec f₁) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  have c12 : e₁ ⬝ᵥ TangentialHessian.qI.mulVec f₂ = 0 := by
    have h1 := ham e₁ f₂; have h2 := ham e₂ f₂
    rw [he1, hf2] at h1; rw [he2, hf2] at h2
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1 h2
    have h3 : (lam ^ 2 + ω ^ 2) * (e₁ ⬝ᵥ TangentialHessian.qI.mulVec f₂) = 0 := by
      linear_combination -lam * h1 - ω * h2
    rcases mul_eq_zero.1 h3 with h | h
    · nlinarith
    · exact h
  have c22 : e₂ ⬝ᵥ TangentialHessian.qI.mulVec f₂ = 0 := by
    have h1 := ham e₁ f₂
    rw [he1, hf2] at h1
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, c12] at h1
    have : ω * (e₂ ⬝ᵥ TangentialHessian.qI.mulVec f₂) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  -- the hyperbolic pairing does not vanish
  set m := f₁ ⬝ᵥ TangentialHessian.qI.mulVec f₂ with hm
  have hm0 : m ≠ 0 := by
    intro hm0
    have hspan := hindep.span_eq_top_of_card_eq_finrank' (by simp)
    have hall : ∀ w : Phase, f₁ ⬝ᵥ TangentialHessian.qI.mulVec w = 0 := by
      intro w
      have hw : w ∈ Submodule.span ℝ (Set.range ![e₁, e₂, f₁, f₂]) := by
        rw [hspan]; trivial
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw
      rw [← hg]
      simp only [Fin.sum_univ_four, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
        dotProduct_smul, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [omega_anti e₁ f₁, omega_anti e₂ f₁, c11, c21, omega_self, ← hm, hm0]
      ring
    have h := hall (TangentialHessian.qI.mulVec f₁)
    rw [qI_qI, dotProduct_neg, neg_eq_zero, dotProduct_self_eq_zero] at h
    exact hf1ne h
  -- the normalized symplectic basis
  set sκ := Real.sqrt κ with hsκ
  have hsκ0 : 0 < sκ := Real.sqrt_pos.2 hκpos
  have hsκ2 : sκ * sκ = κ := Real.mul_self_sqrt hκpos.le
  set sm := Real.sqrt |m| with hsm
  have hm1 : 0 < |m| := abs_pos.2 hm0
  have hsm0 : 0 < sm := Real.sqrt_pos.2 hm1
  have hsm2 : sm * sm = |m| := Real.mul_self_sqrt hm1.le
  set u1 := (1 / sκ) • e₁ with hu1
  set w1 := (-1 / sκ) • e₂ with hw1
  set u2 := (1 / sm) • f₁ with hu2
  set w2 := (m / |m| / sm) • f₂ with hw2
  have hpair : ∀ (a b : ℝ) (x y : Phase),
      (a • x) ⬝ᵥ TangentialHessian.qI.mulVec (b • y) =
        a * b * (x ⬝ᵥ TangentialHessian.qI.mulVec y) := by
    intro a b x y
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
  have h11 : u1 ⬝ᵥ TangentialHessian.qI.mulVec w1 = 1 := by
    rw [hu1, hw1, hpair, ← neg_neg (e₁ ⬝ᵥ _), ← hκ]
    field_simp
    nlinarith [hsκ2]
  have h22 : u2 ⬝ᵥ TangentialHessian.qI.mulVec w2 = 1 := by
    rw [hu2, hw2, hpair, ← hm]
    have hmm : m * m = |m| * |m| := by rw [← abs_mul_abs_self m]
    field_simp
    nlinarith [hsm2, hmm]
  have hu12 : u1 ⬝ᵥ TangentialHessian.qI.mulVec u2 = 0 := by rw [hu1, hu2, hpair, c11]; ring
  have hw12 : w1 ⬝ᵥ TangentialHessian.qI.mulVec w2 = 0 := by rw [hw1, hw2, hpair, c22]; ring
  have hu1w2 : u1 ⬝ᵥ TangentialHessian.qI.mulVec w2 = 0 := by rw [hu1, hw2, hpair, c12]; ring
  have hu2w1 : u2 ⬝ᵥ TangentialHessian.qI.mulVec w1 = 0 := by
    rw [hu2, hw1, hpair, omega_anti e₂ f₁, c21]; ring
  -- eigen relations for the normalized basis
  have hAu1 : TangentialHessian.qI.mulVec (Bm.mulVec u1) = -ω • w1 := by
    rw [hu1, hw1, Matrix.mulVec_smul, Matrix.mulVec_smul, he1, smul_smul, smul_smul]
    congr 1; field_simp
  have hAw1 : TangentialHessian.qI.mulVec (Bm.mulVec w1) = ω • u1 := by
    rw [hu1, hw1, Matrix.mulVec_smul, Matrix.mulVec_smul, he2, smul_smul, smul_smul]
    congr 1; field_simp
  have hAu2 : TangentialHessian.qI.mulVec (Bm.mulVec u2) = lam • u2 := by
    rw [hu2, Matrix.mulVec_smul, Matrix.mulVec_smul, hf1, smul_smul, smul_smul, mul_comm]
  have hAw2 : TangentialHessian.qI.mulVec (Bm.mulVec w2) = -lam • w2 := by
    rw [hw2, Matrix.mulVec_smul, Matrix.mulVec_smul, hf2, smul_smul, smul_smul, mul_comm]
  set P := Pmap u1 u2 w1 w2 with hP
  set Q := Qmap u1 u2 w1 w2 with hQ
  have hPQ := PQ_id h11 h22 hu12 hw12 hu1w2 hu2w1
  have hPs := P_symp h11 h22 hu12 hw12 hu1w2 hu2w1
  have hQs := Q_symp h11 h22 hu12 hw12 hu1w2 hu2w1
  -- the constants
  refine ⟨ω, hω, 4 * Real.pi, fun a L => ?_⟩
  set Mt : ℝ → (Phase →L[ℝ] Phase) := fun t => Mmap ω lam (t - a) with hMt
  set Φ0 : ℝ → (Phase →L[ℝ] Phase) := fun t => P.comp ((Mt t).comp Q) with hΦ0
  have hMQs : ∀ t, ∀ v w : Phase, (Mt t).comp Q v ⬝ᵥ
      TangentialHessian.qI.mulVec ((Mt t).comp Q w) = v ⬝ᵥ TangentialHessian.qI.mulVec w := by
    intro t v w
    simp only [ContinuousLinearMap.comp_apply, hMt]
    rw [M_symp, hQs]
  set Q1 : ℝ → ℂ := fun t => ambientRotationDet (Φ0 t) *
      (starRingEnd ℂ) (ambientRotationDet P) *
      (starRingEnd ℂ) (ambientRotationDet ((Mt t).comp Q)) with hQ1
  set Q2 : ℝ → ℂ := fun t => ambientRotationDet ((Mt t).comp Q) *
      (starRingEnd ℂ) (ambientRotationDet (Mt t)) *
      (starRingEnd ℂ) (ambientRotationDet Q) with hQ2
  set K : ℂ := (starRingEnd ℂ) (ambientRotationDet P) *
      (starRingEnd ℂ) (ambientRotationDet Q) with hK
  have hQ1s : ∀ t, Q1 t ∈ Complex.slitPlane := fun t =>
    ambient_rotation_product_slit P ((Mt t).comp Q) hPs (hMQs t)
  have hQ2s : ∀ t, Q2 t ∈ Complex.slitPlane := fun t =>
    ambient_rotation_product_slit (Mt t) Q (fun v w => M_symp ω lam (t - a) v w) hQs
  set α0 : ℝ → ℝ := fun t => Complex.arg (Q1 t) + Complex.arg (Q2 t) + ω * (t - a) -
    Complex.arg K with hα0
  refine ⟨Φ0, α0, ?_, ?_, ?_, ?_, ?_⟩
  · -- initial value
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [hΦ0, hMt, sub_self, Mmap_zero, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply]
    exact hPQ v
  · -- the variational equation
    intro t _ v
    have h := (P.hasFDerivAt).comp_hasDerivAt t (M_deriv ω lam a t (Q v))
    refine h.congr_deriv ?_
    show P (Nvec ω lam (Mmap ω lam (t - a) (Q v))) =
      TangentialHessian.qI.mulVec (Bm.mulVec (P (Mmap ω lam (t - a) (Q v))))
    rw [AP_eq hAu1 hAw1 hAu2 hAw2]
  · -- continuity of the angle
    have hMc := continuous_Mmap ω lam a
    have hQ1c : Continuous Q1 := by
      simp only [hQ1, hΦ0]
      exact ((continuous_det.comp (continuous_const.clm_comp (hMc.clm_comp continuous_const))).mul
        continuous_const).mul
        (Complex.continuous_conj.comp (continuous_det.comp (hMc.clm_comp continuous_const)))
    have hQ2c : Continuous Q2 := by
      simp only [hQ2]
      exact ((continuous_det.comp (hMc.clm_comp continuous_const)).mul
        (Complex.continuous_conj.comp (continuous_det.comp hMc))).mul continuous_const
    have harg : ∀ {f : ℝ → ℂ}, Continuous f → (∀ t, f t ∈ Complex.slitPlane) →
        Continuous fun t => Complex.arg (f t) := fun hf hs =>
      continuous_iff_continuousAt.2 fun t =>
        (Complex.continuousAt_arg (hs t)).comp hf.continuousAt
    refine Continuous.continuousOn ?_
    simp only [hα0]
    exact (((harg hQ1c hQ1s).add (harg hQ2c hQ2s)).add (by fun_prop)).sub continuous_const
  · -- the polar form
    intro t _
    set D := ambientRotationDet (Φ0 t)
    set q1 := Q1 t
    set q2 := Q2 t
    set dm := ambientRotationDet (Mt t)
    set dmq := ambientRotationDet ((Mt t).comp Q)
    set ch := (Real.exp (lam * (t - a)) + Real.exp (-(lam * (t - a)))) / 2 with hch
    have hch0 : 0 < ch := by positivity
    have hq1 : q1 ≠ 0 := Complex.slitPlane_ne_zero (hQ1s t)
    have hq2 : q2 ≠ 0 := Complex.slitPlane_ne_zero (hQ2s t)
    have hdmq : dmq ≠ 0 := fun h => hq2 (by simp [q2, hQ2, dmq, h])
    have hdm : dm ≠ 0 := fun h => hq2 (by simp [q2, hQ2, dm, h])
    have hK0 : K ≠ 0 := by
      intro h
      rcases mul_eq_zero.1 h with h1 | h1
      · exact hq1 (by simp [q1, hQ1, h1])
      · exact hq2 (by simp [q2, hQ2, h1])
    have hdmpol : dm = (ch : ℂ) * Complex.exp (↑(ω * (t - a)) * Complex.I) := by
      have hd := M_det ω lam (t - a)
      simp only [dm, hMt]
      rw [hd]
      apply Complex.ext <;>
        simp only [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
          Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, hch] <;> ring
    set r : ℝ := Complex.normSq dmq * Complex.normSq dm with hr
    have hr0 : 0 < r := mul_pos (Complex.normSq_pos.2 hdmq) (Complex.normSq_pos.2 hdm)
    have hid : q1 * q2 * dm = D * K * (r : ℂ) := by
      have e1 := Complex.mul_conj dmq
      have e2 := Complex.mul_conj dm
      calc q1 * q2 * dm = D * K * (dmq * (starRingEnd ℂ) dmq) * (dm * (starRingEnd ℂ) dm) := by
            simp only [q1, q2, hQ1, hQ2, hK, D, dmq, dm]; ring
        _ = D * K * (r : ℂ) := by rw [e1, e2, hr]; push_cast; ring
    set R : ℝ := ‖q1‖ * ‖q2‖ * ch / (‖K‖ * r) with hR
    have hR0 : 0 < R := by
      have := norm_pos_iff.2 hq1; have := norm_pos_iff.2 hq2; have := norm_pos_iff.2 hK0
      positivity
    have hDpol : D = (R : ℂ) * Complex.exp (↑(α0 t) * Complex.I) := by
      have hKr : K * (r : ℂ) ≠ 0 := mul_ne_zero hK0 (by exact_mod_cast hr0.ne')
      apply mul_right_cancel₀ hKr
      rw [show D * (K * (r : ℂ)) = q1 * q2 * dm by rw [hid]; ring]
      conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I K]
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I q1, ← Complex.norm_mul_exp_arg_mul_I q2,
        hdmpol]
      have hsplit : (↑(α0 t) : ℂ) * Complex.I = ↑(Complex.arg q1) * Complex.I +
          ↑(Complex.arg q2) * Complex.I + ↑(ω * (t - a)) * Complex.I -
          ↑(Complex.arg K) * Complex.I := by
        simp only [hα0, q1, q2]; push_cast; ring
      rw [hsplit, Complex.exp_sub, Complex.exp_add, Complex.exp_add]
      have hKn : (‖K‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hK0).ne'
      have hrn : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
      have hE : Complex.exp (↑(Complex.arg K) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
      simp only [hR]
      push_cast
      field_simp
    refine ⟨R, hR0, ?_⟩
    rw [hDpol]
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring
  · -- the growth estimate
    simp only [hα0]
    have h1 := Complex.neg_pi_lt_arg (Q1 a)
    have h2 := Complex.arg_le_pi (Q1 (a + L))
    have h3 := Complex.neg_pi_lt_arg (Q2 a)
    have h4 := Complex.arg_le_pi (Q2 (a + L))
    have h5 := Complex.neg_pi_lt_arg (Q1 (a + L))
    have h6 := Complex.neg_pi_lt_arg (Q2 (a + L))
    have h7 := Complex.arg_le_pi (Q1 a)
    have h8 := Complex.arg_le_pi (Q2 a)
    linarith [Real.pi_pos]
