-- Prove2me | solution 1 for BirkhoffGlobalSection.ambient_rotation_angle_exists
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-30T23:40:54.27919+00:00
-- url     : https://prove2.me/submissions/74651998-3a40-44af-90c6-a3ec8bb438b2

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# A continuous ambient rotation angle exists along any variational flow

Let `F` be smooth along `x` and let `Y` solve `Y' = D X_F (x t) ∘ Y` with `Y 0 = id`.

1. `D X_F (p) = qI ∘ Hess F (p)`, and the Hessian of a `C²` function is symmetric. So the
   derivative of `ω(Y u, Y v)` vanishes, and every `Y t` is symplectic.
2. A symplectic map has ambient determinant of modulus at least one (the Gram identity
   `‖P u‖² = ‖u‖² + ‖K̄ u‖²` of the complex-linear and conjugate-linear parts). Hence
   `t ↦ ambientRotationDet (Y t)` is a continuous curve in `ℂ \ {0}`.
3. `ℝ` is simply connected and `Circle.exp` is a covering map, so the normalized curve
   lifts to a continuous angle.

The matrix lemmas of step 2 are copied from the accepted proof of
`BirkhoffGlobalSection.linear_system_rotation_perturbation`.
-/

open BirkhoffGlobalSection
open scoped ContDiff Matrix

set_option autoImplicit false

/-! ### Coordinates of the Hamiltonian structure -/

/-- The symplectic pairing `x ⬝ᵥ qI y` in coordinates. -/
private lemma omegaQ (x y : Phase) :
    x ⬝ᵥ TangentialHessian.qI.mulVec y = x 0 * y 2 + x 1 * y 3 - x 2 * y 0 - x 3 * y 1 := by
  simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

private lemma mulVec_apply4 (A : Matrix (Fin 4) (Fin 4) ℝ) (x : Phase) (i : Fin 4) :
    A.mulVec x i = A i 0 * x 0 + A i 1 * x 1 + A i 2 * x 2 + A i 3 * x 3 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]

private lemma qI0 (w : Phase) : TangentialHessian.qI.mulVec w 0 = w 2 := by
  simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
private lemma qI1 (w : Phase) : TangentialHessian.qI.mulVec w 1 = w 3 := by
  simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
private lemma qI2 (w : Phase) : TangentialHessian.qI.mulVec w 2 = -w 0 := by
  simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
private lemma qI3 (w : Phase) : TangentialHessian.qI.mulVec w 3 = -w 1 := by
  simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

private lemma qI_apply (w : Phase) :
    TangentialHessian.qI.mulVec w = ![w 2, w 3, -w 0, -w 1] := by
  funext i; fin_cases i <;> simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-! ### The ambient determinant -/

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

private lemma det_id : ambientRotationDet (ContinuousLinearMap.id ℝ Phase) = 1 := by
  rw [ambientRotationDet_eq]
  apply Complex.ext <;> simp (config := { decide := true }) [coordinateVector]

/-! ### Symplectic maps have ambient determinant of modulus at least one -/

/-- The squared Euclidean norm on `ℂ²`. -/
private def nsq (v : Fin 2 → ℂ) : ℝ :=
  (v 0).re ^ 2 + (v 0).im ^ 2 + (v 1).re ^ 2 + (v 1).im ^ 2

/-- The coordinate matrix of a linear map, `toMat Y i k = Y (e_k) i`. -/
private def toMat (Y : Phase →L[ℝ] Phase) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i k => Y (coordinateVector k) i

/-- Complex-linear part `(A + D + i (B - C)) / 2` of a real `4 × 4` matrix. -/
private noncomputable def Pm (Y : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨(Y 0 0 + Y 2 2) / 2, (Y 0 2 - Y 2 0) / 2⟩, ⟨(Y 0 1 + Y 2 3) / 2, (Y 0 3 - Y 2 1) / 2⟩;
     ⟨(Y 1 0 + Y 3 2) / 2, (Y 1 2 - Y 3 0) / 2⟩, ⟨(Y 1 1 + Y 3 3) / 2, (Y 1 3 - Y 3 1) / 2⟩]

/-- The entrywise conjugate of the conjugate-linear part of a real `4 × 4` matrix. -/
private noncomputable def Kb (Y : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨(Y 0 0 - Y 2 2) / 2, (Y 0 2 + Y 2 0) / 2⟩, ⟨(Y 0 1 - Y 2 3) / 2, (Y 0 3 + Y 2 1) / 2⟩;
     ⟨(Y 1 0 - Y 3 2) / 2, (Y 1 2 + Y 3 0) / 2⟩, ⟨(Y 1 1 - Y 3 3) / 2, (Y 1 3 + Y 3 1) / 2⟩]

private lemma acl_eq (Y : Phase →L[ℝ] Phase) : ambientComplexLinearPart Y = Pm (toMat Y) := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

private lemma symp_mat {Y : Phase →L[ℝ] Phase}
    (hY : ∀ u v : Phase,
      Y u ⬝ᵥ TangentialHessian.qI.mulVec (Y v) = u ⬝ᵥ TangentialHessian.qI.mulVec v) :
    (toMat Y).transpose * TangentialHessian.qI * toMat Y = TangentialHessian.qI := by
  ext k l
  have h := hY (coordinateVector k) (coordinateVector l)
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, toMat, Matrix.of_apply]
  simp only [dotProduct, Matrix.mulVec] at h
  rw [h]
  simp [coordinateVector]

/-- For a symplectic matrix, `‖P u‖² = ‖u‖² + ‖K̄ u‖²`. -/
private lemma col_identity {Y : Matrix (Fin 4) (Fin 4) ℝ}
    (hY : Y.transpose * TangentialHessian.qI * Y = TangentialHessian.qI) (u : Fin 2 → ℂ) :
    nsq (Pm Y *ᵥ u) = nsq u + nsq (Kb Y *ᵥ u) := by
  set x : Fin 4 → ℝ := ![(u 0).re, (u 1).re, -(u 0).im, -(u 1).im] with hx
  have key : nsq (Pm Y *ᵥ u) - nsq (Kb Y *ᵥ u) =
      -(x ⬝ᵥ (Y.transpose * TangentialHessian.qI * Y) *ᵥ (TangentialHessian.qI *ᵥ x)) := by
    simp [nsq, Pm, Kb, hx, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_four,
      Matrix.mul_apply, TangentialHessian.qI, Complex.mul_re, Complex.mul_im]
    ring
  rw [hY] at key
  have hq : x ⬝ᵥ TangentialHessian.qI *ᵥ (TangentialHessian.qI *ᵥ x) = -nsq u := by
    simp [nsq, hx, Matrix.mulVec, dotProduct, Fin.sum_univ_four, TangentialHessian.qI]
    ring
  linarith

/-- The Gram-determinant identity behind `|det P| ≥ 1`: if the Gram matrix of `P`
equals the identity plus the Gram matrix of `Q`, then `|det P|²` is
`1 + tr (Q* Q) + |det Q|²`. -/
private lemma lagrange_bound (p1 p2 q1 q2 r1 r2 s1 s2 k1 k2 l1 l2 m1 m2 n1 n2 : ℝ)
    (e0 : p1 ^ 2 + p2 ^ 2 + r1 ^ 2 + r2 ^ 2 = 1 + (k1 ^ 2 + k2 ^ 2 + m1 ^ 2 + m2 ^ 2))
    (e1 : q1 ^ 2 + q2 ^ 2 + s1 ^ 2 + s2 ^ 2 = 1 + (l1 ^ 2 + l2 ^ 2 + n1 ^ 2 + n2 ^ 2))
    (e2 : p1 * q1 + p2 * q2 + r1 * s1 + r2 * s2 = k1 * l1 + k2 * l2 + m1 * n1 + m2 * n2)
    (e3 : p1 * q2 - p2 * q1 + r1 * s2 - r2 * s1 = k1 * l2 - k2 * l1 + m1 * n2 - m2 * n1) :
    1 ≤ (p1 * s1 - p2 * s2 - (q1 * r1 - q2 * r2)) ^ 2 +
      (p1 * s2 + p2 * s1 - (q1 * r2 + q2 * r1)) ^ 2 := by
  have key : (p1 * s1 - p2 * s2 - (q1 * r1 - q2 * r2)) ^ 2 +
      (p1 * s2 + p2 * s1 - (q1 * r2 + q2 * r1)) ^ 2 =
      1 + (k1 ^ 2 + k2 ^ 2 + m1 ^ 2 + m2 ^ 2) + (l1 ^ 2 + l2 ^ 2 + n1 ^ 2 + n2 ^ 2) +
        ((k1 * n1 - k2 * n2 - (l1 * m1 - l2 * m2)) ^ 2 +
          (k1 * n2 + k2 * n1 - (l1 * m2 + l2 * m1)) ^ 2) := by
    linear_combination (q1 ^ 2 + q2 ^ 2 + s1 ^ 2 + s2 ^ 2) * e0 +
      (1 + (k1 ^ 2 + k2 ^ 2 + m1 ^ 2 + m2 ^ 2)) * e1 -
      (p1 * q1 + p2 * q2 + r1 * s1 + r2 * s2 + (k1 * l1 + k2 * l2 + m1 * n1 + m2 * n2)) * e2 -
      (p1 * q2 - p2 * q1 + r1 * s2 - r2 * s1 + (k1 * l2 - k2 * l1 + m1 * n2 - m2 * n1)) * e3
  rw [key]
  nlinarith [sq_nonneg k1, sq_nonneg k2, sq_nonneg m1, sq_nonneg m2, sq_nonneg l1,
    sq_nonneg l2, sq_nonneg n1, sq_nonneg n2,
    sq_nonneg (k1 * n1 - k2 * n2 - (l1 * m1 - l2 * m2)),
    sq_nonneg (k1 * n2 + k2 * n1 - (l1 * m2 + l2 * m1))]

private lemma normSq_det_ge_one (P Q : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ u : Fin 2 → ℂ, nsq (P *ᵥ u) = nsq u + nsq (Q *ᵥ u)) :
    1 ≤ Complex.normSq P.det := by
  have e0 : (P 0 0).re ^ 2 + (P 0 0).im ^ 2 + (P 1 0).re ^ 2 + (P 1 0).im ^ 2 =
      1 + ((Q 0 0).re ^ 2 + (Q 0 0).im ^ 2 + (Q 1 0).re ^ 2 + (Q 1 0).im ^ 2) := by
    have := h ![1, 0]
    simp [nsq, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
    linarith
  have e1 : (P 0 1).re ^ 2 + (P 0 1).im ^ 2 + (P 1 1).re ^ 2 + (P 1 1).im ^ 2 =
      1 + ((Q 0 1).re ^ 2 + (Q 0 1).im ^ 2 + (Q 1 1).re ^ 2 + (Q 1 1).im ^ 2) := by
    have := h ![0, 1]
    simp [nsq, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
    linarith
  have e2 : (P 0 0).re * (P 0 1).re + (P 0 0).im * (P 0 1).im +
      (P 1 0).re * (P 1 1).re + (P 1 0).im * (P 1 1).im =
      (Q 0 0).re * (Q 0 1).re + (Q 0 0).im * (Q 0 1).im +
      (Q 1 0).re * (Q 1 1).re + (Q 1 0).im * (Q 1 1).im := by
    have := h ![1, 1]
    simp [nsq, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
    linarith
  have e3 : (P 0 0).re * (P 0 1).im - (P 0 0).im * (P 0 1).re +
      (P 1 0).re * (P 1 1).im - (P 1 0).im * (P 1 1).re =
      (Q 0 0).re * (Q 0 1).im - (Q 0 0).im * (Q 0 1).re +
      (Q 1 0).re * (Q 1 1).im - (Q 1 0).im * (Q 1 1).re := by
    have := h ![1, Complex.I]
    simp [nsq, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
    linarith
  have hb := lagrange_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e0 e1 e2 e3
  rw [Matrix.det_fin_two, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  linarith

/-- A symplectic map has ambient determinant of modulus at least one. -/
private lemma one_le_norm_det {M : Phase →L[ℝ] Phase}
    (hM : ∀ u v : Phase,
      M u ⬝ᵥ TangentialHessian.qI.mulVec (M v) = u ⬝ᵥ TangentialHessian.qI.mulVec v) :
    1 ≤ ‖ambientRotationDet M‖ := by
  have h := normSq_det_ge_one (Pm (toMat M)) (Kb (toMat M)) (col_identity (symp_mat hM))
  unfold ambientRotationDet
  rw [acl_eq]
  have h2 := Complex.sq_norm (Pm (toMat M)).det
  have h3 := norm_nonneg (Pm (toMat M)).det
  by_contra hlt
  push Not at hlt
  nlinarith

/-! ### The variational coefficient is `qI` times a symmetric Hessian -/

/-- The Hessian matrix `H i j = D²F(p)(e_j, e_i)`. -/
private noncomputable def hessMat (F : Phase → ℝ) (p : Phase) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => fderiv ℝ (fderiv ℝ F) p (coordinateVector j) (coordinateVector i)

private lemma sum_coord (w : Phase) : w = ∑ j, w j • coordinateVector j := by
  funext k
  fin_cases k <;> simp [coordinateVector]

private lemma hessMat_symm {F : Phase → ℝ} {p : Phase} (hF : ContDiffAt ℝ ∞ F p) (i j : Fin 4) :
    hessMat F p i j = hessMat F p j i := by
  have hs := hF.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  simp only [hessMat, Matrix.of_apply]
  exact hs _ _

/-- The derivative of the Hamiltonian field is `qI ∘ Hess F`. -/
private lemma fderiv_hvf_apply {F : Phase → ℝ} {p : Phase} (hF : ContDiffAt ℝ ∞ F p)
    (w : Phase) :
    fderiv ℝ (hamiltonianVectorField F) p w =
      TangentialHessian.qI.mulVec ((hessMat F p).mulVec w) := by
  have hF2 : ContDiffAt ℝ 2 F p := hF.of_le (WithTop.coe_le_coe.2 le_top)
  have hdF : ContDiffAt ℝ 1 (fderiv ℝ F) p := hF2.fderiv_right (by norm_num)
  have hD : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) p) p :=
    (hdF.differentiableAt (by norm_num)).hasFDerivAt
  -- each coordinate `s ↦ ∂_j F (s)` has derivative `a ↦ D²F(p)(a, e_j)`
  have hpart : ∀ j : Fin 4, HasFDerivAt (fun s => partialDerivative F s j)
      ((fderiv ℝ (fderiv ℝ F) p).flip (coordinateVector j)) p := by
    intro j
    have h := hD.clm_apply (hasFDerivAt_const (coordinateVector j) p)
    simpa [partialDerivative] using h
  have hX : HasFDerivAt (hamiltonianVectorField F)
      (ContinuousLinearMap.pi ![(fderiv ℝ (fderiv ℝ F) p).flip (coordinateVector 2),
        (fderiv ℝ (fderiv ℝ F) p).flip (coordinateVector 3),
        -(fderiv ℝ (fderiv ℝ F) p).flip (coordinateVector 0),
        -(fderiv ℝ (fderiv ℝ F) p).flip (coordinateVector 1)]) p := by
    have e : hamiltonianVectorField F = fun s i =>
        (![fun s => partialDerivative F s 2, fun s => partialDerivative F s 3,
          fun s => -partialDerivative F s 0, fun s => -partialDerivative F s 1] :
            Fin 4 → Phase → ℝ) i s := by
      funext s i
      fin_cases i <;> rfl
    rw [e, hasFDerivAt_pi]
    intro i
    fin_cases i
    · exact hpart 2
    · exact hpart 3
    · exact (hpart 0).neg
    · exact (hpart 1).neg
  rw [hX.fderiv]
  have hlin : ∀ j : Fin 4, fderiv ℝ (fderiv ℝ F) p w (coordinateVector j) =
      ∑ k, hessMat F p j k * w k := by
    intro j
    conv_lhs => rw [sum_coord w]
    simp [hessMat, map_sum, map_smul, mul_comm]
  funext i
  fin_cases i <;>
    simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      ContinuousLinearMap.pi_apply, hlin]

/-! ### The variational flow is symplectic -/

private lemma symp_all {H : ℝ → Matrix (Fin 4) (Fin 4) ℝ}
    (hHs : ∀ t, ∀ i j : Fin 4, H t i j = H t j i)
    {Y : ℝ → (Phase →L[ℝ] Phase)} (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase)
    (hYd : ∀ t, ∀ v : Phase,
      HasDerivAt (fun τ => Y τ v) (TangentialHessian.qI.mulVec ((H t).mulVec (Y t v))) t) :
    ∀ t : ℝ, ∀ u v : Phase,
      Y t u ⬝ᵥ TangentialHessian.qI.mulVec (Y t v) = u ⬝ᵥ TangentialHessian.qI.mulVec v := by
  intro t u v
  set f : ℝ → ℝ := fun τ => Y τ u ⬝ᵥ TangentialHessian.qI.mulVec (Y τ v) with hf
  have hderiv : ∀ s, HasDerivAt f 0 s := by
    intro s
    have hc := hasDerivAt_pi.mp (hYd s u)
    have hd := hasDerivAt_pi.mp (hYd s v)
    have h := ((((hc 0).mul (hd 2)).add ((hc 1).mul (hd 3))).sub ((hc 2).mul (hd 0))).sub
      ((hc 3).mul (hd 1))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => ?_)
    · simp only [qI0, qI1, qI2, qI3]
      simp only [mulVec_apply4]
      have h01 := hHs s 0 1; have h02 := hHs s 0 2; have h03 := hHs s 0 3
      have h12 := hHs s 1 2; have h13 := hHs s 1 3; have h23 := hHs s 2 3
      rw [h01, h02, h03, h12, h13, h23]
      ring
    · simp only [hf, omegaQ, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  have hc := is_const_of_deriv_eq_zero (fun s => (hderiv s).differentiableAt)
    (fun s => (hderiv s).deriv) t 0
  rw [show Y t u ⬝ᵥ TangentialHessian.qI.mulVec (Y t v) = f t from rfl, hc]
  simp [hf, hY0]

/-! ### Continuous angles of nonvanishing curves -/

/-- A continuous nonvanishing curve in `ℂ` has a continuous polar angle. -/
private lemma exists_angle {d : ℝ → ℂ} (hd : Continuous d) (hne : ∀ t, d t ≠ 0) :
    ∃ α : ℝ → ℝ, Continuous α ∧ ∀ t : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
      d t = Complex.mk (ρ * Real.cos (α t)) (ρ * Real.sin (α t)) := by
  have hn : ∀ t, (‖d t‖ : ℂ) ≠ 0 := fun t => by
    exact_mod_cast (norm_ne_zero_iff.2 (hne t))
  have hmem : ∀ t, d t / ‖d t‖ ∈ Submonoid.unitSphere ℂ := fun t => by
    show d t / ‖d t‖ ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm,
      div_self (norm_ne_zero_iff.2 (hne t))]
  have hcont : Continuous fun t => d t / (‖d t‖ : ℂ) :=
    hd.div (Complex.continuous_ofReal.comp hd.norm) hn
  let u : C(ℝ, Circle) := ⟨fun t => ⟨d t / ‖d t‖, hmem t⟩, hcont.subtype_mk _⟩
  obtain ⟨e₀, he₀⟩ := Circle.exp_surjective (u 0)
  obtain ⟨F, ⟨-, hF⟩, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts u 0 e₀ he₀
  refine ⟨F, F.continuous, fun t => ⟨‖d t‖, norm_pos_iff.2 (hne t), ?_⟩⟩
  have h1 : (Circle.exp (F t) : ℂ) = d t / ‖d t‖ := by
    have := congrFun hF t
    simp only [Function.comp_apply] at this
    rw [this]
    rfl
  rw [Circle.coe_exp, Complex.exp_mul_I] at h1
  have h2 : d t = ‖d t‖ * (Complex.cos (F t) + Complex.sin (F t) * Complex.I) := by
    rw [h1]; field_simp [hn t]
  conv_lhs => rw [h2]
  apply Complex.ext <;>
    simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im]

/-! ### The theorem -/

theorem solution
    (F : Phase → ℝ) (x : ℝ → Phase)
    (hF : ∀ t : ℝ, ContDiffAt ℝ ∞ F (x t))
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution F x Y) :
    ∃ α : ℝ → ℝ, IsAmbientRotationAngle Y α := by
  obtain ⟨hY0, hYd⟩ := hY
  have hvd : ∀ t, ∀ v : Phase, HasDerivAt (fun τ => Y τ v)
      (TangentialHessian.qI.mulVec ((hessMat F (x t)).mulVec (Y t v))) t := by
    intro t v
    have h := (hYd t).clm_apply (hasDerivAt_const t v)
    refine h.congr_deriv ?_
    simp [fderiv_hvf_apply (hF t)]
  have hsymp := symp_all (fun t => hessMat_symm (hF t)) hY0 hvd
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun t => (hYd t).continuousAt
  have hdc : Continuous fun t => ambientRotationDet (Y t) := continuous_det.comp hYc
  have hne : ∀ t, ambientRotationDet (Y t) ≠ 0 := fun t h0 => by
    have h1 := one_le_norm_det (hsymp t)
    rw [h0, norm_zero] at h1
    norm_num at h1
  obtain ⟨α, hαc, hα⟩ := exists_angle hdc hne
  exact ⟨α, hαc, hα⟩
