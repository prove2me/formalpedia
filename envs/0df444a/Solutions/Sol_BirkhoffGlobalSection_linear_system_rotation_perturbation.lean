-- Prove2me | solution 1 for BirkhoffGlobalSection.linear_system_rotation_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-29T23:53:26.278367+00:00
-- url     : https://prove2.me/submissions/62ee4cea-2290-48a3-8cab-9747ba472710

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# Robustness of the ambient rotation angle

Write `d M = ambientRotationDet M`. The proof has four steps.

1. Grönwall: on `[a, a + L]`, `‖Φ₀ t‖ ≤ B₀ = exp (4 ‖K‖ L)` and
   `‖Φ t - Φ₀ t‖ ≤ δ C₁`, with constants depending only on `K` and `L`.
2. `d` is uniformly continuous on the closed ball of radius `B₀ + 1`, so for small
   `δ` we get `|d (Φ t) - d (Φ₀ t)| < 1`.
3. `Φ₀ t` is symplectic, so `|d (Φ₀ t)| ≥ 1`. Hence `X t = d (Φ t) · conj (d (Φ₀ t))`
   has positive real part, and `arg ∘ X` is continuous on the interval.
4. `α - α₀ - arg ∘ X` is continuous with values in `2πℤ`, so it is constant.
   Since `X a = 1` and `arg > -π`, the increments differ by more than `-π`.
-/

open BirkhoffGlobalSection
open scoped Matrix Matrix.Norms.Elementwise

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

/-- The linear flow of a symmetric coefficient matrix preserves the symplectic
pairing on the interval where the equation holds. -/
private lemma symp_on_interval {a b : ℝ} (hab : a ≤ b) {H : ℝ → Matrix (Fin 4) (Fin 4) ℝ}
    (hHs : ∀ t ∈ Set.Icc a b, ∀ i j : Fin 4, H t i j = H t j i)
    {Y : ℝ → (Phase →L[ℝ] Phase)}
    (hY0 : ∀ u v : Phase,
      Y a u ⬝ᵥ TangentialHessian.qI.mulVec (Y a v) = u ⬝ᵥ TangentialHessian.qI.mulVec v)
    (hYd : ∀ t ∈ Set.Icc a b, ∀ v : Phase,
      HasDerivAt (fun τ => Y τ v) (TangentialHessian.qI.mulVec ((H t).mulVec (Y t v))) t) :
    ∀ t ∈ Set.Icc a b, ∀ u v : Phase,
      Y t u ⬝ᵥ TangentialHessian.qI.mulVec (Y t v) = u ⬝ᵥ TangentialHessian.qI.mulVec v := by
  intro t ht u v
  set f : ℝ → ℝ := fun τ => Y τ u ⬝ᵥ TangentialHessian.qI.mulVec (Y τ v) with hf
  have hderiv : ∀ s ∈ Set.Icc a b, HasDerivAt f 0 s := by
    intro s hs
    have hc := hasDerivAt_pi.mp (hYd s hs u)
    have hd := hasDerivAt_pi.mp (hYd s hs v)
    have h := ((((hc 0).mul (hd 2)).add ((hc 1).mul (hd 3))).sub ((hc 2).mul (hd 0))).sub
      ((hc 3).mul (hd 1))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => ?_)
    · simp only [qI0, qI1, qI2, qI3]
      simp only [mulVec_apply4]
      have h01 := hHs s hs 0 1; have h02 := hHs s hs 0 2; have h03 := hHs s hs 0 3
      have h12 := hHs s hs 1 2; have h13 := hHs s hs 1 3; have h23 := hHs s hs 2 3
      rw [h01, h02, h03, h12, h13, h23]
      ring
    · simp only [hf, omegaQ, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  have hcont : ContinuousOn f (Set.Icc a b) :=
    fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun s hs => (hderiv s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
  rw [show Y t u ⬝ᵥ TangentialHessian.qI.mulVec (Y t v) = f t from rfl, hconst t ht]
  exact hY0 u v

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

private lemma continuousOn_mk {f g : ℝ → ℝ} {s : Set ℝ} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun t => (⟨f t, g t⟩ : ℂ)) s := by
  have : (fun t => (⟨f t, g t⟩ : ℂ)) = fun t => (f t : ℂ) + (g t : ℂ) * Complex.I := by
    funext t; apply Complex.ext <;> simp
  rw [this]
  exact (Complex.continuous_ofReal.comp_continuousOn hf).add
    ((Complex.continuous_ofReal.comp_continuousOn hg).mul continuousOn_const)

/-- The ambient determinant of a family of maps with continuous entries is continuous. -/
private lemma detP_continuousOn {Z : ℝ → (Phase →L[ℝ] Phase)} {s : Set ℝ}
    (hZ : ∀ (k i : Fin 4), ContinuousOn (fun t => Z t (coordinateVector k) i) s) :
    ContinuousOn (fun t => ambientRotationDet (Z t)) s := by
  simp only [ambientRotationDet_eq]
  refine ((continuousOn_mk ?_ ?_).mul (continuousOn_mk ?_ ?_)).sub
    ((continuousOn_mk ?_ ?_).mul (continuousOn_mk ?_ ?_)) <;>
    first
    | exact ((hZ _ _).add (hZ _ _)).div_const _
    | exact ((hZ _ _).sub (hZ _ _)).div_const _

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

/-! ### Norm estimates and Grönwall -/

private lemma norm_qI_mulVec (y : Phase) : ‖TangentialHessian.qI.mulVec y‖ ≤ ‖y‖ := by
  rw [qI_apply]
  have hc : ∀ j, |y j| ≤ ‖y‖ := fun j => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm y j
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 fun i => ?_
  fin_cases i <;> simp [hc]

private lemma norm_mulVec_le (A : Matrix (Fin 4) (Fin 4) ℝ) (x : Phase) :
    ‖A.mulVec x‖ ≤ 4 * ‖A‖ * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [mulVec_apply4]
  have hb : ∀ j, ‖A i j * x j‖ ≤ ‖A‖ * ‖x‖ := fun j => by
    rw [norm_mul]
    exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A) (norm_le_pi_norm x j)
      (norm_nonneg _) (norm_nonneg _)
  have h1 := norm_add_le (A i 0 * x 0 + A i 1 * x 1 + A i 2 * x 2) (A i 3 * x 3)
  have h2 := norm_add_le (A i 0 * x 0 + A i 1 * x 1) (A i 2 * x 2)
  have h3 := norm_add_le (A i 0 * x 0) (A i 1 * x 1)
  linarith [hb 0, hb 1, hb 2, hb 3]

private lemma norm_field_le (A : Matrix (Fin 4) (Fin 4) ℝ) (x : Phase) :
    ‖TangentialHessian.qI.mulVec (A.mulVec x)‖ ≤ 4 * ‖A‖ * ‖x‖ :=
  (norm_qI_mulVec _).trans (norm_mulVec_le A x)

/-- Exponential growth bound for the linear system. -/
private lemma gronwall_growth {a b c : ℝ} {A : ℝ → Matrix (Fin 4) (Fin 4) ℝ}
    (hA : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ c) {f : ℝ → Phase}
    (hf : ∀ t ∈ Set.Icc a b,
      HasDerivAt f (TangentialHessian.qI.mulVec ((A t).mulVec (f t))) t) :
    ∀ t ∈ Set.Icc a b, ‖f t‖ ≤ ‖f a‖ * Real.exp (4 * c * (t - a)) := by
  intro t ht
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := f)
    (f' := fun s => TangentialHessian.qI.mulVec ((A s).mulVec (f s)))
    (δ := ‖f a‖) (K := 4 * c) (ε := 0)
    (fun s hs => (hf s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hf s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
    le_rfl
    (fun s hs => by
      have h1 := norm_field_le (A s) (f s)
      have h2 : 4 * ‖A s‖ * ‖f s‖ ≤ 4 * c * ‖f s‖ := by
        have := hA s (Set.Ico_subset_Icc_self hs)
        have := norm_nonneg (f s)
        nlinarith
      linarith)
    t ht
  rwa [gronwallBound_ε0] at h

/-- Grönwall comparison of two linear systems with close coefficients. -/
private lemma gronwall_diff {a b c δ G : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ) (hG : 0 ≤ G)
    {A : ℝ → Matrix (Fin 4) (Fin 4) ℝ} {B : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ c) (hAB : ∀ t ∈ Set.Icc a b, ‖A t - B‖ ≤ δ)
    {f g : ℝ → Phase}
    (hf : ∀ t ∈ Set.Icc a b,
      HasDerivAt f (TangentialHessian.qI.mulVec ((A t).mulVec (f t))) t)
    (hg : ∀ t ∈ Set.Icc a b, HasDerivAt g (TangentialHessian.qI.mulVec (B.mulVec (g t))) t)
    (hgb : ∀ t ∈ Set.Icc a b, ‖g t‖ ≤ G) (h0 : f a = g a) :
    ∀ t ∈ Set.Icc a b, ‖f t - g t‖ ≤ δ * G / c * Real.exp (4 * c * (t - a)) := by
  intro t ht
  have hsplit : ∀ s, TangentialHessian.qI.mulVec ((A s).mulVec (f s)) -
      TangentialHessian.qI.mulVec (B.mulVec (g s)) =
      TangentialHessian.qI.mulVec ((A s).mulVec (f s - g s)) +
        TangentialHessian.qI.mulVec ((A s - B).mulVec (g s)) := by
    intro s
    simp only [Matrix.mulVec_sub, Matrix.sub_mulVec]
    abel
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun s => f s - g s)
    (f' := fun s => TangentialHessian.qI.mulVec ((A s).mulVec (f s)) -
      TangentialHessian.qI.mulVec (B.mulVec (g s)))
    (δ := 0) (K := 4 * c) (ε := 4 * δ * G)
    (fun s hs => ((hf s hs).sub (hg s hs)).continuousAt.continuousWithinAt)
    (fun s hs => ((hf s (Set.Ico_subset_Icc_self hs)).sub
      (hg s (Set.Ico_subset_Icc_self hs))).hasDerivWithinAt)
    (by simp [h0])
    (fun s hs => by
      have hs' := Set.Ico_subset_Icc_self hs
      rw [hsplit s]
      have h1 := norm_add_le (TangentialHessian.qI.mulVec ((A s).mulVec (f s - g s)))
        (TangentialHessian.qI.mulVec ((A s - B).mulVec (g s)))
      have h2 := norm_field_le (A s) (f s - g s)
      have h3 := norm_field_le (A s - B) (g s)
      have h4 : 4 * ‖A s‖ * ‖f s - g s‖ ≤ 4 * c * ‖f s - g s‖ := by
        have := hA s hs'
        have := norm_nonneg (f s - g s)
        nlinarith
      have h5 : 4 * ‖A s - B‖ * ‖g s‖ ≤ 4 * δ * G := by
        have := hAB s hs'
        have := hgb s hs'
        have := norm_nonneg (A s - B)
        have := norm_nonneg (g s)
        nlinarith
      linarith)
    t ht
  rw [gronwallBound_of_K_ne_0 (by positivity)] at h
  have hc4 : (4 * δ * G) / (4 * c) = δ * G / c := by field_simp
  simp only [zero_mul, zero_add, hc4] at h
  have hq : 0 ≤ δ * G / c := by positivity
  nlinarith [Real.exp_pos (4 * c * (t - a))]

/-! ### Uniform continuity and integer-valued continuous functions -/

private lemma det_uniform (R : ℝ) : ∃ η > 0,
    ∀ M ∈ Metric.closedBall (0 : Phase →L[ℝ] Phase) R,
      ∀ N ∈ Metric.closedBall (0 : Phase →L[ℝ] Phase) R,
        dist M N < η → dist (ambientRotationDet M) (ambientRotationDet N) < 1 := by
  have hu := (isCompact_closedBall (0 : Phase →L[ℝ] Phase) R).uniformContinuousOn_of_continuous
    continuous_det.continuousOn
  exact Metric.uniformContinuousOn_iff.1 hu 1 one_pos

/-- A continuous function on an interval with values in `2πℤ` is constant. -/
private lemma const_of_two_pi_int {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Icc a b))
    (hint : ∀ t ∈ Set.Icc a b, ∃ k : ℤ, g t = k * (2 * Real.pi)) :
    g b = g a := by
  obtain ⟨k₁, hk₁⟩ := hint a ⟨le_rfl, hab⟩
  obtain ⟨k₂, hk₂⟩ := hint b ⟨hab, le_rfl⟩
  have hπ := Real.pi_pos
  have hodd : ∀ m n : ℤ, (m : ℝ) * (2 * Real.pi) ≠ n * (2 * Real.pi) + Real.pi := by
    intro m n h
    have h' : ((2 * (m - n) : ℤ) : ℝ) * Real.pi = 1 * Real.pi := by
      push_cast; linarith
    have h'' : ((2 * (m - n) : ℤ) : ℝ) = 1 := mul_right_cancel₀ hπ.ne' h'
    have : 2 * (m - n) = 1 := by exact_mod_cast h''
    omega
  rcases lt_trichotomy k₁ k₂ with h | h | h
  · exfalso
    have hk : (k₁ : ℝ) + 1 ≤ k₂ := by exact_mod_cast h
    have hmem : (k₁ : ℝ) * (2 * Real.pi) + Real.pi ∈ Set.Icc (g a) (g b) := by
      rw [hk₁, hk₂]
      constructor <;> nlinarith
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc hab hg hmem
    obtain ⟨m, hm⟩ := hint t ht
    exact hodd m k₁ (hm ▸ hgt)
  · rw [hk₁, hk₂, h]
  · exfalso
    have hk : (k₂ : ℝ) + 1 ≤ k₁ := by exact_mod_cast h
    have hmem : (k₂ : ℝ) * (2 * Real.pi) + Real.pi ∈ Set.Icc (g b) (g a) := by
      rw [hk₁, hk₂]
      constructor <;> nlinarith
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc' hab hg hmem
    obtain ⟨m, hm⟩ := hint t ht
    exact hodd m k₂ (hm ▸ hgt)

/-! ### The perturbation estimate -/

theorem solution (K : Matrix (Fin 4) (Fin 4) ℝ)
    (hK : ∀ i j : Fin 4, K i j = K j i) (L : ℝ) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : ℝ) (H : ℝ → Matrix (Fin 4) (Fin 4) ℝ),
        ContinuousOn H (Set.Icc a (a + L)) →
        (∀ t ∈ Set.Icc a (a + L), ∀ i j : Fin 4, H t i j = H t j i) →
        (∀ t ∈ Set.Icc a (a + L), ‖H t - K‖ < δ) →
        ∀ Φ Φ₀ : ℝ → (Phase →L[ℝ] Phase),
          Φ a = ContinuousLinearMap.id ℝ Phase →
          Φ₀ a = ContinuousLinearMap.id ℝ Phase →
          (∀ t ∈ Set.Icc a (a + L), ∀ v : Phase,
            HasDerivAt (fun τ => Φ τ v)
              (TangentialHessian.qI.mulVec ((H t).mulVec (Φ t v))) t) →
          (∀ t ∈ Set.Icc a (a + L), ∀ v : Phase,
            HasDerivAt (fun τ => Φ₀ τ v) (TangentialHessian.qI.mulVec (K.mulVec (Φ₀ t v))) t) →
          ∀ α α₀ : ℝ → ℝ,
            ContinuousOn α (Set.Icc a (a + L)) → ContinuousOn α₀ (Set.Icc a (a + L)) →
            (∀ t ∈ Set.Icc a (a + L), ∃ ρ : ℝ, 0 < ρ ∧
              ambientRotationDet (Φ t) = ⟨ρ * Real.cos (α t), ρ * Real.sin (α t)⟩) →
            (∀ t ∈ Set.Icc a (a + L), ∃ ρ : ℝ, 0 < ρ ∧
              ambientRotationDet (Φ₀ t) = ⟨ρ * Real.cos (α₀ t), ρ * Real.sin (α₀ t)⟩) →
            α₀ (a + L) - α₀ a - Real.pi < α (a + L) - α a := by
  -- constants depending only on `K` and `L`
  set B₀ : ℝ := Real.exp (4 * ‖K‖ * L) with hB₀def
  set c₁ : ℝ := ‖K‖ + 1 with hc₁def
  set C₁ : ℝ := B₀ / c₁ * Real.exp (4 * c₁ * L) with hC₁def
  have hB₀ : 0 < B₀ := Real.exp_pos _
  have hc₁ : 0 < c₁ := by positivity
  have hC₁ : 0 < C₁ := by positivity
  obtain ⟨η, hη, hunif⟩ := det_uniform (B₀ + 1)
  set m : ℝ := min η 1 with hmdef
  have hm : 0 < m := lt_min hη one_pos
  refine ⟨min 1 (m / (2 * C₁)), lt_min one_pos (by positivity), ?_⟩
  intro a H hHc hHs hHδ Φ Φ₀ hΦa hΦ₀a hΦd hΦ₀d α α₀ hαc hα₀c hαp hα₀p
  set δ : ℝ := min 1 (m / (2 * C₁)) with hδdef
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδC : δ * (2 * C₁) ≤ m := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hmη : m ≤ η := min_le_left _ _
  have hm1 : m ≤ 1 := min_le_right _ _
  set I := Set.Icc a (a + L) with hIdef
  have hab : a ≤ a + L := by linarith
  have haI : a ∈ I := ⟨le_refl a, hab⟩
  have hbI : a + L ∈ I := ⟨hab, le_refl _⟩
  -- Grönwall bounds
  have hΦ₀v : ∀ t ∈ I, ∀ v : Phase, ‖Φ₀ t v‖ ≤ B₀ * ‖v‖ := by
    intro t ht v
    have h := gronwall_growth (A := fun _ => K) (c := ‖K‖) (fun _ _ => le_rfl)
      (f := fun τ => Φ₀ τ v) (fun s hs => hΦ₀d s hs v) t ht
    simp only [hΦ₀a, ContinuousLinearMap.id_apply] at h
    have hexp : Real.exp (4 * ‖K‖ * (t - a)) ≤ B₀ := by
      rw [hB₀def]
      apply Real.exp_le_exp.mpr
      have := ht.2
      have := norm_nonneg K
      nlinarith
    have := norm_nonneg v
    nlinarith
  have hHK : ∀ t ∈ I, ‖H t‖ ≤ c₁ := by
    intro t ht
    have h1 := norm_le_insert' (H t) K
    have h2 := hHδ t ht
    linarith
  have hdiffv : ∀ t ∈ I, ∀ v : Phase, ‖Φ t v - Φ₀ t v‖ ≤ δ * C₁ * ‖v‖ := by
    intro t ht v
    have h := gronwall_diff (c := c₁) (δ := δ) (G := B₀ * ‖v‖) hc₁ hδpos.le (by positivity)
      (A := H) (B := K) hHK (fun s hs => (hHδ s hs).le)
      (f := fun τ => Φ τ v) (g := fun τ => Φ₀ τ v)
      (fun s hs => hΦd s hs v) (fun s hs => hΦ₀d s hs v) (fun s hs => hΦ₀v s hs v)
      (by simp only [hΦa, hΦ₀a]) t ht
    have hexp : Real.exp (4 * c₁ * (t - a)) ≤ Real.exp (4 * c₁ * L) := by
      apply Real.exp_le_exp.mpr
      have := ht.2
      nlinarith
    have hq : 0 ≤ δ * (B₀ * ‖v‖) / c₁ := by positivity
    calc ‖Φ t v - Φ₀ t v‖ ≤ δ * (B₀ * ‖v‖) / c₁ * Real.exp (4 * c₁ * (t - a)) := h
      _ ≤ δ * (B₀ * ‖v‖) / c₁ * Real.exp (4 * c₁ * L) :=
          mul_le_mul_of_nonneg_left hexp hq
      _ = δ * C₁ * ‖v‖ := by rw [hC₁def]; ring
  have hΦ₀op : ∀ t ∈ I, ‖Φ₀ t‖ ≤ B₀ := fun t ht =>
    ContinuousLinearMap.opNorm_le_bound _ hB₀.le (hΦ₀v t ht)
  have hdop : ∀ t ∈ I, ‖Φ t - Φ₀ t‖ ≤ δ * C₁ := fun t ht =>
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => hdiffv t ht v)
  -- the determinants stay within distance one
  have hdclose : ∀ t ∈ I,
      ‖ambientRotationDet (Φ t) - ambientRotationDet (Φ₀ t)‖ < 1 := by
    intro t ht
    have hΦ₀mem : Φ₀ t ∈ Metric.closedBall (0 : Phase →L[ℝ] Phase) (B₀ + 1) := by
      rw [mem_closedBall_zero_iff]; linarith [hΦ₀op t ht]
    have hΦmem : Φ t ∈ Metric.closedBall (0 : Phase →L[ℝ] Phase) (B₀ + 1) := by
      rw [mem_closedBall_zero_iff]
      have h1 := norm_le_insert' (Φ t) (Φ₀ t)
      linarith [hΦ₀op t ht, hdop t ht]
    have hdist : dist (Φ t) (Φ₀ t) < η := by
      rw [dist_eq_norm]; linarith [hdop t ht]
    have := hunif (Φ t) hΦmem (Φ₀ t) hΦ₀mem hdist
    rwa [dist_eq_norm] at this
  -- the unperturbed flow is symplectic, so its determinant has modulus at least one
  have hsymp := symp_on_interval (H := fun _ => K) hab (fun _ _ i j => hK i j)
    (Y := Φ₀) (by intro u v; rw [hΦ₀a]; rfl) hΦ₀d
  have hd₀ : ∀ t ∈ I, 1 ≤ ‖ambientRotationDet (Φ₀ t)‖ :=
    fun t ht => one_le_norm_det (hsymp t ht)
  -- the comparison product
  set X : ℝ → ℂ := fun t =>
    ambientRotationDet (Φ t) * (starRingEnd ℂ) (ambientRotationDet (Φ₀ t)) with hXdef
  have hXre : ∀ t ∈ I, 0 < (X t).re := by
    intro t ht
    set d := ambientRotationDet (Φ t)
    set d₀ := ambientRotationDet (Φ₀ t)
    have hsplit : X t = d₀ * (starRingEnd ℂ) d₀ + (d - d₀) * (starRingEnd ℂ) d₀ := by
      simp only [hXdef]; ring
    have hre1 : (d₀ * (starRingEnd ℂ) d₀).re = ‖d₀‖ ^ 2 := by
      rw [Complex.mul_conj, Complex.ofReal_re, ← Complex.sq_norm]
    have hre2 : -(‖d - d₀‖ * ‖d₀‖) ≤ ((d - d₀) * (starRingEnd ℂ) d₀).re := by
      have h := Complex.abs_re_le_norm ((d - d₀) * (starRingEnd ℂ) d₀)
      rw [norm_mul, Complex.norm_conj] at h
      linarith [neg_abs_le ((d - d₀) * (starRingEnd ℂ) d₀).re]
    rw [hsplit, Complex.add_re]
    have h1 := hd₀ t ht
    have h2 := hdclose t ht
    nlinarith [norm_nonneg (d - d₀)]
  have hXslit : ∀ t ∈ I, X t ∈ Complex.slitPlane :=
    fun t ht => Complex.mem_slitPlane_iff.2 (Or.inl (hXre t ht))
  have hΦc : ∀ (k i : Fin 4), ContinuousOn (fun t => Φ t (coordinateVector k) i) I :=
    fun k i t ht =>
      ((hasDerivAt_pi.mp (hΦd t ht (coordinateVector k))) i).continuousAt.continuousWithinAt
  have hΦ₀c : ∀ (k i : Fin 4), ContinuousOn (fun t => Φ₀ t (coordinateVector k) i) I :=
    fun k i t ht =>
      ((hasDerivAt_pi.mp (hΦ₀d t ht (coordinateVector k))) i).continuousAt.continuousWithinAt
  have hXc : ContinuousOn X I :=
    (detP_continuousOn hΦc).mul
      (Complex.continuous_conj.comp_continuousOn (detP_continuousOn hΦ₀c))
  have hargc : ContinuousOn (fun t => Complex.arg (X t)) I :=
    fun t ht => (Complex.continuousAt_arg (hXslit t ht)).comp_continuousWithinAt (hXc t ht)
  -- the angle defect is an integer multiple of `2π`
  set g : ℝ → ℝ := fun t => α t - α₀ t - Complex.arg (X t) with hgdef
  have hgc : ContinuousOn g I := (hαc.sub hα₀c).sub hargc
  have hint : ∀ t ∈ I, ∃ k : ℤ, g t = k * (2 * Real.pi) := by
    intro t ht
    obtain ⟨ρ, hρ, h1⟩ := hαp t ht
    obtain ⟨ρ₀, hρ₀, h2⟩ := hα₀p t ht
    have hX : X t = ((ρ * ρ₀ : ℝ) : ℂ) *
        (Complex.cos ((α t - α₀ t : ℝ) : ℂ) + Complex.sin ((α t - α₀ t : ℝ) : ℂ) * Complex.I) := by
      simp only [hXdef]
      rw [h1, h2]
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
          Complex.I_re, Complex.I_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
          Real.cos_sub, Real.sin_sub]
        ring
      · simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
          Complex.I_re, Complex.I_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
          Real.cos_sub, Real.sin_sub]
        ring
    refine ⟨toIocDiv Real.two_pi_pos (-Real.pi) (α t - α₀ t), ?_⟩
    simp only [hgdef]
    rw [hX, Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod (by positivity), self_sub_toIocMod,
      zsmul_eq_mul]
  have hconst := const_of_two_pi_int hab hgc hint
  -- conclusion
  have hXa : X a = 1 := by
    simp only [hXdef, hΦa, hΦ₀a, det_id, map_one, mul_one]
  simp only [hgdef, hXa, Complex.arg_one, sub_zero] at hconst
  have hlow := Complex.neg_pi_lt_arg (X (a + L))
  linarith
