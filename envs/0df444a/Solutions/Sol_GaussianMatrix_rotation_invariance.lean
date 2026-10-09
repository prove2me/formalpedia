-- Prove2me | solution 1 for GaussianMatrix.rotation_invariance
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:05:56.518461+00:00
-- url     : https://prove2.me/submissions/558e8f3f-98a6-4e2f-8a38-79f3013494a2

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix.RotInv

/-- Flatten a `p × m` array into a vector of `EuclideanSpace ℝ (Fin p × Fin m)`. -/
noncomputable def flat (p m : ℕ) (G : Fin p → Fin m → ℝ) : EuclideanSpace ℝ (Fin p × Fin m) :=
  WithLp.toLp 2 (fun ij => G ij.1 ij.2)

lemma measurable_flat (p m : ℕ) : Measurable (flat p m) := by
  unfold flat
  exact (WithLp.measurable_toLp 2 _).comp (by fun_prop)

/-- `flat` as a measurable equivalence. -/
noncomputable def flatEquiv (p m : ℕ) :
    (Fin p → Fin m → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin p × Fin m) :=
  (MeasurableEquiv.curry (Fin p) (Fin m) ℝ).symm.trans (MeasurableEquiv.toLp 2 _)

/-- The Gaussian matrix law, flattened, is the standard Gaussian on `EuclideanSpace`. -/
lemma map_flat_gaussianMatrix (p m : ℕ) :
    (gaussianMatrix p m).map (flat p m) = stdGaussian (EuclideanSpace ℝ (Fin p × Fin m)) := by
  have h1 : gaussianMatrix p m =
      (Measure.pi fun _ : Fin p × Fin m => gaussianReal 0 1).map
        (MeasurableEquiv.curry (Fin p) (Fin m) ℝ) := by
    have := Measure.infinitePi_map_curry (fun (_ : Fin p) (_ : Fin m) => gaussianReal 0 1)
    simp only [Measure.infinitePi_eq_pi] at this
    rw [this]; rfl
  rw [h1, Measure.map_map (measurable_flat p m) (MeasurableEquiv.measurable _)]
  have h2 : flat p m ∘ (MeasurableEquiv.curry (Fin p) (Fin m) ℝ) = WithLp.toLp 2 := by
    funext x; rfl
  rw [h2, map_pi_eq_stdGaussian]


lemma sum_sq_eq_trace {p m : ℕ} (A : Matrix (Fin p) (Fin m) ℝ) :
    ∑ i, ∑ j, A i j ^ 2 = Matrix.trace (A * Aᵀ) := by
  simp [Matrix.trace, Matrix.mul_apply, sq]

lemma sum_sq_mul_orth {p m : ℕ} (U : Matrix (Fin p) (Fin p) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (X : Matrix (Fin p) (Fin m) ℝ) :
    ∑ i, ∑ j, (U * X * V) i j ^ 2 = ∑ i, ∑ j, X i j ^ 2 := by
  have hV' : V * Vᵀ = 1 := mul_eq_one_comm.mp hV
  rw [sum_sq_eq_trace, sum_sq_eq_trace]
  simp only [Matrix.transpose_mul]
  calc Matrix.trace (U * X * V * (Vᵀ * (Xᵀ * Uᵀ)))
      = Matrix.trace (U * (X * (V * Vᵀ) * Xᵀ) * Uᵀ) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Uᵀ * U * (X * (V * Vᵀ) * Xᵀ)) := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    _ = Matrix.trace (X * Xᵀ) := by rw [hU, hV', Matrix.one_mul, Matrix.mul_one]


/-- Unflatten a vector into a matrix. -/
def unflat {p m : ℕ} (x : EuclideanSpace ℝ (Fin p × Fin m)) : Matrix (Fin p) (Fin m) ℝ :=
  Matrix.of fun i j => x (i, j)

/-- The linear map `X ↦ U X V` on flattened matrices. -/
noncomputable def rotLin {p m : ℕ} (U : Matrix (Fin p) (Fin p) ℝ) (V : Matrix (Fin m) (Fin m) ℝ) :
    EuclideanSpace ℝ (Fin p × Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin p × Fin m) where
  toFun x := flat p m (Matrix.of.symm (U * unflat x * V))
  map_add' x y := by
    have : unflat (x + y) = unflat x + unflat y := by ext i j; simp [unflat]
    rw [this, Matrix.mul_add, Matrix.add_mul]
    ext ij; simp [flat]
  map_smul' c x := by
    have : unflat (c • x) = c • unflat x := by ext i j; simp [unflat]
    rw [this, Matrix.mul_smul, Matrix.smul_mul]
    ext ij; simp [flat]

lemma norm_rotLin {p m : ℕ} (U : Matrix (Fin p) (Fin p) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (x : EuclideanSpace ℝ (Fin p × Fin m)) :
    ‖rotLin U V x‖ = ‖x‖ := by
  have h : ‖rotLin U V x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type,
      Fintype.sum_prod_type]
    have := sum_sq_mul_orth U V hU hV (unflat x)
    simpa [rotLin, flat, unflat] using this
  have h1 := norm_nonneg (rotLin U V x)
  have h2 := norm_nonneg x
  nlinarith [sq_nonneg (‖rotLin U V x‖ - ‖x‖), sq_nonneg (‖rotLin U V x‖ + ‖x‖)]

/-- The isometry `X ↦ U X V` of the Frobenius space. -/
noncomputable def rotIso {p m : ℕ} (U : Matrix (Fin p) (Fin p) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    EuclideanSpace ℝ (Fin p × Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin p × Fin m) :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := rotLin U V, norm_map' := norm_rotLin U V hU hV } rfl

lemma rotIso_flat {p m : ℕ} (U : Matrix (Fin p) (Fin p) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (G : Fin p → Fin m → ℝ) :
    rotIso U V hU hV (flat p m G) = flat p m (Matrix.of.symm (U * Matrix.of G * V)) := by
  rfl

end GaussianMatrix.RotInv

open GaussianMatrix

theorem solution {p m : ℕ} (U : Matrix (Fin p) (Fin p) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    Measure.map (fun G : Fin p → Fin m → ℝ => Matrix.of.symm (U * Matrix.of G * V))
      (gaussianMatrix p m) = gaussianMatrix p m := by
  open GaussianMatrix.RotInv in
  have hmeas : Measurable (fun G : Fin p → Fin m → ℝ => Matrix.of.symm (U * Matrix.of G * V)) := by
    have hc : Continuous (fun G : Fin p → Fin m → ℝ => Matrix.of.symm (U * Matrix.of G * V)) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
      fun_prop
    exact hc.measurable
  have key : ((gaussianMatrix p m).map
      (fun G : Fin p → Fin m → ℝ => Matrix.of.symm (U * Matrix.of G * V))).map (flat p m) =
      (gaussianMatrix p m).map (flat p m) := by
    rw [Measure.map_map (measurable_flat p m) hmeas]
    have : flat p m ∘ (fun G : Fin p → Fin m → ℝ => Matrix.of.symm (U * Matrix.of G * V)) =
        rotIso U V hU hV ∘ flat p m := by
      funext G; exact (rotIso_flat U V hU hV G).symm
    rw [this, ← Measure.map_map (rotIso U V hU hV).continuous.measurable (measurable_flat p m),
      map_flat_gaussianMatrix, stdGaussian_map]
  have hfe : ⇑(flatEquiv p m) = flat p m := rfl
  rw [← hfe] at key
  exact (flatEquiv p m).map_measurableEquiv_injective key
