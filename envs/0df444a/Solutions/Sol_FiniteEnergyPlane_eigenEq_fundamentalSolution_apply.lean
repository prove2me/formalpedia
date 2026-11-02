-- Prove2me | solution 1 for FiniteEnergyPlane.eigenEq_fundamentalSolution_apply
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T23:02:53.417126+00:00
-- url     : https://prove2.me/submissions/c8ef37ec-eb40-481a-b737-ec8099f329fd

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib



namespace FiniteEnergyPlane

open Matrix Filter Topology ComplexConjugate
open scoped Real ContDiff

theorem eigenEq_fundamentalSolution_apply_aux (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (μ : ℝ)
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1)
    (hΨ : CauchyRiemannIndex.IsFundamentalSolution
      (fun t => Sinf t + μ • (1 : CauchyRiemannIndex.Mat 1)) Ψ)
    (w : CauchyRiemannIndex.Vec 1) :
    Differentiable ℝ (fun t => Matrix.toEuclideanLin (Ψ t) w) ∧
      ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1)
        (deriv (fun t => Matrix.toEuclideanLin (Ψ t) w) t)) -
          Matrix.toEuclideanLin (Sinf t) (Matrix.toEuclideanLin (Ψ t) w) =
        μ • Matrix.toEuclideanLin (Ψ t) w := by
  let _ : NormedAddCommGroup (CauchyRiemannIndex.Mat 1) := Matrix.normedAddCommGroup
  let _ : NormedSpace ℝ (CauchyRiemannIndex.Mat 1) := Matrix.normedSpace
  let Lw : CauchyRiemannIndex.Mat 1 →ₗ[ℝ] CauchyRiemannIndex.Vec 1 :=
    { toFun := fun N => Matrix.toEuclideanLin N w
      map_add' := fun N N' => by simp
      map_smul' := fun c N => by simp }
  have hx : ∀ t, HasDerivAt (fun t => Matrix.toEuclideanLin (Ψ t) w)
      (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * (Sinf t + μ • 1) * Ψ t) w) t := fun t =>
    (LinearMap.toContinuousLinearMap Lw).hasFDerivAt.comp_hasDerivAt t (hΨ.2 t)
  refine ⟨fun t => (hx t).differentiableAt, fun t => ?_⟩
  rw [(hx t).deriv]
  have hJ : CauchyRiemannIndex.J₀ 1 * CauchyRiemannIndex.J₀ 1 = -1 := Matrix.J_squared _ _
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  have hm : (CauchyRiemannIndex.J₀ 1 * (Sinf t + μ • 1) * Ψ t) *ᵥ WithLp.ofLp w =
      CauchyRiemannIndex.J₀ 1 *ᵥ (Sinf t *ᵥ (Ψ t *ᵥ WithLp.ofLp w) +
        μ • (Ψ t *ᵥ WithLp.ofLp w)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hm, Matrix.mulVec_mulVec, hJ, Matrix.neg_mulVec, Matrix.one_mulVec]
  ext i
  simp

end FiniteEnergyPlane

open FiniteEnergyPlane

open Filter Topology
open scoped Real ContDiff

theorem solution (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (μ : ℝ)
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1)
    (hΨ : CauchyRiemannIndex.IsFundamentalSolution
      (fun t => Sinf t + μ • (1 : CauchyRiemannIndex.Mat 1)) Ψ)
    (w : CauchyRiemannIndex.Vec 1) :
    Differentiable ℝ (fun t => Matrix.toEuclideanLin (Ψ t) w) ∧
      ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1)
        (deriv (fun t => Matrix.toEuclideanLin (Ψ t) w) t)) -
          Matrix.toEuclideanLin (Sinf t) (Matrix.toEuclideanLin (Ψ t) w) =
        μ • Matrix.toEuclideanLin (Ψ t) w :=
  eigenEq_fundamentalSolution_apply_aux Sinf μ Ψ hΨ w
