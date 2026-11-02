-- Prove2me | solution 1 for FiniteEnergyPlane.exists_eigenEq_solution
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T21:48:09.842655+00:00
-- url     : https://prove2.me/submissions/b472957e-3aa6-4a26-97bf-95ae8b6d12ce

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Matrix.Normed



namespace FiniteEnergyPlane

open Matrix

theorem exists_eigenEq_solution_aux {n : ℕ} (S : ℝ → CauchyRiemannIndex.Mat n)
    (hS : Continuous S) (μ : ℝ) (v : CauchyRiemannIndex.Vec n) :
    ∃ x : ℝ → CauchyRiemannIndex.Vec n, x 0 = v ∧ Differentiable ℝ x ∧
      ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (deriv x t)) -
        Matrix.toEuclideanLin (S t) (x t) = μ • x t := by
  obtain ⟨Ψ, ⟨h0, hd⟩, -⟩ := CauchyRiemannIndex.fundamentalSolution_existsUnique n
    (fun t => S t + μ • (1 : CauchyRiemannIndex.Mat n)) (hS.add continuous_const)
  letI : NormedAddCommGroup (CauchyRiemannIndex.Mat n) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (CauchyRiemannIndex.Mat n) := Matrix.normedSpace
  let L : CauchyRiemannIndex.Mat n →ₗ[ℝ] CauchyRiemannIndex.Vec n :=
    { toFun := fun M => Matrix.toEuclideanLin M v
      map_add' := fun M N => by simp
      map_smul' := fun c M => by simp }
  have hx : ∀ t, HasDerivAt (fun t => Matrix.toEuclideanLin (Ψ t) v)
      (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n * (S t + μ • 1) * Ψ t) v) t := by
    intro t
    exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t (hd t)
  refine ⟨fun t => Matrix.toEuclideanLin (Ψ t) v, by simp [h0], fun t => (hx t).differentiableAt,
    fun t => ?_⟩
  rw [(hx t).deriv]
  have hJ : CauchyRiemannIndex.J₀ n * CauchyRiemannIndex.J₀ n = -1 := Matrix.J_squared _ _
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  have hm : (CauchyRiemannIndex.J₀ n * (S t + μ • 1) * Ψ t) *ᵥ WithLp.ofLp v =
      CauchyRiemannIndex.J₀ n *ᵥ (S t *ᵥ (Ψ t *ᵥ WithLp.ofLp v) + μ • (Ψ t *ᵥ WithLp.ofLp v)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hm, Matrix.mulVec_mulVec, hJ, Matrix.neg_mulVec, Matrix.one_mulVec]
  ext i
  simp

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {n : ℕ} (S : ℝ → CauchyRiemannIndex.Mat n) (hS : Continuous S)
    (μ : ℝ) (v : CauchyRiemannIndex.Vec n) :
    ∃ x : ℝ → CauchyRiemannIndex.Vec n, x 0 = v ∧ Differentiable ℝ x ∧
      ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (deriv x t)) -
        Matrix.toEuclideanLin (S t) (x t) = μ • x t :=
  exists_eigenEq_solution_aux S hS μ v
