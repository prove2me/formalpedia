-- Prove2me | solution 1 for FunctionalInequalities.Analysis.convexOn_quadraticAt_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:13:09.407234+00:00
-- url     : https://prove2.me/submissions/b647cce7-8bec-433d-bd3d-4bf22d046160

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT12C1QuadraticSubgradientImage
open MeasureTheory Set Matrix
open scoped RealInnerProductSpace ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
private lemma FunctionalInequalities.Analysis.quadraticAt_inner_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, Matrix.toEuclideanLin A y⟫ = ⟪Matrix.toEuclideanLin A x, y⟫ := by
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin A
  have hT : LinearMap.adjoint T = T := by
    calc
      LinearMap.adjoint T = Matrix.toEuclideanLin Aᴴ := by
        symm
        exact Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
      _ = T := by
        rw [hA.eq]
  change ⟪x, T y⟫ = ⟪T x, y⟫
  simpa [hT] using LinearMap.adjoint_inner_right T x y
private lemma FunctionalInequalities.Analysis.quadraticAt_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ ⟪x, Matrix.toEuclideanLin A x⟫ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change 0 ≤ (A *ᵥ x.ofLp) ⬝ᵥ star x.ofLp
  simpa [dotProduct_comm] using
    (posSemidef_iff_dotProduct_mulVec.mp hA).2 x.ofLp
private lemma FunctionalInequalities.Analysis.quadraticAt_mix_identity {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) (a r : ℝ) (har : a + r = 1) :
    quadraticAt A x₀ b c (a • x + r • y) =
      a * quadraticAt A x₀ b c x + r * quadraticAt A x₀ b c y -
        (1 / 2) * (a * r) *
          ⟪x - y, Matrix.toEuclideanLin A (x - y)⟫ := by
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin A
  have hr : r = 1 - a := by
    linarith
  have hcross (u v : EuclideanSpace ℝ (Fin n)) :
      ⟪v, T u⟫ = ⟪u, T v⟫ := by
    calc
      ⟪v, T u⟫ = ⟪T u, v⟫ := real_inner_comm _ _
      _ = ⟪u, T v⟫ := (quadraticAt_inner_symm hA.1 u v).symm
  have hquad (u v : EuclideanSpace ℝ (Fin n)) :
      ⟪a • u + r • v, T (a • u + r • v)⟫ =
        a * ⟪u, T u⟫ + r * ⟪v, T v⟫ -
          a * r * ⟪u - v, T (u - v)⟫ := by
    rw [hr]
    simp only [map_add, map_smul, map_sub, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [hcross u v]
    ring
  have harg :
      a • x + r • y - x₀ = a • (x - x₀) + r • (y - x₀) := by
    calc
      a • x + r • y - x₀ =
          a • x + r • y - (a + r) • x₀ := by
            rw [har, one_smul]
      _ = a • (x - x₀) + r • (y - x₀) := by
        module
  have hdiff : (x - x₀) - (y - x₀) = x - y := by
    abel
  dsimp [quadraticAt]
  dsimp [T] at hquad ⊢
  rw [harg, hquad, hdiff]
  have hlin :
      ⟪b, a • (x - x₀) + r • (y - x₀)⟫ =
        a * ⟪b, x - x₀⟫ + r * ⟪b, y - x₀⟫ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [hlin, hr]
  ring
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- A quadratic with positive semidefinite Hessian is convex. -/
theorem solution {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) : ConvexOn ℝ univ (FunctionalInequalities.Analysis.quadraticAt A x₀ b c) := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a r ha hr har
  change FunctionalInequalities.Analysis.quadraticAt A x₀ b c (a • x + r • y) ≤
    a * FunctionalInequalities.Analysis.quadraticAt A x₀ b c x + r * FunctionalInequalities.Analysis.quadraticAt A x₀ b c y
  rw [quadraticAt_mix_identity hA x₀ b c x y a r har]
  have hcoeff : 0 ≤ (1 / 2 : ℝ) * (a * r) := by
    positivity
  have hq :
      0 ≤ ⟪x - y, Matrix.toEuclideanLin A (x - y)⟫ :=
    quadraticAt_nonneg hA (x - y)
  have hprod :
      0 ≤ (1 / 2 : ℝ) * (a * r) *
        ⟪x - y, Matrix.toEuclideanLin A (x - y)⟫ :=
    mul_nonneg hcoeff hq
  nlinarith
