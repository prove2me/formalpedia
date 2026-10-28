-- Prove2me | solution 1 for FunctionalInequalities.Analysis.convexOn_quadraticAt_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:31:58.455532+00:00
-- url     : https://prove2.me/submissions/8adec3f5-9d82-4d0a-a5a5-e7a9594ba456

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT12C1QuadraticSubgradientImage
open MeasureTheory Set Matrix
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
/-- A quadratic with positive semidefinite Hessian is convex. -/
theorem solution {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) : ConvexOn ℝ univ (FunctionalInequalities.Analysis.quadraticAt A x₀ b c) := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a r ha hr har
  change FunctionalInequalities.Analysis.quadraticAt A x₀ b c (a • x + r • y) ≤
    a * FunctionalInequalities.Analysis.quadraticAt A x₀ b c x + r * FunctionalInequalities.Analysis.quadraticAt A x₀ b c y
  rw [FunctionalInequalities.Analysis.quadraticAt_mix_identity hA x₀ b c x y a r har]
  have hcoeff : 0 ≤ (1 / 2 : ℝ) * (a * r) := by
    positivity
  have hq :
      0 ≤ ⟪x - y, Matrix.toEuclideanLin A (x - y)⟫ :=
    FunctionalInequalities.Analysis.quadraticAt_nonneg hA (x - y)
  have hprod :
      0 ≤ (1 / 2 : ℝ) * (a * r) *
        ⟪x - y, Matrix.toEuclideanLin A (x - y)⟫ :=
    mul_nonneg hcoeff hq
  nlinarith
