-- Prove2me | solution 1 for FunctionalInequalities.Analysis.quadraticAt_subgradient_iff_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:32:37.096004+00:00
-- url     : https://prove2.me/submissions/903ff7ab-1eb7-4f96-91fd-8f02946afc7b

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
private lemma FunctionalInequalities.Analysis.quadraticAt_quadratic_expand {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) :
    quadraticAt A x₀ b c (x + v) =
      quadraticAt A x₀ b c x +
        ⟪b + Matrix.toEuclideanLin A (x - x₀), v⟫ +
          (1 / 2) * ⟪v, Matrix.toEuclideanLin A v⟫ := by
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin A
  have hq (z w : EuclideanSpace ℝ (Fin n)) :
      ⟪z + w, T (z + w)⟫ =
        ⟪z, T z⟫ + 2 * ⟪T z, w⟫ + ⟪w, T w⟫ := by
    simp only [map_add, inner_add_left, inner_add_right]
    rw [quadraticAt_inner_symm hA z w, real_inner_comm w (T z)]
    ring
  have harg : x + v - x₀ = (x - x₀) + v := by
    abel
  dsimp [quadraticAt]
  dsimp [T] at hq ⊢
  rw [harg, hq]
  have hlin :
      ⟪b + Matrix.toEuclideanLin A (x - x₀), v⟫ =
        ⟪b, v⟫ + ⟪Matrix.toEuclideanLin A (x - x₀), v⟫ := by
    rw [inner_add_left]
  rw [hlin, inner_add_right]
  ring
 lemma solution {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) :
    (∀ y, FunctionalInequalities.Analysis.quadraticAt A x₀ b c x + ⟪p, y - x⟫ ≤ FunctionalInequalities.Analysis.quadraticAt A x₀ b c y) ↔
      p = b + Matrix.toEuclideanLin A (x - x₀) := by
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin A
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun z => b + T (z - x₀)
  constructor
  · intro hp
    have hineq (w : EuclideanSpace ℝ (Fin n)) :
        ⟪p - g x, w⟫ ≤ (1 / 2) * ⟪w, T w⟫ := by
      have h₁ := hp (x + w)
      have h₂ := FunctionalInequalities.Analysis.quadraticAt_quadratic_expand hA.1 x₀ b c x w
      have h₁' :
          FunctionalInequalities.Analysis.quadraticAt A x₀ b c x + ⟪p, w⟫ ≤ FunctionalInequalities.Analysis.quadraticAt A x₀ b c (x + w) := by
        simpa only [add_sub_cancel_left] using h₁
      have h₃ : ⟪p, w⟫ = ⟪g x, w⟫ + ⟪p - g x, w⟫ := by
        rw [← inner_add_left]
        congr 1
        abel
      rw [h₂, h₃] at h₁'
      linarith
    have hv : p - g x = 0 := by
      by_contra hv
      let r : ℝ := ⟪p - g x, p - g x⟫
      let q : ℝ := ⟪p - g x, T (p - g x)⟫
      have hr : 0 < r := by
        dsimp [r]
        rw [real_inner_self_eq_norm_sq]
        exact sq_pos_of_pos (norm_pos_iff.mpr hv)
      have hq : 0 ≤ q := by
        dsimp [q]
        exact FunctionalInequalities.Analysis.quadraticAt_nonneg hA _
      let t : ℝ := r / (q + 1)
      have ht : 0 < t := by
        dsimp [t]
        positivity
      have hs : ⟪p - g x, t • (p - g x)⟫ = t * r := by
        calc
          ⟪p - g x, t • (p - g x)⟫ =
              t * ⟪p - g x, p - g x⟫ := by
                rw [real_inner_smul_right]
          _ = t * r := by rfl
      have hsmul (z : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
          ⟪s • z, T (s • z)⟫ = s ^ 2 * ⟪z, T z⟫ := by
        rw [map_smul]
        simp only [real_inner_smul_left, real_inner_smul_right]
        ring
      have hqs :
          ⟪t • (p - g x), T (t • (p - g x))⟫ =
            t ^ 2 * q := by
        rw [hsmul]
      have hi := hineq (t • (p - g x))
      rw [hs, hqs] at hi
      have htq : t * (q + 1) = r := by
        dsimp [t]
        exact div_mul_cancel₀ r (by positivity)
      nlinarith [sq_pos_of_pos ht, hr, hq, htq]
    exact sub_eq_zero.mp hv
  · intro hp y
    have hinc := FunctionalInequalities.Analysis.quadraticAt_quadratic_expand hA.1 x₀ b c x (y - x)
    have harg : x + (y - x) = y := by
      abel
    rw [harg] at hinc
    rw [hp]
    nlinarith [FunctionalInequalities.Analysis.quadraticAt_nonneg hA (y - x)]
