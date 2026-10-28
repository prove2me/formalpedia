-- Prove2me | solution 1 for FunctionalInequalities.L2.integral_inner_mul_affineOrthPart_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:41:48.233839+00:00
-- url     : https://prove2.me/submissions/885367a4-bdf5-4807-baf4-243bde6100a1

import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition

open MeasureTheory
open scoped RealInnerProductSpace
section AffineOrthPart
variable {n : ℕ}
/-- The affine-orthogonal part is orthogonal to every linear function. -/
theorem solution (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) (u : EuclideanSpace ℝ (Fin n)) :
    ∫ x, ⟪u, x⟫ * FunctionalInequalities.L2.affineOrthPart μ g x ∂μ = 0 := by
    have hu : MemLp (fun x : EuclideanSpace ℝ (Fin n) => ⟪u, x⟫) 2 μ := by
      simpa [Function.comp_def] using (innerSL ℝ u).comp_memLp' hμ2
    have hlin : ∀ v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪v, x⟫ ∂μ = 0 := by
      intro v
      simpa [Function.comp_def, hμ0] using
        (innerSL ℝ v).integral_comp_comm (hμ2.integrable one_le_two)
    have hbasis :
        ∀ j : Fin n,
          MemLp (fun x : EuclideanSpace ℝ (Fin n) =>
            ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) 2 μ := by
      intro j
      simpa [Function.comp_def] using
        (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).comp_memLp' hμ2
    have h₁ : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ⟪u, x⟫ * g x) μ :=
      hu.integrable_mul hg
    have h₂ :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ⟪u, x⟫ * ∫ y, g y ∂μ) μ := by
      simpa [mul_comm] using
        ((hu.integrable one_le_two).const_mul (∫ y, g y ∂μ))
    have h₃ :
        ∀ j : Fin n,
          Integrable
            (fun x : EuclideanSpace ℝ (Fin n) =>
              ⟪u, x⟫ *
                ((∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫)) μ := by
      intro j
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((hu.integrable_mul (hbasis j)).const_mul
          (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ))
    have hsum :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ⟪u, x⟫ *
              ∑ j,
                (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) μ := by
      simpa only [Finset.mul_sum] using
        (integrable_finsetSum _ (fun j hj => h₃ j))
    have hsum_eval :
        ∫ x, ⟪u, x⟫ *
            ∑ j,
              (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ ∂μ =
          ∑ j,
            (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
              ⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫ := by
      calc
        ∫ x, ⟪u, x⟫ *
            ∑ j,
              (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ ∂μ
            =
            ∫ x, ∑ j,
              ⟪u, x⟫ *
                ((∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) ∂μ := by
              congr 1
              funext x
              rw [Finset.mul_sum]
        _ = ∑ j, ∫ x,
              ⟪u, x⟫ *
                ((∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) ∂μ := by
              simpa using
                (integral_finsetSum
                  (μ := μ) (s := Finset.univ)
                  (f := fun j x =>
                    ⟪u, x⟫ *
                      ((∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                        ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫))
                  (fun j hj => h₃ j))
        _ = ∑ j,
            (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
              ⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫ := by
              apply Finset.sum_congr rfl
              intro j hj
              calc
                ∫ x, ⟪u, x⟫ *
                    ((∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                      ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) ∂μ
                    =
                    (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                      ∫ x, ⟪u, x⟫ *
                        ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ ∂μ := by
                      rw [← integral_const_mul]
                      congr 1
                      funext x
                      ring
                _ = _ := by
                  rw [hμcov u (EuclideanSpace.basisFun (Fin n) ℝ j)]
    have hgj :
        ∀ j : Fin n,
          Integrable
            (fun x : EuclideanSpace ℝ (Fin n) =>
              ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ * g x) μ := by
      intro j
      exact (hbasis j).integrable_mul hg
    have hfinal :
        ∫ x, ⟪u, x⟫ * g x ∂μ =
          ∑ j,
            ⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫ *
              (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) := by
      calc
        ∫ x, ⟪u, x⟫ * g x ∂μ =
            ∫ x,
              (∑ j,
                ⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫ *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) * g x ∂μ := by
              congr 1
              funext x
              rw [(EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner u x]
        _ = ∫ x, ∑ j,
              (⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫ *
                ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) * g x ∂μ := by
              congr 1
              funext x
              rw [Finset.sum_mul]
        _ = ∑ j, ∫ x,
              (⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫ *
                ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) * g x ∂μ := by
              simpa using
                (integral_finsetSum
                  (μ := μ) (s := Finset.univ)
                  (f := fun j x =>
                    (⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫ *
                      ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) * g x)
                  (fun j hj => by
                    simpa [mul_assoc] using
                      (hgj j).const_mul
                        ⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫))
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← integral_const_mul]
          congr 1
          funext y
          ring
    unfold FunctionalInequalities.L2.affineOrthPart
    have hpoint :
        (fun x : EuclideanSpace ℝ (Fin n) =>
          ⟪u, x⟫ *
            (g x - ∫ y, g y ∂μ -
              ∑ j,
                (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫)) =
        (fun x =>
          (⟪u, x⟫ * g x - ⟪u, x⟫ * ∫ y, g y ∂μ) -
            ⟪u, x⟫ *
              ∑ j,
                (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) := by
      funext x
      ring
    rw [hpoint]
    calc
      ∫ x,
          (⟪u, x⟫ * g x - ⟪u, x⟫ * ∫ y, g y ∂μ) -
            ⟪u, x⟫ *
              ∑ j,
                (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ ∂μ
          =
          (∫ x, ⟪u, x⟫ * g x ∂μ -
            ∫ x, ⟪u, x⟫ * ∫ y, g y ∂μ ∂μ) -
            ∫ x, ⟪u, x⟫ *
              ∑ j,
                (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                  ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ ∂μ := by
            calc
              ∫ x,
                  (⟪u, x⟫ * g x - ⟪u, x⟫ * ∫ y, g y ∂μ) -
                    ⟪u, x⟫ *
                      ∑ j,
                        (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ *
                          g y ∂μ) *
                          ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ ∂μ
                  =
                  ∫ x, (⟪u, x⟫ * g x - ⟪u, x⟫ * ∫ y, g y ∂μ) ∂μ -
                    ∫ x, ⟪u, x⟫ *
                      ∑ j,
                        (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ *
                          g y ∂μ) *
                          ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ ∂μ := by
                      exact integral_sub (h₁.sub h₂) hsum
              _ = _ := by
                rw [integral_sub h₁ h₂]
    _ = ∫ x, ⟪u, x⟫ * g x ∂μ -
            ∑ j,
              (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
                ⟪u, EuclideanSpace.basisFun (Fin n) ℝ j⟫ := by
      rw [integral_mul_const, hlin u, hsum_eval]
      ring
    _ = 0 := by
      rw [hfinal]
      simp only [mul_comm]
      exact sub_self _
