-- Prove2me | solution 1 for FunctionalInequalities.L2.integral_affineOrthPart_sq_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:45.917101+00:00
-- url     : https://prove2.me/submissions/df47998e-ba85-4d88-956e-88595b65708c

import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition
import Theorems.Thm_FunctionalInequalities_L2_integral_affineOrthPart_readable
import Theorems.Thm_FunctionalInequalities_L2_integral_inner_mul_affineOrthPart_readable
import Theorems.Thm_FunctionalInequalities_L2_memLp_affineOrthPart_readable

open MeasureTheory
open scoped RealInnerProductSpace
section AffineOrthPart
variable {n : ℕ}
/-- **Bessel's inequality for the affine-orthogonal part**: `∫ g̃² ≤ ∫ g²`. -/
theorem solution (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) :
    ∫ x, FunctionalInequalities.L2.affineOrthPart μ g x ^ 2 ∂μ ≤ ∫ x, g x ^ 2 ∂μ := by
    let f := FunctionalInequalities.L2.affineOrthPart μ g
    let P : EuclideanSpace ℝ (Fin n) → ℝ := fun x => g x - f x
    have hf : MemLp f 2 μ := by
      simpa [f] using FunctionalInequalities.L2.memLp_affineOrthPart_readable μ hμ2 hg
    have hP : MemLp P 2 μ := by
      change MemLp (g - f) 2 μ
      exact hg.sub hf
    have hfi : Integrable f μ := hf.integrable (by norm_num)
    have hf2 : Integrable (fun x => f x ^ 2) μ := by
      convert hf.integrable_mul hf using 1;
        ext x; simp [Pi.mul_apply, pow_two]
    have hP2 : Integrable (fun x => P x ^ 2) μ := by
      convert hP.integrable_mul hP using 1;
        ext x; simp [Pi.mul_apply, pow_two]
    have hcrossi : Integrable (fun x => f x * P x) μ :=
      hf.integrable_mul hP
    have hP_formula :
        ∀ x, P x =
          (∫ y, g y ∂μ) +
            ∑ j : Fin n,
              (∫ y,
                ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, y⟫ * g y ∂μ) *
                ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, x⟫ := by
      intro x
      simp [P, f, FunctionalInequalities.L2.affineOrthPart]
      ring
    have hcross : ∫ x, f x * P x ∂μ = 0 := by
      let a : ℝ := ∫ y, g y ∂μ
      let b : Fin n → ℝ := fun j =>
        ∫ y, ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, y⟫ * g y ∂μ
      let q : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun j x =>
        b j * ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, x⟫
      have hinner :
          ∀ j : Fin n,
            MemLp (fun x : EuclideanSpace ℝ (Fin n) =>
              ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, x⟫) 2 μ := by
        intro j
        simpa using
          ((innerSL ℝ ((EuclideanSpace.basisFun (Fin n) ℝ) j)).comp_memLp' hμ2)
      have hq : ∀ j : Fin n, Integrable (fun x => f x * q j x) μ := by
        intro j
        have h := hf.integrable_mul (hinner j)
        dsimp [q, b]
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          h.mul_const
            (∫ y,
              ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, y⟫ * g y ∂μ)
      have hs : Integrable (fun x => f x * ∑ j : Fin n, q j x) μ := by
        have hs' :
            Integrable (fun x => ∑ j : Fin n, f x * q j x) μ := by
          exact
            integrable_finsetSum (s := (Finset.univ : Finset (Fin n)))
              (f := fun j x => f x * q j x) (fun j hj => hq j)
        simpa only [Finset.mul_sum] using hs'
      have hc : Integrable (fun x => f x * a) μ := hfi.mul_const _
      have he :
          ∫ x, f x * (a + ∑ j : Fin n, q j x) ∂μ =
            (∫ x, f x * a ∂μ) +
              ∑ j : Fin n, ∫ x, f x * q j x ∂μ := by
        calc
          ∫ x, f x * (a + ∑ j : Fin n, q j x) ∂μ =
              ∫ x, (f x * a) + (f x * ∑ j : Fin n, q j x) ∂μ := by
                apply integral_congr_ae
                filter_upwards [] with x
                ring
          _ = (∫ x, f x * a ∂μ) +
              ∫ x, f x * ∑ j : Fin n, q j x ∂μ := by
                exact integral_add hc hs
          _ = (∫ x, f x * a ∂μ) +
              ∑ j : Fin n, ∫ x, f x * q j x ∂μ := by
                congr 1
                calc
                  ∫ x, f x * ∑ j : Fin n, q j x ∂μ =
                      ∫ x, ∑ j : Fin n, f x * q j x ∂μ := by
                        apply integral_congr_ae
                        filter_upwards [] with x
                        rw [Finset.mul_sum]
                  _ = ∑ j : Fin n, ∫ x, f x * q j x ∂μ := by
                    simpa using
                      (integral_finsetSum (s := (Finset.univ : Finset (Fin n)))
                        (f := fun j x => f x * q j x)
                        (fun j hj => hq j))
      have hz :
          ∫ x, f x * (a + ∑ j : Fin n, q j x) ∂μ =
            a * (∫ x, f x ∂μ) +
              ∑ j : Fin n, b j *
                (∫ x,
                  ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, x⟫ * f x ∂μ) := by
        rw [he]
        congr 1
        · rw [integral_mul_const]
          ring
        · apply Finset.sum_congr rfl
          intro j hj
          dsimp [q]
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with x
          ring
      calc
        ∫ x, f x * P x ∂μ =
            ∫ x, f x * (a + ∑ j : Fin n, q j x) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              rw [hP_formula x]
        _ = a * (∫ x, f x ∂μ) +
              ∑ j : Fin n, b j *
                (∫ x,
                  ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, x⟫ * f x ∂μ) := hz
        _ = 0 := by
          rw [FunctionalInequalities.L2.integral_affineOrthPart_readable μ hμ2 hμ0 hg]
          simp only [mul_zero, zero_add]
          apply Finset.sum_eq_zero
          intro j hj
          have ho :=
            FunctionalInequalities.L2.integral_inner_mul_affineOrthPart_readable μ hμ2 hμ0 hμcov hg
              ((EuclideanSpace.basisFun (Fin n) ℝ) j)
          dsimp [b, f]
          simpa using congrArg
            (fun z =>
              (∫ y,
                ⟪(EuclideanSpace.basisFun (Fin n) ℝ) j, y⟫ * g y ∂μ) * z) ho
    have hsq :
        (∫ x, g x ^ 2 ∂μ) =
          (∫ x, f x ^ 2 ∂μ) +
            2 * (∫ x, f x * P x ∂μ) +
              ∫ x, P x ^ 2 ∂μ := by
      have hi : Integrable (fun x => 2 * (f x * P x) + P x ^ 2) μ :=
        (hcrossi.const_mul _).add hP2
      have hsplit :
          ∫ x, 2 * (f x * P x) + P x ^ 2 ∂μ =
            (∫ x, 2 * (f x * P x) ∂μ) +
              ∫ x, P x ^ 2 ∂μ :=
        integral_add (hcrossi.const_mul _) hP2
      calc
        ∫ x, g x ^ 2 ∂μ =
            ∫ x, (f x + P x) ^ 2 ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              simp [P]
        _ = ∫ x, (f x ^ 2 + (2 * (f x * P x) + P x ^ 2)) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              ring
        _ = (∫ x, f x ^ 2 ∂μ) +
              ∫ x, (2 * (f x * P x) + P x ^ 2) ∂μ := by
              exact integral_add hf2 hi
        _ = (∫ x, f x ^ 2 ∂μ) +
              (∫ x, 2 * (f x * P x) ∂μ) +
                ∫ x, P x ^ 2 ∂μ := by
              rw [hsplit]
              ring
        _ = (∫ x, f x ^ 2 ∂μ) +
              2 * (∫ x, f x * P x ∂μ) +
                ∫ x, P x ^ 2 ∂μ := by
              rw [integral_const_mul]
    have hnonneg : 0 ≤ ∫ x, P x ^ 2 ∂μ :=
      integral_nonneg fun x => sq_nonneg (P x)
    have hle : ∫ x, f x ^ 2 ∂μ ≤ ∫ x, g x ^ 2 ∂μ := by
      rw [hsq, hcross]
      linarith
    simpa [f] using hle
