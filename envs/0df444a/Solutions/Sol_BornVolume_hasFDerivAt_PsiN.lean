-- Prove2me | solution 1 for BornVolume.hasFDerivAt_PsiN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:04.547821+00:00
-- url     : https://prove2.me/submissions/6f66118f-e1db-4e80-a4ef-a51d6a0d395f

module
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Matrix.Block
public import Definitions.Def_BornVolumeLean_Volume_MomentMarginalUniform
public import Definitions.Def_BornVolumeLean_MeasureTheory_LintegralFintypeProd
public import Definitions.Def_BornVolumeLean_Volume_MomentRatioUniformN

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Real Set
open scoped ENNReal
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (y : Fin (M + 1) → ℝ) : HasFDerivAt PsiN (psiFDerivN y) y := by
  -- `psiFDerivN y = pi (fun i => (proj i).comp (psiFDerivN y))`, so it suffices to
  -- prove each component `(PsiN · i)` has derivative `(proj i).comp (psiFDerivN y)`.
  have hpi : psiFDerivN y
      = ContinuousLinearMap.pi (fun i =>
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (M + 1) => ℝ) i).comp
            (psiFDerivN y)) := by
    ext v i; rfl
  rw [hpi, hasFDerivAt_pi]
  intro i
  -- Component derivative equals `(proj i).comp (psiFDerivN y)`; prove by matching the
  -- explicit `.mul`/affine derivative to the matrix row (the `psiMat` row evaluation).
  induction i using Fin.lastCases with
  | last =>
    -- component: y ↦ (1 − ∑ y∘castSucc) · y last
    have hcomp : (fun x : Fin (M + 1) → ℝ => PsiN x (Fin.last M))
        = fun x => (1 - ∑ k, x (Fin.castSucc k)) * x (Fin.last M) := by
      funext x; simp [PsiN]
    rw [hcomp]
    have hbase :
        HasFDerivAt (fun x : Fin (M + 1) → ℝ => (1 - ∑ k, x (Fin.castSucc k)) * x (Fin.last M))
          ((((1 : ℝ) - ∑ k, y (Fin.castSucc k)) •
              ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (M + 1) => ℝ) (Fin.last M))
            + (y (Fin.last M)) •
              (((0 : (Fin (M + 1) → ℝ) →L[ℝ] ℝ)) -
                ∑ k, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (M + 1) => ℝ)
                  (Fin.castSucc k))) y := by
      apply HasFDerivAt.mul
      · exact (hasFDerivAt_const (1 : ℝ) y).sub
          (HasFDerivAt.fun_sum (fun k _ => hasFDerivAt_apply (𝕜 := ℝ) (Fin.castSucc k) y))
      · exact hasFDerivAt_apply (𝕜 := ℝ) (Fin.last M) y
    refine hbase.congr_fderiv ?_
    ext v
    show _ = (psiFDerivN y v) (Fin.last M)
    rw [psiFDerivN]
    show _ = (Matrix.toLin' (psiMat (y (Fin.last M)) (fun k => y (Fin.castSucc k))) v) (Fin.last M)
    rw [Matrix.toLin'_apply]
    show _ = ∑ j, psiMat (y (Fin.last M)) (fun k => y (Fin.castSucc k)) (Fin.last M) j * v j
    rw [Fin.sum_univ_castSucc]
    simp only [psiMat, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last,
      add_apply, FunLike.coe_smul, Pi.smul_apply,
      sub_apply, zero_apply,
      FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul]
    simp only [zero_sub, Finset.mul_sum, mul_neg, neg_mul, Finset.sum_neg_distrib]
    ring
  | cast k =>
    have hcomp : (fun x : Fin (M + 1) → ℝ => PsiN x (Fin.castSucc k))
        = fun x => x (Fin.castSucc k) * x (Fin.last M) := by
      funext x; simp [PsiN]
    rw [hcomp]
    have hbase :
        HasFDerivAt (fun x : Fin (M + 1) → ℝ => x (Fin.castSucc k) * x (Fin.last M))
          (y (Fin.castSucc k) •
              ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (M + 1) => ℝ) (Fin.last M)
            + y (Fin.last M) •
              ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (M + 1) => ℝ) (Fin.castSucc k)) y :=
      (hasFDerivAt_apply (𝕜 := ℝ) (Fin.castSucc k) y).mul (hasFDerivAt_apply (𝕜 := ℝ) (Fin.last M) y)
    refine hbase.congr_fderiv ?_
    ext v
    show _ = (psiFDerivN y v) (Fin.castSucc k)
    rw [psiFDerivN]
    show _ = (Matrix.toLin' (psiMat (y (Fin.last M)) (fun k => y (Fin.castSucc k))) v) (Fin.castSucc k)
    rw [Matrix.toLin'_apply]
    show _ = ∑ j, psiMat (y (Fin.last M)) (fun k => y (Fin.castSucc k)) (Fin.castSucc k) j * v j
    rw [Fin.sum_univ_castSucc]
    simp only [psiMat, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last,
      add_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · simp; ring
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ k) h
end BornVolume
