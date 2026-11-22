-- Prove2me | solution 1 for BornVolume.injOn_PsiN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:16.585862+00:00
-- url     : https://prove2.me/submissions/a4a327bb-f78e-4ec8-8e1d-fe8cabfa192e

module
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Matrix.Block
public import Definitions.Def_BornVolumeLean_Volume_MomentMarginalUniform
public import Definitions.Def_BornVolumeLean_MeasureTheory_LintegralFintypeProd
public import Definitions.Def_BornVolumeLean_Volume_MomentRatioUniformN
public import Theorems.Thm_BornVolume_PsiN_sum

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Real Set
open scoped ENNReal
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution : InjOn (PsiN (M := M)) domainN := by
  intro y hy y' hy' heq
  obtain ⟨_, _, hS⟩ := hy
  -- S = S' from the total sum.
  have hSeq : y (Fin.last M) = y' (Fin.last M) := by
    rw [← PsiN_sum y, ← PsiN_sum y', heq]
  -- Extensionality via Fin.lastCases: last coord is S, castSucc coords cancel.
  funext i
  induction i using Fin.lastCases with
  | last => exact hSeq
  | cast k =>
    have hk : PsiN y (Fin.castSucc k) = PsiN y' (Fin.castSucc k) := by rw [heq]
    simp only [PsiN, Fin.lastCases_castSucc] at hk
    rw [hSeq] at hk
    exact mul_right_cancel₀ (ne_of_gt (hSeq ▸ hS)) hk
end BornVolume
