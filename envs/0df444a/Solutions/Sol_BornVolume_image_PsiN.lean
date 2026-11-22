-- Prove2me | solution 1 for BornVolume.image_PsiN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:38.250391+00:00
-- url     : https://prove2.me/submissions/bdf1d27a-a442-4541-b6c3-470695ce35c9

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
theorem _root_.solution : PsiN '' (domainN : Set (Fin (M + 1) → ℝ)) = posQuadrant := by
  ext s
  simp only [mem_image, domainN, posQuadrant, Set.mem_ofPred_eq]
  constructor
  · -- (⊆) every coordinate of Ψ_N y is positive on the domain.
    rintro ⟨y, ⟨ht, hsum, hS⟩, rfl⟩ i
    induction i using Fin.lastCases with
    | last =>
      simp only [PsiN, Fin.lastCases_last]
      exact mul_pos (by linarith) hS
    | cast k =>
      simp only [PsiN, Fin.lastCases_castSucc]
      exact mul_pos (ht k) hS
  · -- (⊇) given positive s, the inverse is S = ∑ s, t_k = s(castSucc k)/S.
    intro hs
    set S : ℝ := ∑ i, s i with hSdef
    have hSpos : 0 < S := Finset.sum_pos (fun i _ => hs i) ⟨Fin.last M, Finset.mem_univ _⟩
    refine ⟨Fin.lastCases S (fun k => s (Fin.castSucc k) / S), ⟨?_, ?_, ?_⟩, ?_⟩
    · -- t_k = s(castSucc k)/S > 0
      intro k; simp only [Fin.lastCases_castSucc]; exact div_pos (hs _) hSpos
    · -- ∑_k s(castSucc k)/S < 1: the omitted last term s(last)/S is positive.
      simp only [Fin.lastCases_castSucc, ← Finset.sum_div]
      rw [div_lt_one hSpos]
      have hsplit : S = (∑ k, s (Fin.castSucc k)) + s (Fin.last M) := by
        rw [hSdef, Fin.sum_univ_castSucc]
      rw [hsplit]; linarith [hs (Fin.last M)]
    · -- last coord = S > 0
      simp only [Fin.lastCases_last]; exact hSpos
    · -- Ψ_N (inverse) = s
      funext i
      induction i using Fin.lastCases with
      | last =>
        simp only [PsiN, Fin.lastCases_last, Fin.lastCases_castSucc, ← Finset.sum_div]
        rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hSpos), one_mul, hSdef,
          Fin.sum_univ_castSucc]
        ring
      | cast k =>
        simp only [PsiN, Fin.lastCases_castSucc, Fin.lastCases_last]
        rw [div_mul_cancel₀ _ (ne_of_gt hSpos)]
end BornVolume
