-- Prove2me | solution 1 for ClassicalComplexWPT.preparation_factorization_of_sequence_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:15:48.825172+00:00
-- url     : https://prove2.me/submissions/df4aaee7-611d-42e0-af3a-0fd602974654

import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Definitions.Def_ClassicalComplexWPT_PublicExistence
import Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_zero
import Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_add
import Theorems.Thm_ClassicalComplexWPT_preparedPolynomial_preparationCoefficient
import Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_convolution
import Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_eq_sum_fin_of_highShift_eq_zero
import Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_monomialSeq
import Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_smul
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_normalizedOriginCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionOperatorInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionPerturbationMap_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionRhsInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_divisionRemainder
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_divisionRemainderGlobal
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero
attribute [local simp] ClassicalComplexWPT.normalizedOriginCoeffs_apply
attribute [local simp] ClassicalComplexWPT.originWeightedCoeffs_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionOperatorInput_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionPerturbationMap_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionRhsInput_apply
attribute [local simp] ClassicalComplexWPT.seqHighShift_divisionRemainder
attribute [local simp] ClassicalComplexWPT.seqHighShift_divisionRemainderGlobal
attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply


attribute [local simp] ClassicalComplexWPT.evalL1PowerSeries_zero

set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ}
    {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (hr0 : 0 < r)
    (htop : originWeightedCoeffs p r hr d ≠ 0)
    (z : Base n) (w : ℂ)
    (hfac : monomialSeq d =
      convolution (normalizedPreparationQuotient p r hr d z)
        (analyticNormalizedCoefficientMap p r hr d z) +
          normalizedPreparationRemainder p r hr d z)
    (hsupp : seqHighShift d (normalizedPreparationRemainder p r hr d z) = 0)
    (hw : ‖(r : ℂ)⁻¹ * w‖ < 1)
    (hrecon : evalL1PowerSeries ((weightedCoefficientSeries p r).sum z)
        ((r : ℂ)⁻¹ * w) = f (z, w))
    (hQne : preparationQuotientEval p r hr d (z, w) ≠ 0) :
    f (z, w) = preparationUnit p r hr d (z, w) *
      preparedPolynomial d (preparationCoefficient p r hr d) (z, w) := by
  let t : ℂ := (r : ℂ)⁻¹ * w
  let q : OriginSeq := normalizedPreparationQuotient p r hr d z
  let rem : OriginSeq := normalizedPreparationRemainder p r hr d z
  let C : OriginSeq := (weightedCoefficientSeries p r).sum z
  let D : ℂ := originWeightedCoeffs p r hr d
  have hD : D ≠ 0 := htop
  have hEvalFac := congrArg (fun a : OriginSeq ↦ evalL1PowerSeries a t) hfac
  have hG : analyticNormalizedCoefficientMap p r hr d z = D⁻¹ • C := rfl
  have hseries :
      t ^ d = evalL1PowerSeries q t * (D⁻¹ * evalL1PowerSeries C t) +
        ∑ i : Fin d, rem i * t ^ (i : ℕ) := by
    rw [evalL1PowerSeries_monomialSeq d hw, evalL1PowerSeries_add,
      evalL1PowerSeries_convolution _ _ hw, hG, evalL1PowerSeries_smul,
      evalL1PowerSeries_eq_sum_fin_of_highShift_eq_zero d rem hsupp hw] at hEvalFac
    simpa only [q, rem] using hEvalFac
  rw [preparedPolynomial_preparationCoefficient p r hr d hr0 z w]
  rw [← hrecon]
  simp only [preparationUnit, preparationQuotientEval]
  rw [← mul_pow]
  change evalL1PowerSeries C t =
    (D * (r : ℂ)⁻¹ ^ d) * (evalL1PowerSeries q t)⁻¹ *
      ((r : ℂ) ^ d * (t ^ d - ∑ i : Fin d, rem i * t ^ (i : ℕ)))
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hQ : evalL1PowerSeries q t ≠ 0 := hQne
  let R : ℂ := ∑ i : Fin d, rem i * t ^ (i : ℕ)
  calc
    evalL1PowerSeries C t =
        D * (evalL1PowerSeries q t)⁻¹ * (t ^ d - R) := by
      rw [hseries]
      field_simp [hD, hQ]
      ring
    _ = (D * (r : ℂ)⁻¹ ^ d) * (evalL1PowerSeries q t)⁻¹ *
        ((r : ℂ) ^ d * (t ^ d - R)) := by
      have hrpow : (r : ℂ) ^ d * (r : ℂ)⁻¹ ^ d = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hrC, one_pow]
      calc
        D * (evalL1PowerSeries q t)⁻¹ * (t ^ d - R) =
            D * (evalL1PowerSeries q t)⁻¹ * (1 * (t ^ d - R)) := by rw [one_mul]
        _ = _ := by rw [← hrpow]; ring
end ClassicalComplexWPT
