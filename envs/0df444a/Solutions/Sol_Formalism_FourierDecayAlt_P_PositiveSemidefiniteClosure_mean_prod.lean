-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.mean_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:27.579687+00:00
-- url     : https://prove2.me/submissions/0fc168f9-aec6-412d-b5cd-42916cf5a704

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedVectorChoices
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
open Classical
namespace Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
theorem _root_.solution {K : Type} [CommRing K] (hCM : CharMean) (R : Subring K) (ψ : AddChar K ℂ)
    (L₁ L₂ : AddSubgroup K) (A B : Finset K) (le₁ : L₁ ≤ R.toAddSubgroup)
    (le₂ : R.toAddSubgroup ≤ L₂) (hA : IsReps A L₂ R.toAddSubgroup)
    (hB : IsReps B R.toAddSubgroup L₁) (a : K) (ha : a ∈ perp ψ L₁) :
    ((A.card : ℂ) * (B.card : ℂ))⁻¹ * ∑ p ∈ A ×ˢ B, ψ (a * (p.1 + p.2)) =
      if a ∈ perp ψ L₂ then 1 else 0 := by
  have e : ((A.card : ℂ) * (B.card : ℂ))⁻¹ * ∑ p ∈ A ×ˢ B, ψ (a * (p.1 + p.2)) =
      ((A.card : ℂ)⁻¹ * ∑ ρ ∈ A, ψ (a * ρ)) * ((B.card : ℂ)⁻¹ * ∑ b ∈ B, ψ (a * b)) := by
    rw [Finset.sum_product, mul_inv]
    simp only [mul_add, AddChar.map_add_eq_mul]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [e, hCM K ψ L₁ R.toAddSubgroup B le₁ hB a ha]
  by_cases hR : a ∈ perp ψ R.toAddSubgroup
  · rw [if_pos hR, mul_one, hCM K ψ R.toAddSubgroup L₂ A le₂ hA a hR]
  · rw [if_neg hR, mul_zero, if_neg]
    intro h2
    exact hR fun l hl => h2 l (le₂ hl)
end Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
