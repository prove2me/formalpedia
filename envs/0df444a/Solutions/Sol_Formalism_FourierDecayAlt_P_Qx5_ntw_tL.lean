-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.ntw_tL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:00:58.316115+00:00
-- url     : https://prove2.me/submissions/ae9c9b81-7c49-462d-90a7-1d2957b09158

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_ntw_qminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Qx2
variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution (hD : IsOpen D) (φ : E →L[ℂ] E') (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2) :
    Ntw k r i D φ (fun f => tL k r z z' i Y p q f) (fun f => tL k r z z' i Y p q f) := by
  intro f hf x hx
  fin_cases p <;> fin_cases q
  · exact ntw_qminor hD φ id id _ f hf x hx
  · show -(chatL _ _ _ _ _ _ x) = φ (-(chatL _ _ _ _ _ f x))
    simp only [chatL, map_neg, map_sum, map_smul]
    congr 1
    refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun j₁ _ => ?_
    exact congrArg _ (ntw_qminor hD φ (skip1 i₁) (skip1 j₁) _ f hf x hx)
  · show -(chatL _ _ _ _ _ _ x) = φ (-(chatL _ _ _ _ _ f x))
    simp only [chatL, map_neg, map_sum, map_smul]
    congr 1
    refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun j₁ _ => ?_
    exact congrArg _ (ntw_qminor hD φ (skip1 i₁) (skip1 j₁) _ f hf x hx)
  · show -(chat2L _ _ _ _ _ _ _ _ x) = φ (-(chat2L _ _ _ _ _ _ _ f x))
    simp only [chat2L, map_neg, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun i₂ _ => Finset.sum_congr rfl fun j₁ _ =>
      Finset.sum_congr rfl fun j₂ _ => ?_
    split_ifs
    · rw [map_smul]
      exact congrArg _ (ntw_qminor hD φ (skip2 i₁ i₂) (skip2 j₁ j₂) _ f hf x hx)
    · simp
end Formalism.FourierDecayAlt.P.Qx5
