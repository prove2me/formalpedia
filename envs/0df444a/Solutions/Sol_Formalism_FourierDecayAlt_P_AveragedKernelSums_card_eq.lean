-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AveragedKernelSums.card_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:22.343788+00:00
-- url     : https://prove2.me/submissions/5142ab96-72e8-4cac-80b0-8eea2d0ef457

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_reps_card
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_R_le_perp
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
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



set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.AveragedKernelSums
open Formalism.FourierDecayAlt.P.A5x6
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.AveragedKernelSums
theorem _root_.solution (hL : LocalDatum K R ψ) {L₁ : AddSubgroup K} (hle : L₁ ≤ R.toAddSubgroup)
    (B : Finset K) (hB : IsReps B R.toAddSubgroup L₁)
    (hvol : volL R L₁ * volL R (perp ψ L₁) = 1) :
    R.toAddSubgroup.relIndex (perp ψ L₁) = B.card := by
  have h1 : R.toAddSubgroup.relIndex L₁ = 1 := AddSubgroup.relIndex_eq_one.mpr hle
  have h2 : (perp ψ L₁).relIndex R.toAddSubgroup = 1 :=
    AddSubgroup.relIndex_eq_one.mpr (R_le_perp hL hle)
  have h3 := reps_card _ _ B hB
  unfold volL at hvol
  rw [h1, h2, h3] at hvol
  have hB0 : (B.card : ℝ) ≠ 0 := by
    intro h0
    rw [h0] at hvol
    simp at hvol
  have : ((R.toAddSubgroup.relIndex (perp ψ L₁) : ℕ) : ℝ) = (B.card : ℝ) := by
    field_simp at hvol
    linarith
  exact_mod_cast this
end Formalism.FourierDecayAlt.P.AveragedKernelSums
