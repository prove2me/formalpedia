-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.uBlock_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:49.75088+00:00
-- url     : https://prove2.me/submissions/3fffead8-a351-40f6-961c-b21e79227ba7

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
namespace Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
theorem _root_.solution : UBlock := by
  intro hB hC hM K _ _ _ R ψ hD m cr S h h' t t' ht hdet
  unfold uGram
  have : ∀ x : K ⧸ R.toAddSubgroup, Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) = 0 := by
    intro x
    by_contra hne
    have h1 := hB K R ψ hD _ _ hne
    have c1 := hC K R ψ hD (addBlock h m t) 1 (cr x)
    have c2 := hC K R ψ hD (addBlock h' m t') 1 (cr x)
    rw [hC K R ψ hD h m t] at c1
    rw [hC K R ψ hD h' m t'] at c2
    have h3 : cSize R (pt2 h m t (cr x)) = cSize R (pt2 h' m t' (cr x)) := by
      unfold cSize; rw [h1]
    unfold pt2 at h3
    rw [c1, c2, ht] at h3
    obtain ⟨hb, _⟩ := hM K R ψ hD t' t
    obtain ⟨hc, _⟩ := hM K R ψ hD (cr x) t
    have : cSize R h = cSize R h' := by
      have hb' := ne_of_gt hb
      have hc' := ne_of_gt hc
      have k1 : ((modK R (t' : K)) ^ m)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hb')
      have k2 : ((modK R ((cr x : Kˣ) : K)) ^ 1)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hc')
      exact mul_right_cancel₀ k1 (mul_right_cancel₀ k2 h3)
    unfold cSize at this
    exact hdet (inv_injective this)
  simp [this]
end Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
