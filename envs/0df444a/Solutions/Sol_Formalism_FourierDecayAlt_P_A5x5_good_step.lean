-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.good_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:12:24.602949+00:00
-- url     : https://prove2.me/submissions/a9925038-adc7-432b-a1f3-6eabe5b31c06

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_LL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_dl_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_sr1
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_dl_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_good_corner
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


attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply

set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {R : Subring K}
variable [TopologicalSpace K] [IsTopologicalRing K] {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution (hd : LocalDatum K R ψ) (hG : Good R ι) : Good R (ι ⊕ Unit) := by
  intro M hM
  haveI := hd.artin
  haveI := hd.red
  have hL : Lat (LL R (ι ⊕ Unit)) := lat_LL hd.isOpen hd.isCompact
  have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have hrow : (∑ i : ι, M (Sum.inr ()) (Sum.inl i) * M⁻¹ (Sum.inl i) (Sum.inr ())) +
      M (Sum.inr ()) (Sum.inr ()) * M⁻¹ (Sum.inr ()) (Sum.inr ()) = 1 := by
    have h := congrFun (congrFun hinv (Sum.inr ())) (Sum.inr ())
    rw [Matrix.mul_apply, Fintype.sum_sum_type] at h
    simpa using h
  obtain ⟨c', hc'⟩ := sr1 (M (Sum.inr ()) (Sum.inr ()))
    (∑ i : ι, M (Sum.inr ()) (Sum.inl i) * M⁻¹ (Sum.inl i) (Sum.inr ()))
    (M⁻¹ (Sum.inr ()) (Sum.inr ())) (by rw [add_comm]; exact hrow)
  set q : Matrix ι Unit K := fun i _ => c' * M⁻¹ (Sum.inl i) (Sum.inr ()) with hq
  have hE : IsUnit (fromBlocks (1 : Matrix ι ι K) q 0 (1 : Matrix Unit Unit K)).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    simp
  have hME : IsUnit (M * fromBlocks (1 : Matrix ι ι K) q 0 (1 : Matrix Unit Unit K)).det := by
    rw [Matrix.det_mul]
    exact hM.mul hE
  have hcorner : IsUnit ((M * fromBlocks (1 : Matrix ι ι K) q 0 (1 : Matrix Unit Unit K))
      (Sum.inr ()) (Sum.inr ())) := by
    have e : (M * fromBlocks (1 : Matrix ι ι K) q 0 (1 : Matrix Unit Unit K)) (Sum.inr ()) (Sum.inr ()) =
        M (Sum.inr ()) (Sum.inr ()) +
          c' * ∑ i : ι, M (Sum.inr ()) (Sum.inl i) * M⁻¹ (Sum.inl i) (Sum.inr ()) := by
      rw [Matrix.mul_apply, Fintype.sum_sum_type, Finset.mul_sum]
      have h1 : ∑ u : Unit, M (Sum.inr ()) (Sum.inr u) *
          (fromBlocks (1 : Matrix ι ι K) q 0 (1 : Matrix Unit Unit K)) (Sum.inr u) (Sum.inr ()) =
          M (Sum.inr ()) (Sum.inr ()) := by
        simp
      rw [h1, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.fromBlocks_apply₁₂, hq]
      ring
    rw [e]
    exact hc'
  have key := good_corner hd hG _ hME hcorner
  rw [dl_mul hL hM hE, dl_upper hd, mul_one, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁] at key
  simpa using key
end Formalism.FourierDecayAlt.P.A5x5
