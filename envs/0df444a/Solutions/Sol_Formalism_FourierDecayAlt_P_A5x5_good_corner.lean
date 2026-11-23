-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.good_corner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:03.016585+00:00
-- url     : https://prove2.me/submissions/4fcb5929-de72-4bfc-a847-51ba966f3c06

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_LL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_dl_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_dl_blockL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_dl_blockR
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A5x5_modK_mul__b5e25af6776b
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_dl_lower
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_dl_upper
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
theorem _root_.solution (hd : LocalDatum K R ψ) (hG : Good R ι) (M : Matrix (ι ⊕ Unit) (ι ⊕ Unit) K)
    (hM : IsUnit M.det) (hc : IsUnit (M (Sum.inr ()) (Sum.inr ()))) : dl R M = modK R M.det := by
  have hL : Lat (LL R (ι ⊕ Unit)) := lat_LL hd.isOpen hd.isCompact
  set A := M.toBlocks₁₁ with hA
  set B := M.toBlocks₁₂ with hB
  set C := M.toBlocks₂₁ with hC
  set D := M.toBlocks₂₂ with hD
  have hDd : D.det = D () () := Matrix.det_unique D
  have hc1 : IsUnit (D () ()) := hc
  have hDdet : IsUnit D.det := by rw [hDd]; exact hc1
  letI := Matrix.invertibleOfIsUnitDet D hDdet
  have hMeq : M = fromBlocks A B C D := (Matrix.fromBlocks_toBlocks M).symm
  have hfac := Matrix.fromBlocks_eq_of_invertible₂₂ A B C D
  have hdet := Matrix.det_fromBlocks₂₂ A B C D
  rw [← hMeq] at hfac hdet
  set S := A - B * ⅟D * C with hS
  have hSdet : IsUnit S.det := by
    have h : IsUnit (D.det * S.det) := hdet ▸ hM
    exact isUnit_of_mul_isUnit_right h
  have hU : IsUnit (fromBlocks (1 : Matrix ι ι K) (B * ⅟D) 0 (1 : Matrix Unit Unit K)).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    simp
  have hLw : IsUnit (fromBlocks (1 : Matrix ι ι K) 0 (⅟D * C) (1 : Matrix Unit Unit K)).det := by
    rw [Matrix.det_fromBlocks_zero₁₂]
    simp
  have hDg : IsUnit (fromBlocks S 0 0 D).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    exact hSdet.mul hDdet
  have hDg' : fromBlocks S 0 0 D =
      fromBlocks S 0 0 (1 : Matrix Unit Unit K) * fromBlocks (1 : Matrix ι ι K) 0 0 D := by
    rw [Matrix.fromBlocks_multiply]
    simp
  have hS1 : IsUnit (fromBlocks S 0 0 (1 : Matrix Unit Unit K)).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    simpa using hSdet
  have hD1 : IsUnit (fromBlocks (1 : Matrix ι ι K) 0 0 D).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    simpa using hDdet
  have hUD : IsUnit (fromBlocks (1 : Matrix ι ι K) (B * ⅟D) 0 (1 : Matrix Unit Unit K) *
      fromBlocks S 0 0 D).det := by
    rw [Matrix.det_mul]
    exact hU.mul hDg
  conv_lhs => rw [hfac]
  rw [dl_mul hL hUD hLw, dl_mul hL hU hDg, dl_upper hd, dl_lower hd, hDg', dl_mul hL hS1 hD1,
    dl_blockL, dl_blockR, hG S hSdet, hdet, one_mul, mul_one, hDd, modK_mul' hd hc1 hSdet, mul_comm]
end Formalism.FourierDecayAlt.P.A5x5
