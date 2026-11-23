-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.dl_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:43.460445+00:00
-- url     : https://prove2.me/submissions/ebbe1a9a-c24f-4851-bedf-2cb2f7d239cd

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_dl_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_LL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_dl_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_dl_blockR
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_exists_pow_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_int_upper
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A5x5_modK_mul__b5e25af6776b
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
theorem _root_.solution (hd : LocalDatum K R ψ) (r : Matrix ι Unit K) :
    dl R (fromBlocks (1 : Matrix ι ι K) r 0 (1 : Matrix Unit Unit K)) = 1 := by
  obtain ⟨ϖ, hϖR, hϖ⟩ := hd.unif
  obtain ⟨m, hm⟩ := exists_pow_mem hϖR hϖ (fun i => r i ())
  have hL : Lat (LL R (ι ⊕ Unit)) := lat_LL hd.isOpen hd.isCompact
  set u : Kˣ := ϖ ^ m with hu
  set D : Matrix Unit Unit K := Matrix.diagonal fun _ => (u : K) with hD
  set Di : Matrix Unit Unit K := Matrix.diagonal fun _ => ((u⁻¹ : Kˣ) : K) with hDi
  have hDD : D * Di = 1 := by
    rw [hD, hDi, Matrix.diagonal_mul_diagonal]
    simp
  set s : Matrix ι Unit K := r * D with hs_def
  have hs : ∀ i, s i () ∈ R := by
    intro i
    rw [hs_def, hD, Matrix.mul_diagonal, mul_comm]
    simpa [hu] using hm i
  have hfac : fromBlocks (1 : Matrix ι ι K) r 0 (1 : Matrix Unit Unit K) =
      fromBlocks (1 : Matrix ι ι K) 0 0 D * fromBlocks (1 : Matrix ι ι K) s 0 1 *
        fromBlocks (1 : Matrix ι ι K) 0 0 Di := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
    rw [hs_def, Matrix.mul_assoc, hDD, Matrix.mul_one]
  have hdet1 : IsUnit (fromBlocks (1 : Matrix ι ι K) 0 0 D).det := by
    rw [Matrix.det_fromBlocks_zero₂₁, hD, Matrix.det_diagonal]
    simp
  have hdet2 : IsUnit (fromBlocks (1 : Matrix ι ι K) s 0 (1 : Matrix Unit Unit K)).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    simp
  have hdet3 : IsUnit (fromBlocks (1 : Matrix ι ι K) 0 0 Di).det := by
    rw [Matrix.det_fromBlocks_zero₂₁, hDi, Matrix.det_diagonal]
    simp
  have h12 : IsUnit (fromBlocks (1 : Matrix ι ι K) 0 0 D *
      fromBlocks (1 : Matrix ι ι K) s 0 (1 : Matrix Unit Unit K)).det := by
    rw [Matrix.det_mul]
    exact hdet1.mul hdet2
  have hone : dl R (fromBlocks (1 : Matrix ι ι K) s 0 (1 : Matrix Unit Unit K)) = 1 :=
    dl_eq_one (N := fromBlocks (1 : Matrix ι ι K) (-s) 0 1)
      (by rw [Matrix.fromBlocks_multiply]; simp) (int_upper hs)
      (int_upper fun i => by simpa using R.neg_mem (hs i))
  rw [hfac, dl_mul hL h12 hdet3, dl_mul hL hdet1 hdet2, hone, dl_blockR, dl_blockR, mul_one, hDi, hD]
  simp only [Matrix.diagonal_apply_eq]
  rw [← modK_mul' hd (Units.isUnit _) (Units.isUnit _)]
  simp [modK_one]
end Formalism.FourierDecayAlt.P.A5x5
