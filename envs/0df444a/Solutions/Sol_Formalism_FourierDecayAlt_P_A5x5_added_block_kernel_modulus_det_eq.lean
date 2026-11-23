-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.added_block_kernel_modulus_det_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:50.326301+00:00
-- url     : https://prove2.me/submissions/0cd705ba-b7e1-40c9-b2fe-da5d12303504

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A5x5_modK_mul__b5e25af6776b
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_det_pt
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_prod_addBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_isUnit_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_kernel_nonzero_modulus_determinant_eq
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
variable {K : Type} [CommRing K] {R : Subring K}
variable [TopologicalSpace K] [IsTopologicalRing K] {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution (hd : LocalDatum K R ψ) (h h' : Point K) (s : ℕ) (t : Kˣ)
    (hne : Ns R ψ s h h' t t ≠ 0) :
    modK R (pt h.1 h.2).det = modK R (pt h'.1 h'.2).det := by
  have hK : Kp R ψ (addBlock h s t) (addBlock h' s t) ≠ 0 := by
    intro h0
    apply hne
    unfold Ns
    rw [h0, mul_zero]
  have e := kernel_nonzero_modulus_determinant_eq hd _ _ hK
  rw [modK_det_pt, modK_det_pt, prod_addBlock, prod_addBlock] at e
  rw [modK_det_pt, modK_det_pt]
  have hu : IsUnit ((t : K) ^ s) := (Units.isUnit t).pow s
  rw [modK_mul' hd (isUnit_prod _) hu, modK_mul' hd (isUnit_prod _) hu] at e
  have hpos : 0 < modK R ((t : K) ^ s) := by
    have := modK_pos hd.isOpen hd.isCompact (t ^ s)
    simpa using this
  exact mul_right_cancel₀ hpos.ne' e
end Formalism.FourierDecayAlt.P.A5x5
