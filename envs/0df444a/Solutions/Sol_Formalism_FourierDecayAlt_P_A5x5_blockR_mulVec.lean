-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.blockR_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:59.216342+00:00
-- url     : https://prove2.me/submissions/d607be7a-0b20-48a6-96bb-e95662fdaa9b

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
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
variable {K : Type} [CommRing K] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] {R : Subring K}
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution (D : Matrix Unit Unit K) (w : ι ⊕ Unit → K) :
    fromBlocks (1 : Matrix ι ι K) 0 0 D *ᵥ w =
      Sum.elim (w ∘ Sum.inl) (fun _ => D () () * w (Sum.inr ())) := by
  rw [Matrix.fromBlocks_mulVec]
  simp only [Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
  congr 1
  funext u
  cases u
  simp [Matrix.mulVec, dotProduct]
end Formalism.FourierDecayAlt.P.A5x5
