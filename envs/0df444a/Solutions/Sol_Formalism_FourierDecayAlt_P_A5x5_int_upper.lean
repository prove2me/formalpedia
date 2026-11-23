-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.int_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:59.170631+00:00
-- url     : https://prove2.me/submissions/aecd8210-488a-401f-b09d-1b4575552870

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
variable {K : Type} [CommRing K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {R : Subring K}
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution {s : Matrix ι Unit K} (hs : ∀ i, s i () ∈ R) (a b : ι ⊕ Unit) :
    (fromBlocks (1 : Matrix ι ι K) s 0 (1 : Matrix Unit Unit K)) a b ∈ R := by
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply] <;>
    (try split_ifs) <;>
    first | exact R.one_mem | exact R.zero_mem | exact hs _
end Formalism.FourierDecayAlt.P.A5x5
