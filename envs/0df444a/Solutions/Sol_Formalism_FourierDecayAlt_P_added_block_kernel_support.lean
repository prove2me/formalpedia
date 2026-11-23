-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.added_block_kernel_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:33.33396+00:00
-- url     : https://prove2.me/submissions/22fba592-8e77-4a29-903a-b20b2fdbc265

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_supp_one
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
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x7
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.NsSupport := by
  intro K _ R ψ s hs h h' t t' hN
  have hK : Kp R ψ (addBlock h s t) (addBlock h' s t') ≠ 0 := by
    intro h0
    apply hN
    unfold Ns
    rw [h0, mul_zero]
  obtain ⟨q, hq⟩ : ∃ q, pairTerm R ψ (addBlock h s t) (addBlock h' s t') q ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hK
    unfold Kp
    simp only [hc, finsum_zero]
  have hc : IsInt R (orbZ (addBlock h s t) (rep R q.1)) ∧
      IsInt R (orbZ (addBlock h' s t') (rep R q.2)) := by
    by_contra hc
    apply hq
    unfold pairTerm
    rw [if_neg hc, zero_mul, zero_mul]
  exact ⟨supp_one R h s hs t _ hc.1, supp_one R h' s hs t' _ hc.2⟩
end Formalism.FourierDecayAlt.P
