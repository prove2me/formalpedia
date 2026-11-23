-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.zero_kernel_all_ones
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:44.82+00:00
-- url     : https://prove2.me/submissions/14abf269-4c5e-4c16-935b-1408f3162d1e

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_orb_of_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_card_iso_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_cos_eq_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_int_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_phase_one
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
theorem _root_.solution : Formalism.FourierDecayAlt.A5.BaseKernelOne := by
  intro K _ R ψ hψ h h' _ hh hh'
  unfold N0 Kp
  rw [finsum_eq_single _ (cos1 R h, cos1 R h')]
  · obtain ⟨a1, a2⟩ := (cos_eq_iff R h (cos1 R h)).1 rfl
    obtain ⟨b1, b2⟩ := (cos_eq_iff R h' (cos1 R h')).1 rfl
    obtain ⟨i1, j1, k1⟩ := orb_of_int R h hh _ a1 a2
    obtain ⟨i2, j2, k2⟩ := orb_of_int R h' hh' _ b1 b2
    unfold pairTerm
    dsimp only
    rw [if_pos ⟨i1, i2⟩, card_iso_one R j1 k1 j2 k2, phase_one R ψ hψ h _ a1 a2,
      phase_one R ψ hψ h' _ b1 b2]
    simp
  · rintro ⟨q1, q2⟩ hq
    have hnc : ¬ (IsInt R (orbZ h (rep R q1)) ∧ IsInt R (orbZ h' (rep R q2))) := by
      rintro ⟨c1, c2⟩
      exact hq (by rw [(int_iff R h hh q1).1 c1, (int_iff R h' hh' q2).1 c2])
    unfold pairTerm
    dsimp only
    rw [if_neg hnc, zero_mul, zero_mul]
end Formalism.FourierDecayAlt.P
