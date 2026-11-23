-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.gi_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:00.268937+00:00
-- url     : https://prove2.me/submissions/2cf208fc-2dd9-45b0-ad4c-c5a172ba297c

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_of_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_relIndex_ne_zero
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
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {V W : Type} [AddCommGroup V] [AddCommGroup W]
variable [TopologicalSpace V] [IsTopologicalAddGroup V]
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution {A B C : AddSubgroup V} (hA : Lat A) (hB : Lat B) (hC : Lat C) :
    gi A B * gi B C = gi A C := by
  have hD : IsOpen ((A ⊓ B ⊓ C : AddSubgroup V) : Set V) := by
    simp only [AddSubgroup.coe_inf]
    exact (hA.op.inter hB.op).inter hC.op
  rw [gi_of_le (D := A ⊓ B ⊓ C) (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
      (relIndex_ne_zero hD hA.cp) (relIndex_ne_zero hD hB.cp),
    gi_of_le (D := A ⊓ B ⊓ C) (inf_le_left.trans inf_le_right) inf_le_right
      (relIndex_ne_zero hD hB.cp) (relIndex_ne_zero hD hC.cp),
    gi_of_le (D := A ⊓ B ⊓ C) (inf_le_left.trans inf_le_left) inf_le_right
      (relIndex_ne_zero hD hA.cp) (relIndex_ne_zero hD hC.cp)]
  have hb : ((A ⊓ B ⊓ C).relIndex B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (relIndex_ne_zero hD hB.cp)
  rw [div_mul_div_comm, mul_comm ((A ⊓ B ⊓ C).relIndex B : ℝ), mul_div_mul_right _ _ hb]
end Formalism.FourierDecayAlt.P.A5x5
