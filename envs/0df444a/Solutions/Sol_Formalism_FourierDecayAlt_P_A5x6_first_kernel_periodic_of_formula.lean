-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x6.first_kernel_periodic_of_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:32.395963+00:00
-- url     : https://prove2.me/submissions/569cad49-ecb6-46b3-beb0-4683f47322bd

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
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
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6
namespace Formalism.FourierDecayAlt.P.A5x6
theorem _root_.solution (hF : SingleBlockFormula) : SingleBlockPeriodic := by
  unfold SingleBlockPeriodic
  unfold SingleBlockFormula at hF
  intro K _ _ _ R ψ hLD h h' c c' hs hc
  rw [hF K R ψ hLD h h' c hs, hF K R ψ hLD h h' c' hs]
  have e : (Submodule.Quotient.mk (c : K) : KR R) = Submodule.Quotient.mk (c' : K) := by
    rw [Submodule.Quotient.eq, mem_rangeR]
    exact hc
  have e2 : ∀ {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K) (Z' : Matrix (Fin n') (Fin n') K),
      singleBlockInner R ψ Z Z' (c : K) = singleBlockInner R ψ Z Z' (c' : K) := by
    intro n n' Z Z'
    unfold singleBlockInner
    rw [e]
  simp only [e2]
end Formalism.FourierDecayAlt.P.A5x6
