-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x7.cos_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:43.563373+00:00
-- url     : https://prove2.me/submissions/4f2a54f0-33a4-44d6-a27a-60607d5b0ddd

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x7
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x7
theorem _root_.solution (w : Point K) (q : Cos R w) : q = cos1 R w ↔
    (rep R q).1 ∈ intSub R (lowW K w.1 w.2) ∧ (rep R q).2 ∈ intSub R (upUniG K w.1.sum) := by
  obtain ⟨q1, q2⟩ := q
  simp only [cos1, rep, Prod.mk.injEq]
  apply and_congr
  · constructor
    · intro hq
      have h := QuotientGroup.rightRel_apply.mp (Quotient.exact ((Quotient.out_eq q1).trans hq))
      simpa using h
    · intro hq
      rw [← Quotient.out_eq q1]
      apply Quotient.sound
      exact QuotientGroup.rightRel_apply.mpr (by simpa using hq)
  · constructor
    · intro hq
      have h := QuotientGroup.eq.1 ((Quotient.out_eq q2).trans hq)
      simpa using h
    · intro hq
      rw [← Quotient.out_eq q2]
      exact QuotientGroup.eq.2 (by simpa using hq)
end Formalism.FourierDecayAlt.P.A5x7
