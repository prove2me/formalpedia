-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.mul_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:01.402369+00:00
-- url     : https://prove2.me/submissions/d5ffea2a-fa03-43d1-84a3-c9ebdb4caf71

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
open Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K]
namespace Formalism.DoubleCosetMeasures.P.Phase
theorem _root_.solution (s : List ℕ) (f : Fin s.sum → K) (M : Matrix (Fin s.sum) (Fin s.sum) K)
    (a c : Fin s.sum) : (M * mono s f) a c = M a (revF s c) * f (revF s c) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (revF s c)]
  · simp [mono]
  · intro b _ hb
    simp only [mono]
    rw [if_neg (fun h => hb (by rw [h, revF_revF])), mul_zero]
  · simp
end Formalism.DoubleCosetMeasures.P.Phase
