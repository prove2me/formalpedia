-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.bdiag_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:52.371002+00:00
-- url     : https://prove2.me/submissions/05f0a083-f7e8-4c97-8611-037bb1788b9e

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_low_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxHeartbeats 400000
noncomputable section
open Matrix
namespace Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
namespace Phase
variable {K : Type} [CommRing K]
private lemma bdiag_apply (s : List ℕ) (x : Matrix (Fin s.sum) (Fin s.sum) K)
    (a c : Fin s.sum) : bdiag s x a c = if blk s a = blk s c then x a c else 0 := rfl
end Phase
end Formalism.DoubleCosetMeasures.P
end
end

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
open Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K]
namespace Formalism.DoubleCosetMeasures.P.Phase
theorem _root_.solution (s : List ℕ) {x : Matrix (Fin s.sum) (Fin s.sum) K} (hx : IsLowUni x) :
    IsLowUni (bdiag s x) := by
  unfold IsLowUni
  constructor
  · intro i j h
    have h' : i < j := h
    rw [bdiag_apply]
    split_ifs
    · exact low_zero hx h'
    · rfl
  · intro a
    rw [bdiag_apply, if_pos rfl, hx.2 a]
end Formalism.DoubleCosetMeasures.P.Phase
