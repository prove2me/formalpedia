-- Prove2me | solution 1 for CCS.resid_par
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:55:26.326875+00:00
-- url     : https://prove2.me/submissions/cf593aa2-d1a3-4fdd-9784-4b9016199d32

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation

set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}
namespace CCS
theorem _root_.solution {P Q : Process Name} (c : Set (semantics (.par P Q)).Event) :
    resid (.par P Q) c = .par (resid P (projL c)) (resid Q (projR c)) := by
  rw [resid]
end CCS
