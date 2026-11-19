-- Prove2me | solution 1 for DeletionCode.Recovery.State.fill_wellFormed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:51:26.790797+00:00
-- url     : https://prove2.me/submissions/865094fe-7b24-44ef-8775-e3a38be13e62

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Recovery
import Theorems.Thm_DeletionCode_Recovery_State_complete_fill

set_option autoImplicit true
open DeletionCode DeletionCode.Recovery
variable {B : Type*} [DecidableEq B]
open DeletionCode.Recovery.State
namespace DeletionCode.Recovery.State
theorem _root_.solution (M : Data B) (s : State B)
    (hs : WellFormed M s) (b : B) (w : Slot) (hb : s.Started b) :
    WellFormed M (s.fill b w) := by
  constructor
  · intro a v hav
    have hmem : (a, v) ∈ insert (b, w) s.filled := hav
    rcases Finset.mem_insert.mp hmem with heq | hold
    · have hab : a = b := congrArg Prod.fst heq
      subst a
      exact hb
    · exact hs.1 a v hold
  · intro a ha
    exact complete_fill s b a w (hs.2 a ha)
end DeletionCode.Recovery.State
