-- Prove2me | solution 1 for Formalism.FG.WittVectorsCharZero.neZero_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:30.958999+00:00
-- url     : https://prove2.me/submissions/9e14bbdc-7939-48af-92e6-2bf07d994431

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.WittVectorsCharZero
namespace Formalism.FG.WittVectorsCharZero
theorem _root_.solution (l : ℕ) [Fact l.Prime] (d : ℕ) (hd : 1 ≤ d) :
    NeZero (((l ^ d - 1 : ℕ) : ZMod l)) := by
  constructor
  have hl : 1 ≤ l ^ d := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  rw [Nat.cast_sub hl, Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega), Nat.cast_one, zero_sub]
  exact neg_ne_zero.mpr one_ne_zero
end Formalism.FG.WittVectorsCharZero
