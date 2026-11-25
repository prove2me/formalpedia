-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.closure_le_FG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:57:32.963933+00:00
-- url     : https://prove2.me/submissions/58234d3b-76dc-47fe-b8df-18bbd0ca4e7f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_InvSubOneBd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {n : ℕ} {K : Type*} [Field K]
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
theorem _root_.solution :
    Subgroup.closure {a : Matrix.GeneralLinearGroup (Fin n) K |
      ∀ i j, (i < j → (a : Matrix (Fin n) (Fin n) K) i j = 0) ∧
        (i = j → (a : Matrix (Fin n) (Fin n) K) i j = 1)} ≤ FG n K 0 := by
  rw [Subgroup.closure_le]
  intro a ha i j hij
  rw [Matrix.sub_apply]
  have hle : (i : ℕ) ≤ j := by omega
  rcases Nat.lt_or_eq_of_le hle with h | h
  · have hij' : i < j := Fin.lt_def.mpr h
    rw [(ha i j).1 hij', Matrix.one_apply_ne (ne_of_lt hij'), sub_zero]
  · have e : i = j := Fin.ext h
    subst e
    rw [(ha i i).2 rfl, Matrix.one_apply_eq, sub_self]
end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
