-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.S4.parity_of_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:57:09.100791+00:00
-- url     : https://prove2.me/submissions/fc0864b3-be51-464e-9d97-caf88a96296a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4
namespace Formalism.L2.FormalSeriesBounds.S4
theorem _root_.solution {d : ℕ} (big : ZMod d → Prop) (halt : ∀ b, big (b + 1) ↔ ¬ big b)
    (a : ZMod d) (ha : big a) : ∀ k : ℕ, big (a + (k : ZMod d)) ↔ Even k := by
  intro k
  induction k with
  | zero => simp [ha]
  | succ k ih => rw [Nat.cast_succ, ← add_assoc, halt, ih, Nat.even_add_one]
end Formalism.L2.FormalSeriesBounds.S4
