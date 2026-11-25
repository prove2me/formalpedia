-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.keyL_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:49:10.112256+00:00
-- url     : https://prove2.me/submissions/53dd626d-f2d5-43b3-a49e-260299b66d07

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution : Function.Injective (keyL (T := T) (r := r) (n := n)) := by
  rintro ⟨σ, i, c⟩ ⟨σ', i', c'⟩ h
  simp only [keyL, Prod.mk.injEq] at h
  obtain ⟨rfl, hi, rfl⟩ := h
  obtain rfl : i = i' := Fin.ext hi
  rfl
end Formalism.L2.FormalSeriesBounds.RF
