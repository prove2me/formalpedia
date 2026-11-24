-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.mem_GG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:03:33.050842+00:00
-- url     : https://prove2.me/submissions/92de201e-e0f6-4c0d-86ca-0b19732b3929

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NegOneNeOneUnitsZmodFour

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {s m : ℕ} (h : s ≤ m) (x : GalL (m + 2)) :
    x ∈ GG h ↔ resMap h x ∈ Subgroup.zpowers ((-1, 1, 1) : GalL (s + 2)) := by
  unfold GG
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
end Formalism.TwoAdicCyclotomicDecomposition
