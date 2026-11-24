-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.avg_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:30.969943+00:00
-- url     : https://prove2.me/submissions/e8d0adab-7042-4153-977d-4c91261652c2

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Finset
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W : Type*} [AddCommGroup W]
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution (k : ℕ) (H : AddSubgroup W) [Fintype (Qt k H)] (g : W → ℂ) :
    avg k H g = (Fintype.card (Qt k H) : ℂ)⁻¹ * ∑ q : Qt k H, g ((q.out : H) : W) := by
  rw [avg, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
end Formalism.IndefR.Fin.Four
