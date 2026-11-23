-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.exists_mu_generator_pow_sub_one_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:51.061033+00:00
-- url     : https://prove2.me/submissions/42f3228b-0eaa-40df-bc91-f8ffbe8fc12c

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (hm : MuFacts) : ∃ d ∈ mu l, ∀ j, 0 < j → j < l - 1 → IsUnit (d ^ j - 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have ho : orderOf g = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  obtain ⟨d, ⟨hd, hdx⟩, -⟩ := (hm l).2.1 (g : ZMod l) g.ne_zero
  refine ⟨d, hd, fun j h0 hj => ?_⟩
  rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
    map_one, hdx, sub_eq_zero]
  intro h
  have h' : g ^ j = 1 := Units.ext (by simpa using h)
  exact pow_ne_one_of_lt_orderOf h0.ne' (ho ▸ hj) h'
end Formalism.CohomologicalDescent.HeightDescentMinors
