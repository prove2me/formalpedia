-- Prove2me | solution 1 for C6BipartiteDomination.main_upper_bound_gamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:16:38.487737+00:00
-- url     : https://prove2.me/submissions/5861d512-6881-48f2-882a-06eed94a53f7

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
import Theorems.Thm_C6BipartiteDomination_gammaBip_minimum_exists
import Theorems.Thm_C6BipartiteDomination_main_upper_bound_minimum


set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace C6BipartiteDomination
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hNoIso : HasNoIsolatedVertices G)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    15 * gammaBip G ≤ 8 * Fintype.card V := by
  obtain ⟨D, hmin, hcard⟩ := gammaBip_minimum_exists G
  have h := main_upper_bound_minimum G hNoIso hmax D hmin
  simpa [hcard] using h
end C6BipartiteDomination
