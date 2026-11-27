-- Prove2me | solution 1 for C6BipartiteDomination.main_upper_bound_minimum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:15:30.637811+00:00
-- url     : https://prove2.me/submissions/13dfb5fd-f1a9-4dee-bfc6-a580f18f1f09

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
import Theorems.Thm_C6BipartiteDomination_main_bound_strong_induction

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hNoIso : HasNoIsolatedVertices G)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (D : Finset V) (hmin : MinimumBipartiteDominatingSet G D) :
    15 * D.card ≤ 8 * Fintype.card V := by
  exact main_bound_strong_induction (Fintype.card V) G rfl hNoIso hmax D hmin
end C6BipartiteDomination
