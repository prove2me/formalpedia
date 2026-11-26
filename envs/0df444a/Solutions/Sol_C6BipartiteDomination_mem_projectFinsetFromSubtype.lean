-- Prove2me | solution 1 for C6BipartiteDomination.mem_projectFinsetFromSubtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:23.775235+00:00
-- url     : https://prove2.me/submissions/ae420483-0f07-48f3-89c9-7bec8115a56e

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {S : Finset V}
    (F : Finset {v // v ∈ S}) (v : V) :
    v ∈ projectFinsetFromSubtype (S := S) F ↔
      ∃ x ∈ F, x.1 = v := by
  classical
  simp only [projectFinsetFromSubtype, Finset.mem_image]
end C6BipartiteDomination
