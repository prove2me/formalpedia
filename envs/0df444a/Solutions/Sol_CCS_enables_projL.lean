-- Prove2me | solution 1 for CCS.enables_projL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:10:11.072429+00:00
-- url     : https://prove2.me/submissions/d8c933dd-ecdb-4f51-95c3-fb3924c41775

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Theorems.Thm_CCS_projL_isConf
import Theorems.Thm_CCS_projL_insert

set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}
variable {c : Set (Tag E F)}
namespace CCS
theorem _root_.solution {t : Tag E F} {x : E.Event}
    (hins : (parSES E F).toGES.isConf (c ∪ {t}))
    (hfr : t ∉ c) (hx : t.evL = some x) :
    E.toGES.isConf (projL c ∪ {x}) ∧ x ∉ projL c := by
  refine ⟨(projL_insert hx) ▸ projL_isConf hins, ?_⟩
  rintro ⟨u, hu, hev⟩
  refine hfr ?_
  classical
  have hpair : ParCon ({u, t} : Finset (Tag E F)) := by
    refine hins.1 {u, t} fun v hv => ?_
    rcases Finset.mem_insert.mp (by exact_mod_cast hv) with rfl | hv'
    · exact Or.inl hu
    · exact (Finset.mem_singleton.mp hv') ▸ Or.inr rfl
  have : u = t :=
    (hpair.1 u (Finset.mem_insert_self _ _) t
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).1 x hev hx
  exact this ▸ hu
end CCS
