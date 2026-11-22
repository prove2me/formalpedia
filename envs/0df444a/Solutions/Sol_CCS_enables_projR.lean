-- Prove2me | solution 1 for CCS.enables_projR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:10:26.813741+00:00
-- url     : https://prove2.me/submissions/e493e0ed-d843-4a96-9f17-4eccd7baab4a

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Theorems.Thm_CCS_projR_isConf
import Theorems.Thm_CCS_projR_insert

set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}
variable {c : Set (Tag E F)}
namespace CCS
theorem _root_.solution {t : Tag E F} {y : F.Event}
    (hins : (parSES E F).toGES.isConf (c ∪ {t}))
    (hfr : t ∉ c) (hy : t.evR = some y) :
    F.toGES.isConf (projR c ∪ {y}) ∧ y ∉ projR c := by
  refine ⟨(projR_insert hy) ▸ projR_isConf hins, ?_⟩
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
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).2 y hev hy
  exact this ▸ hu
end CCS
