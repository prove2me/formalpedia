-- Prove2me | solution 1 for FairSelling.RelaxEx.o_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:16:47.922549+00:00
-- url     : https://prove2.me/submissions/b7ab7a58-dd0b-4c7c-952c-3b9888f34d9b

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_EnvyRelaxation

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.RelaxEx
namespace FairSelling.RelaxEx
theorem _root_.solution : o.Full p Finset.univ := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, Finset.subset_univ _, ?_, ?_⟩
  · intro j; fin_cases j <;> simp [o]
  · intro j k hjk; fin_cases j <;> fin_cases k <;> simp_all [o]
  · intro j; fin_cases j <;> norm_num [o]
  · simp [o, Fin.sum_univ_two, p]
  · show ({1} : Finset (Fin 2)) ∪ Finset.univ.biUnion o.kept = Finset.univ
    ext x
    fin_cases x <;> simp [o, Finset.mem_biUnion, Fin.exists_fin_two]
  · simp [o, Fin.sum_univ_two, p]
end FairSelling.RelaxEx
