-- Prove2me | solution 1 for FairSelling.RelaxEx.o_not_SEFXlit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:16:56.894866+00:00
-- url     : https://prove2.me/submissions/f8ed12be-4814-4034-83ec-7a7b16777752

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_EnvyRelaxation
import Theorems.Thm_FairSelling_RelaxEx_vbarSum_empty

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.RelaxEx
namespace FairSelling.RelaxEx
theorem _root_.solution : ¬ SEFXlit v p o := by
  intro h
  have hmem : (0 : Fin 2) ∈ o.kept 1 := by simp [o]
  have hx := (h 0 1).2 (by norm_num [o]) 0 hmem
  have h1 : o.kept 0 = ∅ := by simp [o]
  have h2 : ({0} : Finset (Fin 2)) \ {0} = ∅ := by decide
  have h3 : o.kept 1 = ({0} : Finset (Fin 2)) := by simp [o]
  rw [h1, vbarSum_empty, h3, h2, vbarSum_empty] at hx
  norm_num [p] at hx
end FairSelling.RelaxEx
