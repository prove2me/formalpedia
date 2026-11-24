-- Prove2me | solution 1 for FairSelling.RelaxEx.o_not_SEF1lit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:16:55.026174+00:00
-- url     : https://prove2.me/submissions/0e8f1dcd-5290-46dc-a93c-1e390e1dd32d

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
theorem _root_.solution : ¬ SEF1lit v p o := by
  intro h
  obtain ⟨g, hg, hx⟩ := (h 0 1).2 (by norm_num [o])
  have hg0 : g = 0 := by
    have : g ∈ ({0} : Finset (Fin 2)) := hg
    simpa using this
  subst hg0
  have h1 : o.kept 0 = ∅ := by simp [o]
  have h2 : ({0} : Finset (Fin 2)) \ {0} = ∅ := by decide
  rw [h1, vbarSum_empty] at hx
  have h3 : o.kept 1 = ({0} : Finset (Fin 2)) := by simp [o]
  rw [h3, h2, vbarSum_empty] at hx
  norm_num [p] at hx
end FairSelling.RelaxEx
