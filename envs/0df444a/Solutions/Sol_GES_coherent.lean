-- Prove2me | solution 1 for GES.coherent
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T21:11:21.969715+00:00
-- url     : https://prove2.me/submissions/9b521ffc-1693-4fc0-a321-d3872dd5bd3e

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_General_Stable
import Mathlib.Data.Set.Lattice
import Definitions.Def_EventStructures_Stable_Basic
set_option autoImplicit true
open ConfFamily
variable {L : Type*}

theorem GES.coherent (G : GES L) : Coherent G.toFamily := by
  intro S z hS hz hSz
  change G.isConf z at hz
  change G.isConf (⋃₀ S)
  refine ⟨fun X hX => hz.1 X (hX.trans (Set.sUnion_subset hSz)), fun e he => ?_⟩
  obtain ⟨x, hx, h⟩ := he
  have hxc : G.isConf x := hS x hx
  obtain ⟨n, hn⟩ := hxc.2 e h
  exact ⟨n, GES.secApprox_mono_set (Set.subset_sUnion_of_mem hx) n hn⟩

theorem solution (G : GES L) : Coherent G.toFamily := GES.coherent G
