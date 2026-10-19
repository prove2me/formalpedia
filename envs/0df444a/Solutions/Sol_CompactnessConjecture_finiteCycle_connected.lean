-- Prove2me | solution 1 for CompactnessConjecture.finiteCycle_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/427b16a2-1121-40cc-a1e1-1967f11765f5

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution {n : ℕ} (hn : 0 < n) :
    (finiteCycle n).graph.Connected := by
  change (SimpleGraph.cycleGraph n).Connected
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ⟨SimpleGraph.cycleGraph_preconnected⟩
end CompactnessConjecture
