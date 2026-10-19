-- Prove2me | solution 1 for CompactnessConjecture.extremalScale_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/bbc20be0-0a53-40ad-b715-1166f468efa7

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Filter Finset SimpleGraph
open scoped Topology
namespace CompactnessConjecture
theorem _root_.solution {n : ℕ} (hn : 0 < n) :
    0 < extremalScale n := by
  unfold extremalScale
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
end CompactnessConjecture
