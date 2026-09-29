-- Prove2me | solution 1 for Erdos180.symplecticPointRelated_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:40:27.989199+00:00
-- url     : https://prove2.me/submissions/76272ea5-5a3b-4a38-9593-daad6e91fcd8

import Definitions.Def_erdos180_core4
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    {p q : SymplecticPoint K}
    (h : SymplecticPointRelated K p q) :
    SymplecticPointRelated K q p := by
  obtain ⟨hpq, L, hpL, hqL⟩ := h
  exact ⟨Ne.symm hpq, L, hqL, hpL⟩
