-- Prove2me | solution 1 for DRConvexOpt.InfConv.subset_outer
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T12:08:20.004967+00:00
-- url     : https://prove2.me/submissions/df624ca4-3054-4573-a0a5-8d423dadf112

import Mathlib
import Definitions.Def_DRConvexOpt_InfConv_Setting

open DRConvexOpt.InfConv
open MeasureTheory Matrix Filter Topology

theorem solution {nP nQ nK nI nJ : ℕ} (d : AmbData nP nQ nK nI)
    (blk : Fin (nI + 1) → Fin nJ) (j : Fin nJ) :
    ambiguitySet d ⊆ outerSet d blk j := by
  rintro μ ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, fun i _ => h4 i⟩
