-- Prove2me | solution 1 for CookPvsNP.P_eq_NP_of_npComplete_mem_P
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T04:55:50.121891+00:00
-- url     : https://prove2.me/submissions/46ffc001-1b3b-4bdc-bf4c-ee913b67c641

import Definitions.Def_CookPvsNP_defs
import Theorems.Thm_CookPvsNP_mem_P_of_polyReducible
import Theorems.Thm_CookPvsNP_P_subset_NP

open CookPvsNP

theorem solution {Sym : Type} [Fintype Sym] (L : Lang Sym)
    (hL : NPComplete L) (hP : L ∈ P Sym) :
    ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'], P Sym' = NP Sym' := by
  intro Sym' _ _
  apply Set.Subset.antisymm (P_subset_NP Sym')
  intro L' hL'
  exact mem_P_of_polyReducible L' L (hL.2 Sym' L' hL') hP
