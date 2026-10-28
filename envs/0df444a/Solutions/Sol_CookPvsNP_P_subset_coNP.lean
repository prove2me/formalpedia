-- Prove2me | solution 1 for CookPvsNP.P_subset_coNP
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T04:55:49.432122+00:00
-- url     : https://prove2.me/submissions/5e140132-5d17-4b93-bb7e-84053c6f4825

import Definitions.Def_CookPvsNP_defs
import Theorems.Thm_CookPvsNP_coP_eq_P
import Theorems.Thm_CookPvsNP_P_subset_NP

open CookPvsNP

theorem solution (Sym : Type) [Fintype Sym] : P Sym ⊆ coNP Sym := by
  intro L hL
  rw [← coP_eq_P Sym] at hL
  exact P_subset_NP Sym hL
