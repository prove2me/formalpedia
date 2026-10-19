-- Prove2me | solution 1 for CompactnessConjecture.symplecticPointRelated_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/22cf36fd-286e-4d28-b957-18975b204517

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {p q : SymplecticPoint K}
    (h : SymplecticPointRelated K p q) :
    SymplecticPointRelated K q p := by
  obtain ⟨hpq, L, hpL, hqL⟩ := h
  exact ⟨Ne.symm hpq, L, hqL, hpL⟩
end CompactnessConjecture
