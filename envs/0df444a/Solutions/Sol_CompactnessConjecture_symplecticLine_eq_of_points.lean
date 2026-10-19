-- Prove2me | solution 1 for CompactnessConjecture.symplecticLine_eq_of_points
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/3b711915-aa24-4ac4-8718-7b8458ac46c5

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticPoint_sup_finrank

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {p q : SymplecticPoint K} (hpq : p ≠ q)
    {L M : SymplecticLine K}
    (hpL : p.1 ≤ L.1) (hqL : q.1 ≤ L.1)
    (hpM : p.1 ≤ M.1) (hqM : q.1 ≤ M.1) : L = M := by
  have hsupL : p.1 ⊔ q.1 ≤ L.1 := sup_le hpL hqL
  have hsupM : p.1 ⊔ q.1 ≤ M.1 := sup_le hpM hqM
  have hL : p.1 ⊔ q.1 = L.1 :=
    Submodule.eq_of_le_of_finrank_eq hsupL
      ((symplecticPoint_sup_finrank K hpq).trans L.2.1.symm)
  have hM : p.1 ⊔ q.1 = M.1 :=
    Submodule.eq_of_le_of_finrank_eq hsupM
      ((symplecticPoint_sup_finrank K hpq).trans M.2.1.symm)
  exact Subtype.ext (hL.symm.trans hM)
end CompactnessConjecture
