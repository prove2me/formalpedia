-- Prove2me | solution 1 for CompactnessConjecture.subdivisionLine_base_of_line_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/f6f9eadd-e056-481c-9b22-d912aa9938a0

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_subdivisionLine_center_of_line_base
import Theorems.Thm_CompactnessConjecture_subdivisionLine_base_of_line_center

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base otherBase : Fin 3} (center : Fin k)
    {L : SymplecticLine K}
    (hbase : copy (.inl (.inl base)) = .inr L) :
    ∃ M : SymplecticLine K,
      copy (.inl (.inl otherBase)) = .inr M := by
  obtain ⟨C, hC⟩ := subdivisionLine_center_of_line_base K
    copy (center := center) hbase
  exact subdivisionLine_base_of_line_center K
    copy (base := otherBase) hC
end CompactnessConjecture
