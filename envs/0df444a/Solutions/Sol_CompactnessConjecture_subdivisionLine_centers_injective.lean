-- Prove2me | solution 1 for CompactnessConjecture.subdivisionLine_centers_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/92b3ab57-f4e9-4399-8082-c26625a81082

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

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
    (C : Fin k → SymplecticLine K)
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inr (C center)) :
    Function.Injective C := by
  intro i j hij
  apply Sum.inr.inj
  apply Sum.inl.inj
  apply copy.injective
  change copy (.inl (.inr i)) = copy (.inl (.inr j))
  rw [hcenter i, hcenter j, hij]
end CompactnessConjecture
