-- Prove2me | solution 1 for CompactnessConjecture.symplecticAutomorphism_incidence_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/dcbb8875-0a1a-4af1-8e9f-ff2e16c3018a

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (e : SymplecticAutomorphism K)
    (p : SymplecticPoint K) (L : SymplecticLine K) :
    (symplecticAutomorphismPoint K e p).1 ≤
        (symplecticAutomorphismLine K e L).1 ↔
      p.1 ≤ L.1 := by
  change
    p.1.map e.toLinearEquiv.toLinearMap ≤
      L.1.map e.toLinearEquiv.toLinearMap ↔ p.1 ≤ L.1
  exact LinearMap.map_le_map_iff'
    (LinearMap.ker_eq_bot.mpr e.toLinearEquiv.injective)
end CompactnessConjecture
