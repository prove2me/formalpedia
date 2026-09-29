-- Prove2me | solution 1 for DiazModulus.diaz_iff_no_candidate
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T16:09:06.513635+00:00
-- url     : https://prove2.me/submissions/dc7491db-f291-4c46-9345-aae391fdeeb3

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

open DiazModulus in
theorem solution : DiazModulusConjecture ↔ ¬ ∃ u : ℂ, IsCandidate u := by
  constructor
  · rintro h ⟨u, hu0, hmod, hexp⟩
    exact h u hu0 hmod hexp
  · intro h u hu0 hmod hexp
    exact h ⟨u, hu0, hmod, hexp⟩
