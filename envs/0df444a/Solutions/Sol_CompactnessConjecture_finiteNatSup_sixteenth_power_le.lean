-- Prove2me | solution 1 for CompactnessConjecture.finiteNatSup_sixteenth_power_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/d857a528-6993-44af-990a-6d1bd7914740

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {α : Type*} (s : Finset α) (weight : α → ℕ) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hweight : ∀ a ∈ s, (weight a : ℝ) ^ 16 ≤ bound) :
    ((s.sup weight : ℕ) : ℝ) ^ 16 ≤ bound := by
  classical
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst s
    simpa using hbound
  · obtain ⟨a, ha, hmax⟩ := Finset.exists_mem_eq_sup s hs weight
    simpa [hmax] using hweight a ha
end CompactnessConjecture
