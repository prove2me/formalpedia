-- Prove2me | solution 1 for CompactnessConjecture.symplecticPoint_centers_span_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/1ff8e279-46a3-48b9-a11d-e13a81ee0c05

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticPoint_sup_finrank
import Theorems.Thm_CompactnessConjecture_symplecticPointSpan_orthogonal_finrank

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {y z c d : SymplecticPoint K}
    (hyz : y ≠ z) (hcd : c ≠ d)
    (hcy : c.1 ≤ SymplecticPointOrthogonal K y)
    (hcz : c.1 ≤ SymplecticPointOrthogonal K z)
    (hdy : d.1 ≤ SymplecticPointOrthogonal K y)
    (hdz : d.1 ≤ SymplecticPointOrthogonal K z) :
    c.1 ⊔ d.1 =
      (standardSymplecticBilin K).orthogonal (y.1 ⊔ z.1) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply sup_le
    · intro w hw
      change ∀ u ∈ y.1 ⊔ z.1,
        standardSymplecticForm K u w = 0
      intro u hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      have haorth : standardSymplecticForm K a w = 0 := by
        have h := hcy hw a ha
        change standardSymplecticForm K a w = 0 at h
        exact h
      have hborth : standardSymplecticForm K b w = 0 := by
        have h := hcz hw b hb
        change standardSymplecticForm K b w = 0 at h
        exact h
      rw [standardSymplecticForm_add_left, haorth, hborth, add_zero]
    · intro w hw
      change ∀ u ∈ y.1 ⊔ z.1,
        standardSymplecticForm K u w = 0
      intro u hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      have haorth : standardSymplecticForm K a w = 0 := by
        have h := hdy hw a ha
        change standardSymplecticForm K a w = 0 at h
        exact h
      have hborth : standardSymplecticForm K b w = 0 := by
        have h := hdz hw b hb
        change standardSymplecticForm K b w = 0 at h
        exact h
      rw [standardSymplecticForm_add_left, haorth, hborth, add_zero]
  · rw [symplecticPoint_sup_finrank K hcd,
      symplecticPointSpan_orthogonal_finrank K hyz]
end CompactnessConjecture
