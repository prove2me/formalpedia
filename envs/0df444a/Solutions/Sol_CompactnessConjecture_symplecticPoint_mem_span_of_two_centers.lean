-- Prove2me | solution 1 for CompactnessConjecture.symplecticPoint_mem_span_of_two_centers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/a50d61fb-d418-4e3a-bab1-bc870f2c8ebd

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_standardSymplecticBilin_isAlt
import Theorems.Thm_CompactnessConjecture_symplecticPoint_centers_span_orthogonal

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {x y z c d : SymplecticPoint K}
    (hyz : y ≠ z) (hcd : c ≠ d)
    (hcx : c.1 ≤ SymplecticPointOrthogonal K x)
    (hcy : c.1 ≤ SymplecticPointOrthogonal K y)
    (hcz : c.1 ≤ SymplecticPointOrthogonal K z)
    (hdx : d.1 ≤ SymplecticPointOrthogonal K x)
    (hdy : d.1 ≤ SymplecticPointOrthogonal K y)
    (hdz : d.1 ≤ SymplecticPointOrthogonal K z) :
    x.1 ≤ y.1 ⊔ z.1 := by
  have hcenters := symplecticPoint_centers_span_orthogonal K
    hyz hcd hcy hcz hdy hdz
  have hxorth :
      x.1 ≤ (standardSymplecticBilin K).orthogonal (c.1 ⊔ d.1) := by
    intro w hw
    change ∀ u ∈ c.1 ⊔ d.1,
      standardSymplecticForm K u w = 0
    intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    rw [standardSymplecticForm_add_left]
    have haorth : standardSymplecticForm K a w = 0 := by
      have h := hcx ha w hw
      change standardSymplecticForm K w a = 0 at h
      rw [standardSymplecticForm_swap, h, neg_zero]
    have hborth : standardSymplecticForm K b w = 0 := by
      have h := hdx hb w hw
      change standardSymplecticForm K w b = 0 at h
      rw [standardSymplecticForm_swap, h, neg_zero]
    rw [haorth, hborth, add_zero]
  rw [hcenters,
    LinearMap.BilinForm.orthogonal_orthogonal
      (standardSymplecticBilin_nondegenerate K)
      (standardSymplecticBilin_isAlt K).isRefl] at hxorth
  exact hxorth
end CompactnessConjecture
