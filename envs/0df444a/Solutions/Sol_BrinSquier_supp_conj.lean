-- Prove2me | solution 1 for BrinSquier.supp_conj
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-12T22:04:06.800603+00:00
-- url     : https://prove2.me/submissions/b54a1afe-bcd6-4131-9cb2-67f0ca39e65c

import Definitions.Def_BrinSquier
import Mathlib

namespace BS_aux

/-- A support is invariant: if `f` moves `x`, it moves `f x`. -/
lemma mem_supp_apply {f : ℝ ≃o ℝ} {x : ℝ} (hx : x ∈ BrinSquier.supp f) :
    f x ∈ BrinSquier.supp f := fun h => hx (f.injective h)

end BS_aux

theorem solution (f g : ℝ ≃o ℝ) :
    BrinSquier.supp (f * g * f⁻¹) = f '' BrinSquier.supp g := by
  ext x
  constructor
  · intro hx
    refine ⟨f⁻¹ x, ?_, RelIso.apply_inv_self f x⟩
    intro h
    apply hx
    show f (g (f⁻¹ x)) = x
    rw [h, RelIso.apply_inv_self]
  · rintro ⟨y, hy, rfl⟩
    show f (g (f⁻¹ (f y))) ≠ f y
    rw [RelIso.inv_apply_self]
    exact fun h => hy (f.injective h)
