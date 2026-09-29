-- Prove2me | solution 1 for BrinSquier.commute_of_disjoint_supp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-12T22:06:46.805192+00:00
-- url     : https://prove2.me/submissions/ad6992c9-52ed-4a1f-b7e0-6d7895a89fb3

import Definitions.Def_BrinSquier
import Mathlib

namespace BS_aux

/-- A support is invariant: if `f` moves `x`, it moves `f x`. -/
lemma mem_supp_apply {f : ℝ ≃o ℝ} {x : ℝ} (hx : x ∈ BrinSquier.supp f) :
    f x ∈ BrinSquier.supp f := fun h => hx (f.injective h)

end BS_aux

open BS_aux in
theorem solution {f g : ℝ ≃o ℝ} (h : Disjoint (BrinSquier.supp f) (BrinSquier.supp g)) :
    f * g = g * f := by
  apply RelIso.ext
  intro x
  show f (g x) = g (f x)
  by_cases hf : x ∈ BrinSquier.supp f
  · have hgx : g x = x := not_not.1 (Set.disjoint_left.mp h hf)
    have hgfx : g (f x) = f x := not_not.1 (Set.disjoint_left.mp h (mem_supp_apply hf))
    rw [hgx, hgfx]
  · have hfx : f x = x := not_not.1 hf
    by_cases hg : x ∈ BrinSquier.supp g
    · have hfgx : f (g x) = g x := not_not.1 (Set.disjoint_right.mp h (mem_supp_apply hg))
      rw [hfx, hfgx]
    · have hgx : g x = x := not_not.1 hg
      rw [hfx, hgx, hfx]
