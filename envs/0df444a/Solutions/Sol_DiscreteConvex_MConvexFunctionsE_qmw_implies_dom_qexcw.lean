-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsE.qmw_implies_dom_qexcw
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:20:20.249111+00:00
-- url     : https://prove2.me/submissions/4a318e2a-a91a-4740-9737-69a053be085b

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QMw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QEXCw

set_option autoImplicit false

theorem f33d5922_aux {V : Type*} (f : (V → ℤ) → WithTop ℝ) (z w : V → ℤ)
    (hz : f z ≠ ⊤) (h : f w - f z ≤ 0) : f w ≠ ⊤ := by
  intro hw
  lift f z to ℝ using hz with a ha
  rw [hw] at h
  simp at h

open Classical in
open scoped Pointwise in
open DiscreteConvex.MConvexFunctionsE in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : QMw f) : QEXCw (DomZ f) := by
  intro x hx y hy hxy
  obtain ⟨u, hu, v, hv, h⟩ := hf x hx y hy hxy
  refine ⟨u, hu, v, hv, ?_⟩
  rcases h with h | h
  · left
    have hw := f33d5922_aux f x _ hx h
    have e : (fun w => x w - CharVec u w + CharVec v w) =
        (fun w => x w + CharVec v w - CharVec u w) := by
      funext w; ring
    show f _ ≠ ⊤
    rw [e]; exact hw
  · right
    exact f33d5922_aux f y _ hy h

