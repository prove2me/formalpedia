-- Prove2me | solution 1 for CSeparatedNPComplete.convexOnPredicate_iff_convexOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:50:49.871054+00:00
-- url     : https://prove2.me/submissions/5872b30b-c686-40a6-a900-4a40be8c4c59

module
public import Definitions.Def_CSeparatedNPComplete_Definitions
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Tactic.Linarith
public import Definitions.Def_CSeparatedNPComplete_ConvexPredicate

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution (P : Real → Prop) (f : Real → Real) :
    convexOnPredicate P f ↔ ConvexOn ℝ {x | P x} f := by
  constructor
  · intro h
    constructor
    · intro x hx y hy a b ha hb hab
      have hb' : b = 1 - a := by linarith
      simpa only [hb', smul_eq_mul, Set.mem_setOf_eq] using
        (h x y hx hy a ha (by linarith)).1
    · intro x hx y hy a b ha hb hab
      have hb' : b = 1 - a := by linarith
      simpa only [hb', smul_eq_mul] using (h x y hx hy a ha (by linarith)).2
  · intro h x y hx hy t ht ht'
    exact ⟨h.1 hx hy ht (sub_nonneg.mpr ht') (by ring),
      h.2 hx hy ht (sub_nonneg.mpr ht') (by ring)⟩
end CSeparatedNPComplete
