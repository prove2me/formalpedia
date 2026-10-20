-- Prove2me | solution 1 for DerivativeChainPrivate.nonreal_roots_of_real_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T01:48:46.70629+00:00
-- url     : https://prove2.me/submissions/76e5b980-b4a4-48f5-85fb-bb5d203adb31

import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false

theorem solution (p : Polynomial ℝ) :
    ((p.map Complex.ofRealHom).roots.filter (fun z => z.im ≠ 0)).card =
      p.natDegree - p.roots.card := by
  classical
  have hrange (z : ℂ) : z ∈ Complex.ofRealHom.range ↔ z.im = 0 := by
    change (∃ r : ℝ, (r : ℂ) = z) ↔ z.im = 0
    constructor
    · rintro ⟨r, rfl⟩
      simp
    · intro hz
      refine ⟨z.re, ?_⟩
      apply Complex.ext <;> simp [hz]
  have hfilter : (p.map Complex.ofRealHom).roots.filter (fun z => z.im = 0) =
      p.roots.map Complex.ofRealHom := by
    simpa only [hrange] using
      Polynomial.filter_roots_map_range_eq_map_roots
        (f := Complex.ofRealHom) Complex.ofReal_injective p
  have hcard : (p.map Complex.ofRealHom).roots.card = p.natDegree := by
    rw [← (IsAlgClosed.splits (p.map Complex.ofRealHom)).natDegree_eq_card_roots,
      Polynomial.natDegree_map]
  have hparts := congrArg Multiset.card
    ((p.map Complex.ofRealHom).roots.filter_add_not (p := fun z => z.im = 0))
  rw [Multiset.card_add, hfilter, Multiset.card_map, hcard] at hparts
  change p.roots.card +
    ((p.map Complex.ofRealHom).roots.filter (fun z => z.im ≠ 0)).card =
      p.natDegree at hparts
  omega
