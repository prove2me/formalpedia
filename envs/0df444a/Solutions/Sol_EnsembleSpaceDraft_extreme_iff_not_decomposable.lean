-- Prove2me | solution 1 for EnsembleSpaceDraft.extreme_iff_not_decomposable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:31:27.873733+00:00
-- url     : https://prove2.me/submissions/2123cded-2e1c-44ea-a39a-c6d6dfc60468

import Definitions.Def_EnsembleSpaceDraft_axioms
import Mathlib

open scoped unitInterval

open EnsembleSpaceDraft

universe u

theorem solution {E : Type u} [TopologicalSpace E] (X : EnsembleSpace E)
    (e : E) :
    X.IsExtreme e ↔ ¬ X.IsDecomposable e := by
  constructor
  · rintro hext ⟨p, a, b, hp0, hp1, hab, he⟩
    have ha : a = e := hext p a b hp0 he
    have he' : e = X.mix (unitInterval.symm p) b a := by rw [he, X.mix_comm]
    have hb : b = e := hext (unitInterval.symm p) b a
      (by rw [unitInterval.coe_symm_eq]; linarith) he'
    exact hab (ha.trans hb.symm)
  · intro hnd p a b hp0 he
    by_cases hp1 : (p : ℝ) < 1
    · by_cases hab : a = b
      · subst hab; rw [X.mix_self] at he; exact he.symm
      · exact absurd ⟨p, a, b, hp0, hp1, hab, he⟩ hnd
    · have : p = 1 := Subtype.ext (le_antisymm p.2.2 (not_lt.mp hp1))
      subst this; rw [X.mix_one] at he; exact he.symm

