-- Prove2me | solution 1 for DirichletUnitTheorem.torsion_units_of_exists_isReal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:19:48.564417+00:00
-- url     : https://prove2.me/submissions/4da4df95-706d-4c3e-abcd-7a1b2b7f6e3c

import Mathlib
open NumberField

theorem solution (K : Type*) [Field K] [NumberField K]
    (h : ∃ w : InfinitePlace K, w.IsReal) (u : (𝓞 K)ˣ) (hu : IsOfFinOrder u) :
    u = 1 ∨ u = -1 := by
  have hK : orderOf ((u : 𝓞 K) : K) = orderOf u := by
    rw [← orderOf_units]
    exact orderOf_injective (algebraMap (𝓞 K) K).toMonoidHom RingOfIntegers.coe_injective _
  by_cases! hc : 2 < orderOf u
  · exfalso
    rw [← hK] at hc
    have := NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc
      (IsPrimitiveRoot.orderOf ((u : 𝓞 K) : K))
    obtain ⟨w, hw⟩ := h
    rw [NumberField.nrRealPlaces_eq_zero_iff] at this
    exact InfinitePlace.not_isReal_iff_isComplex.mpr (this.isComplex w) hw
  · interval_cases hi : orderOf u
    · exact absurd hi (orderOf_pos_iff.2 hu).ne'
    · exact Or.inl (orderOf_eq_one_iff.1 hi)
    · rw [CharP.orderOf_eq_two_iff 0 (by decide)] at hK
      right
      ext
      simp [hK]
