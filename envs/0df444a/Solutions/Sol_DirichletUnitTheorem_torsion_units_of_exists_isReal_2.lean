-- Prove2me | solution 2 for DirichletUnitTheorem.torsion_units_of_exists_isReal
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:22:15.803419+00:00
-- url     : https://prove2.me/submissions/4d449a37-da4d-4bee-a47f-3371d0845b1f

import Mathlib
set_option autoImplicit false
open NumberField

theorem solution (K : Type*) [Field K] [NumberField K]
    (h : ∃ w : InfinitePlace K, w.IsReal) (u : (𝓞 K)ˣ) (hu : IsOfFinOrder u) :
    u = 1 ∨ u = -1 := by
  obtain ⟨w, hw⟩ := h
  let ψ : K →+* ℝ := InfinitePlace.embedding_of_isReal hw
  let f : 𝓞 K →+* ℝ := ψ.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f :=
    ψ.injective.comp (IsFractionRing.injective (𝓞 K) K)
  obtain ⟨n, hn, hun⟩ := hu.exists_pow_eq_one
  have h1 : (f (u : 𝓞 K)) ^ n = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hun]
    simp
  rcases pow_eq_one_iff_cases.mp h1 with h0 | h1 | ⟨h1, _⟩
  · omega
  · left
    apply Units.ext
    apply hf
    simp [h1]
  · right
    apply Units.ext
    apply hf
    simp [h1]
