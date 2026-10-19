-- Prove2me | solution 1 for ContWeatherall.alternating_sum_cons_removeNth
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-18T21:43:59.87847+00:00
-- url     : https://prove2.me/submissions/155277b9-af56-497b-8038-3a8d9c6e6dfc

import Mathlib
import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

theorem acr_main {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (v : Fin (n + 1) → M) :
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • f (Fin.cons (v i) (i.removeNth v)) = (n + 1) • f v := by
  have h : ∀ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • f (Fin.cons (v i) (i.removeNth v)) = f v := by
    intro i
    have := f.map_insertNth i (v i) (i.removeNth v)
    rw [Fin.insertNth_self_removeNth] at this
    rw [this, Matrix.vecCons]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

end ContWeatherall

theorem solution {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (v : Fin (n + 1) → M) :
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • f (Fin.cons (v i) (i.removeNth v)) = (n + 1) • f v :=
  ContWeatherall.acr_main f v
