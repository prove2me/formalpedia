-- Prove2me | solution 1 for FirstLawThermo.quasiStatic_adiabatic_work_eq_neg_deltaU
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T13:15:21.339027+00:00
-- url     : https://prove2.me/submissions/755273ce-294b-45cd-8f0b-0cf83007fc86

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem solution {σ : Type*}
    (W : σ → σ → ℝ) (U : σ → ℝ) (O : σ)
    (hrev : ∀ A : σ, W A O = -W O A)
    (hpath : ∀ A B : σ, W A B = W A O + W O B)
    (hU : ∀ A : σ, U A = U O - W O A) :
    ∀ A B : σ, -W A B = U B - U A := by
  intro A B
  rw [hpath A B, hrev A, hU A, hU B]
  ring
