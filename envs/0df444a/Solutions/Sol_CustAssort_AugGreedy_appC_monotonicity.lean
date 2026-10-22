-- Prove2me | solution 1 for CustAssort.AugGreedy.appC_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:17:01.154351+00:00
-- url     : https://prove2.me/submissions/b36452aa-ba98-420d-b74f-4dae8f4e9eda

import Mathlib
import Definitions.Def_CustAssort_AugGreedy_Setting

set_option autoImplicit false
open CustAssort.AugGreedy

theorem solution {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (j : Fin m) (A B : Finset (Fin n)) (hAB : A ⊆ B) :
    fj v r j A ≤ fj v r j B := by
  unfold fj
  exact Finset.sup'_mono _ (Finset.powerset_mono.mpr hAB) _
