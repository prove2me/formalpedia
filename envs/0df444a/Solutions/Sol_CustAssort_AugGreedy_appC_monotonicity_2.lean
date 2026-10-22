-- Prove2me | solution 2 for CustAssort.AugGreedy.appC_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:21:10.313409+00:00
-- url     : https://prove2.me/submissions/3d1e42ff-6bd1-4ac3-b03f-7caf04628d67

import Mathlib
import Definitions.Def_CustAssort_AugGreedy_Setting

set_option autoImplicit false
open CustAssort.AugGreedy

theorem solution {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (j : Fin m) (A B : Finset (Fin n)) (hAB : A ⊆ B) :
    fj v r j A ≤ fj v r j B := by
  unfold fj
  apply Finset.sup'_le
  intro S hS
  exact Finset.le_sup' (rev v r j) (Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hS).trans hAB))
