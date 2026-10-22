-- Prove2me | solution 1 for CompOT.Duality.sec_3_2_ctransform_admissible
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:12:25.565205+00:00
-- url     : https://prove2.me/submissions/1ac3fa81-a563-47ae-82d6-f14640092363

import Mathlib
import Definitions.Def_CompOT_Duality_Defs
set_option autoImplicit false
open CompOT.Duality

theorem ct_le {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → ℝ) (i : Fin n) (j : Fin m) :
    cTransform C f j ≤ C i j - f i :=
  ciInf_le (Set.finite_range _).bddBelow i

theorem le_ct {n m : ℕ} (hn : 0 < n) (C : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → ℝ) (j : Fin m)
    (x : ℝ) (h : ∀ i, x ≤ C i j - f i) : x ≤ cTransform C f j := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact le_ciInf h

theorem solution {n m : ℕ} (hn : 0 < n) (C : Matrix (Fin n) (Fin m) ℝ)
    (f : Fin n → ℝ) :
    dualFeasible C f (cTransform C f) ∧
      ∀ g : Fin m → ℝ, dualFeasible C f g → g ≤ cTransform C f := by
  constructor
  · intro i j
    have := ct_le C f i j
    linarith
  · intro g hg j
    refine le_ct hn C f j _ fun i => ?_
    have := hg i j
    linarith

