-- Prove2me | solution 1 for CompOT.Duality.sec_3_2_semidual_inequality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:12:30.179511+00:00
-- url     : https://prove2.me/submissions/ffd0768c-6d1e-4109-9fc6-d1d243052ec8

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

theorem sol_admissible {n m : ℕ} (hn : 0 < n) (C : Matrix (Fin n) (Fin m) ℝ)
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

theorem solution {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (C : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ)
    (hfg : dualFeasible C f g) :
    dualObj a b f g ≤ dualObj a b f (cTransform C f) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have := ha.2
      simp at this
    · exact h
  have hle := (sol_admissible hn C f).2 g hfg
  unfold dualObj
  have : ∑ j, g j * b j ≤ ∑ j, cTransform C f j * b j :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hle j) (hb.1 j)
  linarith

