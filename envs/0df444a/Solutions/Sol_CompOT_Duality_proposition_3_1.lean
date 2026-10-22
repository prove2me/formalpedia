-- Prove2me | solution 1 for CompOT.Duality.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:12:48.474781+00:00
-- url     : https://prove2.me/submissions/c0d82aee-7168-4df3-911e-195430ac4392

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

theorem cbt_le {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (g : Fin m → ℝ) (i : Fin n) (j : Fin m) :
    cbarTransform C g i ≤ C i j - g j :=
  ciInf_le (Set.finite_range _).bddBelow j

theorem le_cbt {n m : ℕ} (hm : 0 < m) (C : Matrix (Fin n) (Fin m) ℝ) (g : Fin m → ℝ) (i : Fin n)
    (x : ℝ) (h : ∀ j, x ≤ C i j - g j) : x ≤ cbarTransform C g i := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact le_ciInf h

theorem solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (C : Matrix (Fin n) (Fin m) ℝ) :
    (∀ f f' : Fin n → ℝ, f ≤ f' → cTransform C f' ≤ cTransform C f) ∧
      (∀ f : Fin n → ℝ, f ≤ cbarTransform C (cTransform C f)) ∧
      (∀ g : Fin m → ℝ, g ≤ cTransform C (cbarTransform C g)) ∧
      (∀ f : Fin n → ℝ, cTransform C (cbarTransform C (cTransform C f)) = cTransform C f) := by
  have h1 : ∀ f f' : Fin n → ℝ, f ≤ f' → cTransform C f' ≤ cTransform C f := by
    intro f f' hff j
    refine le_ct hn C f j _ fun i => ?_
    have := ct_le C f' i j
    have := hff i
    linarith
  have h2 : ∀ f : Fin n → ℝ, f ≤ cbarTransform C (cTransform C f) := by
    intro f i
    refine le_cbt hm C _ i _ fun j => ?_
    have := ct_le C f i j
    linarith
  have h3 : ∀ g : Fin m → ℝ, g ≤ cTransform C (cbarTransform C g) := by
    intro g j
    refine le_ct hn C _ j _ fun i => ?_
    have := cbt_le C g i j
    linarith
  refine ⟨h1, h2, h3, fun f => le_antisymm ?_ (h3 _)⟩
  exact h1 _ _ (h2 f)

