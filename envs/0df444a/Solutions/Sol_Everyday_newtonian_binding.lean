-- Prove2me | solution 1 for Everyday.newtonian_binding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:23:54.545483+00:00
-- url     : https://prove2.me/submissions/43fde41c-fd6e-4991-9c4b-f1ac3d5ffa5f

import Mathlib
import Definitions.Def_Everyday_spacetime__e5fc57
import Definitions.Def_Everyday_sectors

open scoped BigOperators

open Everyday
/-- Gravity, at the everyday level: Newtonian gravitation is
attractive. For finitely many positive masses at pairwise distinct
positions, the gravitational binding energy — half the sum of the pair
energies over ordered pairs of distinct particles — is strictly
negative. This is the everyday face of the (m_p²/2) R sector: at the
everyday level the Einstein–Hilbert term reduces to Newtonian
gravitation, and Newtonian gravitation binds. -/


theorem solution (ι : Type) [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (G : ℝ) (m : ι → ℝ) (q : ι → ℝ)
    (hG : 0 < G) (hm : ∀ i, 0 < m i) (hq : ∀ i j, i ≠ j → q i ≠ q j) :
    ∑ p ∈ Finset.univ.filter (fun p : ι × ι => p.1 ≠ p.2),
      -(G * m p.1 * m p.2 / (2 * |q p.1 - q p.2|)) < 0 := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne ι
  have hne : (Finset.univ.filter (fun p : ι × ι => p.1 ≠ p.2)).Nonempty := ⟨(a, b), by simp [hab]⟩
  rw [Finset.sum_neg_distrib, neg_lt_zero]
  apply Finset.sum_pos _ hne
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have h1 : 0 < |q p.1 - q p.2| := abs_pos.mpr (sub_ne_zero.mpr (hq _ _ hp))
  have := hm p.1
  have := hm p.2
  positivity


