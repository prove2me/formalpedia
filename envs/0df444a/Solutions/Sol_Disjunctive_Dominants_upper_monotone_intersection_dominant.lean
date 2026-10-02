-- Prove2me | solution 1 for Disjunctive.Dominants.upper_monotone_intersection_dominant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T04:24:36.524384+00:00
-- url     : https://prove2.me/submissions/3c2cb067-b68f-4c3a-b7bd-d0a9287aa69e

import Mathlib
import Definitions.Def_Disjunctive_Dominants_Basic

namespace Disjunctive.Dominants

theorem dot_mono_7eee {n : ℕ} (a x y : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j) (hxy : x ≤ y) :
    dotProduct a x ≤ dotProduct a y := by
  unfold dotProduct
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hxy j) (ha j)

end Disjunctive.Dominants

open Disjunctive.Dominants in
theorem solution {n m : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (P : Set (Fin n → ℝ)) (Pi : Fin m → Set (Fin n → ℝ))
    (hP : P = UnitCube n ∩ {x | ∀ i, 1 ≤ dotProduct (A i) x})
    (hPi : ∀ i, Pi i = UnitCube n ∩ {x | 1 ≤ dotProduct (A i) x})
    (hupper : IsUpperMonotone P) :
    Dominant P = ⋂ i, Dominant (Pi i) := by
  ext y
  simp only [Set.mem_iInter]
  constructor
  · rintro ⟨hy0, x, hxP, hxy⟩ i
    refine ⟨hy0, x, ?_, hxy⟩
    rw [hP] at hxP
    rw [hPi i]
    exact ⟨hxP.1, hxP.2 i⟩
  · intro h
    have hy0 : 0 ≤ y := (h 0).1
    refine ⟨hy0, fun j => min (y j) 1, ?_, fun j => min_le_left _ _⟩
    rw [hP]
    refine ⟨fun j => ⟨le_min (hy0 j) zero_le_one, min_le_right _ _⟩, ?_⟩
    intro i
    obtain ⟨-, x, hx, hxy⟩ := h i
    rw [hPi i] at hx
    obtain ⟨hxc, hx1⟩ := hx
    refine le_trans hx1 (dot_mono_7eee _ _ _ (hA i) ?_)
    intro j
    exact le_min (hxy j) (hxc j).2
