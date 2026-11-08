-- Prove2me | solution 1 for DynStochMatching.Reward.claim_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:22:29.35595+00:00
-- url     : https://prove2.me/submissions/feddae1b-9d77-4a18-ab46-1c9b0274441e

import Definitions.Def_DynStochMatching_Reward_CountChains

open MeasureTheory Filter
open scoped ENNReal Classical

open DynStochMatching.Reward in
theorem solution {n : ℕ} (D : DynStochMatching.Reward.Instance n) (flow : DynStochMatching.Reward.Flow n)
    (x y : DynStochMatching.Reward.CountState n) (A : Set (DynStochMatching.Reward.CountState n))
    (hxy : x ≤ y) (hupper : IsUpperSet A) (hx : x ∈ A) :
    ∀ a ∈ DynStochMatching.Reward.boundaryCoordinates D flow y A, x a = y a := by
  intro a ha
  obtain ⟨hpos, hnot, -⟩ := ha
  by_contra hne
  have hlt : x a < y a := lt_of_le_of_ne (hxy a) hne
  apply hnot
  have hle : x ≤ DynStochMatching.Reward.decrease y a := by
    intro b
    unfold DynStochMatching.Reward.decrease
    by_cases hb : b = a
    · rw [hb, Function.update_self]
      exact Nat.le_sub_one_of_lt hlt
    · rw [Function.update_of_ne hb]
      exact hxy b
  exact hupper hle hx
