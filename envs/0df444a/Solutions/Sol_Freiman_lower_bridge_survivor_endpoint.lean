-- Prove2me | solution 1 for Freiman.lower_bridge_survivor_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T10:30:21.970994+00:00
-- url     : https://prove2.me/submissions/984c2dfa-9041-4291-a541-a90616d15693

import Mathlib
-- Adapted from tav_math, accepted Prove2Me submission ad762493-8337-481f-be1d-971c5e40785b.
import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (hlarge : ∀ c n k, lowerBridgeZero c = decide (n=0) → lowerBridgeSurvivorLarge c n k) (t : ℝ) (f : LowerInitialFamily) (n k p : ℕ)
    (hmarked : (f = .A ∧ k = 0) ∨ (f = .B ∧ k = 0) ∨ (f = .C ∧ p = 0))
    (hsafe : lowerInitialSafeBound t f n k p) (s : LowerPair)
    (hnorm : lowerNormalize s =
      ((lowerNormalize (lowerFamilyPair f n k p)).1 ++ [1],
       (lowerNormalize (lowerFamilyPair f n k p)).2 ++ [1])) :
    lowerLocalLower s ([2],[2]) ≤ lowerLocalCoordinate s t := by
  unfold lowerInitialSafeBound at hsafe
  obtain ⟨h1, h2⟩ := hsafe
  have hE : (if (lowerNormalize (lowerFamilyPair f n k p)).1.length % 2 = 0 then t ≤ lowerEndpoint ((lowerNormalize (lowerFamilyPair f n k p)).1 ++ [1,2], (lowerNormalize (lowerFamilyPair f n k p)).2 ++ [1,2]) (decide ((lowerNormalize (lowerFamilyPair f n k p)).1.length % 2 = 0)) else lowerEndpoint ((lowerNormalize (lowerFamilyPair f n k p)).1 ++ [1,2], (lowerNormalize (lowerFamilyPair f n k p)).2 ++ [1,2]) (decide ((lowerNormalize (lowerFamilyPair f n k p)).1.length % 2 = 0)) ≤ t) := by
    rcases hmarked with ⟨hf, hk⟩ | ⟨hf, hk⟩ | ⟨hf, hp⟩
    · exact h2 (Or.inl ⟨hf, hk⟩)
    · exact h2 (Or.inr ⟨hf, hk⟩)
    · exact h1 hf hp
  have hchild : lowerChild s ([2],[2]) = ((lowerNormalize (lowerFamilyPair f n k p)).1 ++ [1,2], (lowerNormalize (lowerFamilyPair f n k p)).2 ++ [1,2]) := by
    simp only [lowerChild, hnorm]
    simp
  have hslen : (lowerNormalize s).1.length = (lowerNormalize (lowerFamilyPair f n k p)).1.length + 1 := by
    rw [hnorm]
    simp
  unfold lowerLocalLower lowerLocalCoordinate
  rw [hslen, hchild]
  by_cases hpar : (lowerNormalize (lowerFamilyPair f n k p)).1.length % 2 = 0
  · rw [if_pos hpar, decide_eq_true hpar] at hE
    rw [if_neg (by omega : ¬ (((lowerNormalize (lowerFamilyPair f n k p)).1.length + 1) % 2 = 0))]
    rw [if_neg (by omega : ¬ (((lowerNormalize (lowerFamilyPair f n k p)).1.length + 1) % 2 = 0))]
    linarith
  · rw [if_neg hpar, decide_eq_false hpar] at hE
    rw [if_pos (by omega : (((lowerNormalize (lowerFamilyPair f n k p)).1.length + 1) % 2 = 0))]
    rw [if_pos (by omega : (((lowerNormalize (lowerFamilyPair f n k p)).1.length + 1) % 2 = 0))]
    linarith
#print axioms solution
example : (∀ (hlarge : ∀ c n k, lowerBridgeZero c = decide (n=0) → lowerBridgeSurvivorLarge c n k) (t : ℝ) (f : LowerInitialFamily) (n k p : ℕ)
    (hmarked : (f = .A ∧ k = 0) ∨ (f = .B ∧ k = 0) ∨ (f = .C ∧ p = 0))
    (hsafe : lowerInitialSafeBound t f n k p) (s : LowerPair)
    (hnorm : lowerNormalize s =
      ((lowerNormalize (lowerFamilyPair f n k p)).1 ++ [1],
       (lowerNormalize (lowerFamilyPair f n k p)).2 ++ [1])) , 
    lowerLocalLower s ([2],[2]) ≤ lowerLocalCoordinate s t) := @solution
