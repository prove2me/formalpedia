-- Prove2me | solution 1 for DualSepClusterLP.positiveTriangleEndpointCertificate
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-19T12:40:02.486935+00:00
-- url     : https://prove2.me/submissions/07a50a29-1347-44f3-8a8e-c9cf76cbbf2b

import Theorems.Thm_DualSepClusterLP_threePositiveTriangleEndpoints
import Theorems.Thm_DualSepClusterLP_twoPositiveTriangleEndpoints

open DualSepClusterLP

theorem solution (s₁ s₂ s₃ : Bool)
    (hs : (s₁ = true ∧ s₂ = true) ∨ (s₂ = true ∧ s₃ = true) ∨ (s₃ = true ∧ s₁ = true))
    (x y z : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hz : z ∈ Set.Icc (0:ℝ) 1) (hn : tripleLower x y z ≤ tripleUpper x y z) :
    0 ≤ signedTriangleSurplus s₁ s₂ s₃ x y z (tripleLower x y z) ∧
    0 ≤ signedTriangleSurplus s₁ s₂ s₃ x y z (tripleUpper x y z) := by
  have rot (s q r : Bool) (a b c : ℝ) :
      (0 ≤ signedTriangleSurplus s q r a b c (tripleLower a b c) ∧
       0 ≤ signedTriangleSurplus s q r a b c (tripleUpper a b c)) ↔
      (0 ≤ signedTriangleSurplus q r s b c a (tripleLower b c a) ∧
       0 ≤ signedTriangleSurplus q r s b c a (tripleUpper b c a)) := by
    simp only [tripleLower,tripleUpper,signedTriangleSurplus,add_assoc,add_comm,add_left_comm,
      max_assoc,max_comm,max_left_comm,min_assoc,min_comm,min_left_comm]
  have cycle (a b c : ℝ) : tripleLower a b c ≤ tripleUpper a b c ↔ tripleLower b c a ≤ tripleUpper b c a := by
    simp only [tripleLower,tripleUpper,add_comm,add_left_comm,add_assoc,
      max_assoc,max_comm,max_left_comm,min_assoc,min_comm,min_left_comm]
  cases s₁ <;> cases s₂ <;> cases s₃ <;> simp at hs
  · exact (rot ..).mpr (twoPositiveTriangleEndpoints y z x hy hz hx ((cycle ..).mp hn))
  · exact (rot ..).mp (twoPositiveTriangleEndpoints z x y hz hx hy ((cycle ..).mpr hn))
  · exact twoPositiveTriangleEndpoints x y z hx hy hz hn
  · exact threePositiveTriangleEndpoints x y z hx hy hz hn
