-- Prove2me | solution 1 for D1Bound5.firstPairClassified_of_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:38:52.630002+00:00
-- url     : https://prove2.me/submissions/815fe55d-e987-492b-8fbb-254abf49a206

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Theorems.Thm_D1Bound5_QuadInt_mem_disk_iff
import Theorems.Thm_D1Bound5_QuadInt_norm_formula
import Theorems.Thm_D1Bound5_first_pair_root_norm_le_eight
import Theorems.Thm_D1Bound5_pairSeedCandidate_eq

section
namespace D1Bound5
open QuadInt













theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu)
    (small roots : List (QuadInt tau nu))
    (rows : List ((ℤ × ℤ) × (ℤ × ℤ)))
    (hsmall : ∀ a ∈ disk tau nu 8, a ∈ small)
    (hroots : ∀ q ∈ disk tau nu 8, q ∈ roots)
    (hcheck : firstPairClassifiedBool small roots rows = true)
    (a b : QuadInt tau nu) (hnorm : FirstPairNorms a b)
    (hroot : ∃ q, q*q = a*b+1) :
    (a = 1 ∧ b = 3) ∨ (a = -1 ∧ b = -3) ∨ firstPairCoordinates a b ∈ rows := by
  have ha : a ≠ 0 := by
    intro h
    rcases hnorm with hN | hN <;> simp [h, norm_formula] at hN
  have hNa : a.norm ≤ 8 := by rcases hnorm with hN | hN <;> omega
  have hprod : a.norm*b.norm ≤ 63 := by
    rcases hnorm with hN | hN
    · rw [hN.1]
      simpa using hN.2.2
    · rw [hN.1]
      omega
  obtain ⟨q,hq⟩ := hroot
  have hNq := first_pair_root_norm_le_eight hd a b q hprod hq
  have hma := hsmall a ((mem_disk_iff hd 8 a).2 hNa)
  have hmq := hroots q ((mem_disk_iff hd 8 q).2 hNq)
  have hc := List.all_eq_true.mp hcheck a hma
  have ga : decide (a ≠ 0) = true := by simp [ha]
  simp only [ga, if_true] at hc
  have hcq := List.all_eq_true.mp hc q hmq
  have heq := pairSeedCandidate_eq hd a b q ha hq
  simpa [heq, hq, hnorm] using hcq









end D1Bound5
end
