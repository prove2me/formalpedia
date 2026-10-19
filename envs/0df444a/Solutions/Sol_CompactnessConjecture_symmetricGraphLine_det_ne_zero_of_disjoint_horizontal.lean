-- Prove2me | solution 1 for CompactnessConjecture.symmetricGraphLine_det_ne_zero_of_disjoint_horizontal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/deae1dd1-0416-4016-9da8-ec41aee3cf01

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (a b c : K)
    (hhorizontal :
      Disjoint (symmetricGraphLine K a b c).1
        (symmetricGraphLine K 0 0 0).1) :
    symmetricDet a b c ≠ 0 := by
  intro hdet
  have hkernel :
      ∃ x y : K,
        (x ≠ 0 ∨ y ≠ 0) ∧
          a * x + b * y = 0 ∧
          b * x + c * y = 0 := by
    by_cases ha : a = 0
    · have hb : b = 0 := by
        have hsq : b ^ 2 = 0 := by
          simpa [symmetricDet, ha] using hdet
        exact eq_zero_of_pow_eq_zero hsq
      exact ⟨1, 0, Or.inl one_ne_zero, by simp [ha, hb],
        by simp [hb]⟩
    · refine ⟨b, -a, Or.inr (neg_ne_zero.mpr ha), ?_, ?_⟩
      · ring
      · unfold symmetricDet at hdet
        linear_combination -hdet
  obtain ⟨x, y, hnonzero, hfirst, hsecond⟩ := hkernel
  let w := symmetricGraphVector K a b c x y
  have hwgraph : w ∈ (symmetricGraphLine K a b c).1 := by
    change w ∈ LinearMap.range (symmetricGraphLinearMap K a b c)
    exact ⟨![x, y], rfl⟩
  have hwhorizontal : w ∈ (symmetricGraphLine K 0 0 0).1 := by
    change w ∈ LinearMap.range (symmetricGraphLinearMap K 0 0 0)
    refine ⟨![x, y], ?_⟩
    funext i
    fin_cases i <;>
      simp [symmetricGraphLinearMap, symmetricGraphVector,
        w, hfirst, hsecond]
  have hwzero : w = (0 : SymplecticVector K) := by
    have hbot : w ∈ (⊥ : Submodule K (SymplecticVector K)) :=
      hhorizontal.le_bot ⟨hwgraph, hwhorizontal⟩
    simpa using hbot
  have hxzero : x = 0 := by
    simpa [w, symmetricGraphVector] using congrFun hwzero 0
  have hyzero : y = 0 := by
    simpa [w, symmetricGraphVector] using congrFun hwzero 2
  exact hnonzero.elim (fun h => h hxzero) (fun h => h hyzero)
end CompactnessConjecture
