-- Prove2me | solution 1 for D1Bound5.IsD1.one_three_all_positive_integers
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:44:03.561831+00:00
-- url     : https://prove2.me/submissions/f0aa2159-4788-46c1-90cf-43f12b5c4b44

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_IsD1_card_le_four_of_one_three_negative
import Theorems.Thm_D1Bound5_full_ring_one_three_common_extension_is_integer

section
open scoped NumberField
open Module

namespace D1Bound5





























/-- If a D(1)-set containing 1 and 3 has at least five entries, every
entry is a positive ordinary integer, in the same full number ring. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) {A : Finset (𝓞 K)} (hA : IsD1 A)
    (h1 : (1 : 𝓞 K) ∈ A) (h3 : (3 : 𝓞 K) ∈ A) (hcard : 4<A.card) :
    ∀ z ∈ A, ∃ n : ℤ, 0<n ∧ z=(n : 𝓞 K) := by
  intro z hz
  by_cases hz1 : z=1
  · exact ⟨1,by norm_num,by simpa using hz1⟩
  by_cases hz3 : z=3
  · exact ⟨3,by norm_num,by simpa using hz3⟩
  obtain ⟨n,rfl⟩ := full_ring_one_three_common_extension_is_integer hK
    (by simpa only [one_mul] using hA.2 1 h1 z hz (Ne.symm hz1))
    (hA.2 3 h3 z hz (Ne.symm hz3))
  have hn0 : n ≠ 0 := by
    intro he
    subst n
    exact hA.1 0 (by simpa using hz) rfl
  have hn : ¬n<0 := by
    intro hn
    have := hA.card_le_four_of_one_three_negative hK h1 h3 ⟨n,hn,hz⟩
    omega
  exact ⟨n,by omega,rfl⟩

end D1Bound5
end
