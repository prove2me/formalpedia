-- Prove2me | solution 1 for D1Bound5.SmallPairGraphProperty.symmetry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:37:50.943402+00:00
-- url     : https://prove2.me/submissions/d5060410-e47b-4f96-a057-980a588459e5

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphSymmetry_Definitions
import Theorems.Thm_D1Bound5_smallExtensionSymmetry_involutive
import Theorems.Thm_D1Bound5_smallExtensionSymmetry_norm
import Theorems.Thm_D1Bound5_smallExtensionSymmetry_zero

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt



private theorem smallPairSymmetry_square {tau nu : ℤ} (sgn conj : Bool)
    (a z : QuadInt tau nu) (h : ∃ r : QuadInt tau nu, r*r = a*z+1) :
    ∃ r : QuadInt tau nu, r*r =
      smallExtensionSymmetry sgn conj a*smallExtensionSymmetry sgn conj z+1 := by
  obtain ⟨r, hr⟩ := h
  have hstar : star r*star r = star a*star z+1 := by
    simpa only [star_mul, star_add, star_one, mul_comm] using congrArg star hr
  cases sgn <;> cases conj
  · exact ⟨r, hr⟩
  · exact ⟨star r, hstar⟩
  · exact ⟨r, by simpa [smallExtensionSymmetry] using hr⟩
  · exact ⟨star r, by simpa [smallExtensionSymmetry] using hstar⟩

/-- The entire triangle exclusion, including all three compatibility edges,
transports through each simultaneous sign/conjugation symmetry. -/
theorem _root_.solution {tau nu : ℤ}
    (A : Finset (QuadInt tau nu)) (hA : SmallPairGraphProperty A)
    (sgn conj : Bool) :
    SmallPairGraphProperty (A.image (smallExtensionSymmetry sgn conj)) := by
  let F := smallExtensionSymmetry (tau := tau) (nu := nu) sgn conj
  have hF : Function.Involutive F := smallExtensionSymmetry_involutive sgn conj
  have hzero : F 0 = 0 := smallExtensionSymmetry_zero sgn conj
  intro t ht hproper hlarge hbound
  have hFt : IsD1Tuple (fun i => F (t i)) := by
    refine ⟨hF.injective.comp ht.1, ?_, ?_⟩
    · intro i hi
      apply ht.2.1 i
      apply hF.injective
      simpa only [hzero] using hi
    · intro i j hij
      exact smallPairSymmetry_square sgn conj _ _ (ht.2.2 i j hij)
  have hback (i : Fin 3) : ProperCommonExtension A (F (t i)) := by
    refine ⟨hFt.2.1 i, ?_, ?_⟩
    · intro hmem
      apply (hproper i).2.1
      exact Finset.mem_image.mpr ⟨F (t i), hmem, hF (t i)⟩
    · intro a ha
      have hs := (hproper i).2.2 (F a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      have h := smallPairSymmetry_square sgn conj (F a) (t i) hs
      simpa only [show smallExtensionSymmetry sgn conj (F a) = a from hF a] using h
  apply hA (fun i => F (t i)) hFt hback
  · intro i
    simpa only [F, smallExtensionSymmetry_norm] using hlarge i
  · intro i
    simpa only [F, smallExtensionSymmetry_norm] using hbound i





end D1Bound5
end
