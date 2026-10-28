-- Prove2me | solution 1 for D1Bound5.SmallTripleExtensionProperty.symmetry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:37:35.670713+00:00
-- url     : https://prove2.me/submissions/9813f0ad-662c-4335-b113-c7e82db929a7

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
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Theorems.Thm_D1Bound5_smallExtensionSymmetry_involutive
import Theorems.Thm_D1Bound5_smallExtensionSymmetry_norm
import Theorems.Thm_D1Bound5_smallExtensionSymmetry_zero

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt





private theorem properCommonExtension_map
    {R : Type*} [CommRing R] [DecidableEq R]
    (F : R → R) (hF : Function.Injective F) (hzero : F 0 = 0)
    (hsquare : ∀ a z, (∃ r : R, r*r = a*z+1) →
      ∃ r : R, r*r = F a*F z+1)
    (A : Finset R) (z : R) (hz : ProperCommonExtension A z) :
    ProperCommonExtension (A.image F) (F z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hz.1
    apply hF
    simpa only [hzero] using h
  · intro h
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
    have he' : a = z := hF he
    exact hz.2.1 (he' ▸ ha)
  · intro a ha
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    exact hsquare a' z (hz.2.2 a' ha')











private theorem smallExtensionSymmetry_square {tau nu : ℤ} (sgn conj : Bool)
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

/-- Proper extension uniqueness and the norm bound survive each of the four
simultaneous sign/conjugation symmetries. -/
theorem _root_.solution {tau nu : ℤ}
    (A : Finset (QuadInt tau nu)) (hA : SmallTripleExtensionProperty A)
    (sgn conj : Bool) :
    SmallTripleExtensionProperty (A.image (smallExtensionSymmetry sgn conj)) := by
  let F := smallExtensionSymmetry (tau := tau) (nu := nu) sgn conj
  have hF : Function.Involutive F := smallExtensionSymmetry_involutive sgn conj
  have hback (z : QuadInt tau nu) (hz : ProperCommonExtension (A.image F) z) :
      ProperCommonExtension A (F z) := by
    have h := properCommonExtension_map F hF.injective
      (smallExtensionSymmetry_zero sgn conj) (smallExtensionSymmetry_square sgn conj)
      (A.image F) z hz
    have himage : (A.image F).image F = A := by
      have hFF : F ∘ F = id := by
        funext x
        exact hF x
      rw [Finset.image_image, hFF, Finset.image_id]
    rwa [himage] at h
  constructor
  · intro z hz hNz
    have hN : (F z).norm ≤ 10^80 := by
      simpa only [F, smallExtensionSymmetry_norm] using hNz
    have h := hA.1 (F z) (hback z hz) hN
    simpa only [F, smallExtensionSymmetry_norm] using h
  · intro z w hz hw hNz hNw
    apply hF.injective
    apply hA.2 (F z) (F w) (hback z hz) (hback w hw)
    · simpa only [F, smallExtensionSymmetry_norm] using hNz
    · simpa only [F, smallExtensionSymmetry_norm] using hNw







end D1Bound5
end
