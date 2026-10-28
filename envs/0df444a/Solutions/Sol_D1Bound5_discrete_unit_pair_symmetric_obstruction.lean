-- Prove2me | solution 1 for D1Bound5.discrete_unit_pair_symmetric_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:38:57.944988+00:00
-- url     : https://prove2.me/submissions/69cbfcd9-05e1-4571-bbb3-453d1fefbb21

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_D1Bound5_discrete_unit_pair_symmetric_ordered_obstruction

section
open scoped NumberField
open Module

namespace D1Bound5







/-- Symmetric form of the obstruction: both entries extend `{-1,1}`
and both signs of their product plus one are squares. Ordering is
supplied internally, so no mutation or artificial tuple extension is used. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (hdiscrete : ∀ z : R, z ≠ 0 → 1 ≤ ‖f z‖)
    (a b : R) (hA : 3 ≤ ‖f a‖) (hB : 3 ≤ ‖f b‖)
    (ham : ∃ x : R, x ^ 2 = 1 - a) (hap : ∃ y : R, y ^ 2 = 1 + a)
    (hbm : ∃ x : R, x ^ 2 = 1 - b) (hbp : ∃ y : R, y ^ 2 = 1 + b)
    (habm : ∃ v : R, v ^ 2 = 1 - a * b)
    (habp : ∃ w : R, w ^ 2 = 1 + a * b) : False := by
  obtain ⟨v, hv⟩ := habm
  obtain ⟨w, hw⟩ := habp
  rcases le_total ‖f a‖ ‖f b‖ with hAB | hBA
  · obtain ⟨x, hx⟩ := hbm
    obtain ⟨y, hy⟩ := hbp
    exact discrete_unit_pair_symmetric_ordered_obstruction f hdiscrete a b x y v w
      hA hAB hx hy hv hw
  · obtain ⟨x, hx⟩ := ham
    obtain ⟨y, hy⟩ := hap
    exact discrete_unit_pair_symmetric_ordered_obstruction f hdiscrete b a x y v w
      hB hBA hx hy (by simpa only [mul_comm] using hv)
      (by simpa only [mul_comm] using hw)



end D1Bound5
end
