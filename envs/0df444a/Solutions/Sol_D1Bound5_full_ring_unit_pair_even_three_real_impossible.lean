-- Prove2me | solution 1 for D1Bound5.full_ring_unit_pair_even_three_real_impossible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:31.419847+00:00
-- url     : https://prove2.me/submissions/ea501d66-5e4a-419e-90cf-6dc37b1ca048

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Int.Units
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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions
import Definitions.Def_D1Bound5_UnitPairRealReduction_Definitions
import Theorems.Thm_D1Bound5_full_ring_unit_pair_even_same_sign_impossible
import Theorems.Thm_D1Bound5_unit_pair_pell_even_magnitude

section
open scoped NumberField
open Module

namespace D1Bound5













/-- Three real extensions are impossible when the field parameter is even.
The argument uses actual full-ring squares, so it also covers both choices
of sign for each real extension. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (d : ℤ) (hd : 0 < d) (heven : d % 2 = 0)
    (z : Fin 3 → 𝓞 K) (hreal : ∀ i, UnitPairRealDescription d (z i))
    (hpair : ∀ i j, i ≠ j → ∃ r : 𝓞 K, r^2 = 1+z i*z j) : False := by
  obtain ⟨u0,v0,hv0,hp0,hz0⟩ := hreal 0
  obtain ⟨u1,v1,hv1,hp1,hz1⟩ := hreal 1
  obtain ⟨u2,v2,hv2,hp2,hz2⟩ := hreal 2
  have hpositive (v : ℤ) : 0 < d*v^2+1 := by
    nlinarith only [mul_nonneg hd.le (sq_nonneg v)]
  have hmod0 := unit_pair_pell_even_magnitude d u0 v0 heven hp0
  have hmod1 := unit_pair_pell_even_magnitude d u1 v1 heven hp1
  have hmod2 := unit_pair_pell_even_magnitude d u2 v2 heven hp2
  have hno (i j : Fin 3) (hij : i ≠ j) (m n : ℤ)
      (hm : 0 < m) (hn : 0 < n) (hm4 : m % 4 = 3) (hn4 : n % 4 = 3)
      (hprod : z i*z j = ((m*n : ℤ) : 𝓞 K)) : False := by
    obtain ⟨r,hr⟩ := hpair i j hij
    apply full_ring_unit_pair_even_same_sign_impossible hK m n hm hn hm4 hn4
    refine ⟨r,?_⟩
    rw [pow_two,hprod] at hr
    simpa only [Int.cast_add,Int.cast_one,add_comm] using hr
  rcases hz0 with hz0 | hz0 <;> rcases hz1 with hz1 | hz1 <;> rcases hz2 with hz2 | hz2
  · exact hno 0 1 (by decide) _ _ (hpositive v0) (hpositive v1) hmod0 hmod1
      (by rw [hz0,hz1,Int.cast_mul])
  · exact hno 0 1 (by decide) _ _ (hpositive v0) (hpositive v1) hmod0 hmod1
      (by rw [hz0,hz1,Int.cast_mul])
  · exact hno 0 2 (by decide) _ _ (hpositive v0) (hpositive v2) hmod0 hmod2
      (by rw [hz0,hz2,Int.cast_mul])
  · exact hno 1 2 (by decide) _ _ (hpositive v1) (hpositive v2) hmod1 hmod2
      (by rw [hz1,hz2,neg_mul_neg,Int.cast_mul])
  · exact hno 1 2 (by decide) _ _ (hpositive v1) (hpositive v2) hmod1 hmod2
      (by rw [hz1,hz2,Int.cast_mul])
  · exact hno 0 2 (by decide) _ _ (hpositive v0) (hpositive v2) hmod0 hmod2
      (by rw [hz0,hz2,neg_mul_neg,Int.cast_mul])
  · exact hno 0 1 (by decide) _ _ (hpositive v0) (hpositive v1) hmod0 hmod1
      (by rw [hz0,hz1,neg_mul_neg,Int.cast_mul])
  · exact hno 0 1 (by decide) _ _ (hpositive v0) (hpositive v1) hmod0 hmod1
      (by rw [hz0,hz1,neg_mul_neg,Int.cast_mul])





end D1Bound5
end
