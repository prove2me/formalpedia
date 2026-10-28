-- Prove2me | solution 1 for D1Bound5.bennettLocalResidue_eq_decomposition_coeff
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:46.730573+00:00
-- url     : https://prove2.me/submissions/189194c5-2e8e-45d0-8c99-3a5321f52e37

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettResidueCoefficient_Definitions
import Theorems.Thm_D1Bound5_bennettLocalReciprocal_mul
import Theorems.Thm_D1Bound5_bennettLocalResidue_clearedPole_of_ne
import Theorems.Thm_D1Bound5_bennettShiftToSeries_linear

section
open Finset

namespace D1Bound5

section Field

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]



@[simp] theorem bennettShiftToSeries_C (b c : F) :
    bennettShiftToSeries b (Polynomial.C c) = PowerSeries.C c := by
  simp [bennettShiftToSeries]









/-- At its own node, multiplication by the explicit local reciprocal cancels
all other factors of a cleared pole numerator. -/
theorem bennettShift_clearedPole_self (a : ι → F) (ha : Function.Injective a)
    (e : ι → ℕ) (i : ι) (j : Fin (e i + 1)) :
    bennettShiftToSeries (a i) (clearedPoleNumerator a e i j) *
      bennettLocalReciprocal a e i = PowerSeries.X ^ j.val := by
  unfold clearedPoleNumerator
  simp only [map_mul, map_pow, bennettShiftToSeries_linear, sub_self, map_zero,
    zero_add, map_prod]
  rw [mul_assoc, bennettLocalReciprocal_mul a ha e i, mul_one]



/-- Local residues are compatible with scalar multiplication of the numerator. -/
theorem bennettLocalResidue_C_mul (a : ι → F) (e : ι → ℕ)
    (f : Polynomial F) (i : ι) (c : F) :
    bennettLocalResidue a e (Polynomial.C c * f) i =
      c * bennettLocalResidue a e f i := by
  simp only [bennettLocalResidue, map_mul, bennettShiftToSeries_C, mul_assoc,
    PowerSeries.coeff_C_mul]

/-- The concrete local series coefficient equals the simple-pole coefficient
in any exact cleared decomposition. -/
theorem _root_.solution
    (a : ι → F) (ha : Function.Injective a) (e : ι → ℕ)
    (c : (l : ι) → Fin (e l + 1) → F) (f : Polynomial F)
    (hc : f = ∑ l, ∑ j : Fin (e l + 1),
      Polynomial.C (c l j) * clearedPoleNumerator a e l j) (i : ι) :
    bennettLocalResidue a e f i = c i (Fin.last (e i)) := by
  classical
  rw [hc]
  simp only [bennettLocalResidue, map_sum, Finset.sum_mul]
  change (∑ l, ∑ j : Fin (e l + 1),
    bennettLocalResidue a e (Polynomial.C (c l j) * clearedPoleNumerator a e l j) i) = _
  simp only [bennettLocalResidue_C_mul]
  rw [Finset.sum_eq_single i]
  · simp only [bennettLocalResidue, bennettShift_clearedPole_self a ha,
      PowerSeries.coeff_X_pow]
    have heq (j : Fin (e i + 1)) : e i = j.val ↔ j = Fin.last (e i) := by
      constructor
      · intro h
        exact Fin.ext h.symm
      · intro h
        subst j
        rfl
    simp_rw [heq]
    simp [mul_ite]
  · intro l hl hli
    simp only [bennettLocalResidue_clearedPole_of_ne a e i l hli.symm, mul_zero,
      Finset.sum_const_zero]
  · simp



end Field

end D1Bound5
end
