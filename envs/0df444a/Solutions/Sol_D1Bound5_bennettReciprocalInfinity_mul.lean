-- Prove2me | solution 1 for D1Bound5.bennettReciprocalInfinity_mul
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:36:42.055713+00:00
-- url     : https://prove2.me/submissions/91a79f57-f107-491e-ac32-cb43aa9966d1

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettPartialFractions_Definitions
import Definitions.Def_D1Bound5_BennettResiduesAtInfinity_Definitions
import Theorems.Thm_D1Bound5_bennettNegativeBinomial_mul

section
open Finset Polynomial

namespace D1Bound5

section Reverse

variable {F : Type*} [Field F]



end Reverse

section Residues

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]









private theorem bennett_reverse_pow (p : F[X]) (n : ℕ) :
    (p ^ n).reverse = p.reverse ^ n := by
  induction n with
  | zero => simp [Polynomial.reverse]
  | succ n ih => rw [pow_succ, Polynomial.reverse_mul_of_domain, ih, pow_succ]

private theorem bennett_reverse_X_sub_C (a : F) :
    (X - C a : F[X]).reverse = 1 - C a * X := by
  have hsub : (X - C a : F[X]) = X + C (-a) := by simp [sub_eq_add_neg]
  have hX : (X : F[X]).reverse = 1 := by
    simp only [Polynomial.reverse, Polynomial.natDegree_X, Polynomial.reflect_one_X]
  rw [hsub, Polynomial.reverse_add_C, hX, Polynomial.natDegree_X, pow_one, map_neg]
  ring

/-- The explicit product at infinity really inverts the reversed denominator. -/
theorem _root_.solution
    (a : ι → F) (e : ι → ℕ) :
    ((bennettPoleDenominator a e).reverse : PowerSeries F) *
      bennettReciprocalInfinity a e = 1 := by
  classical
  have hprod (s : Finset ι) :
      (∏ i ∈ s, (X - C (a i) : F[X]) ^ (e i + 1)).reverse =
        ∏ i ∈ s, ((X - C (a i) : F[X]) ^ (e i + 1)).reverse := by
    induction s using Finset.induction_on with
    | empty => simp [Polynomial.reverse]
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Polynomial.reverse_mul_of_domain, ih, Finset.prod_insert hi]
  unfold bennettPoleDenominator bennettReciprocalInfinity
  rw [hprod]
  change Polynomial.coeToPowerSeries.ringHom (∏ i, _) * (∏ i, _) = 1
  rw [map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i hi
  rw [bennett_reverse_pow, bennett_reverse_X_sub_C]
  change Polynomial.coeToPowerSeries.ringHom ((1 - C (a i) * X) ^ (e i + 1)) * _ = 1
  simp only [map_pow, map_sub, map_mul, map_one, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, Polynomial.coe_X]
  have h := congrArg (PowerSeries.rescale (-a i))
    (bennettNegativeBinomial_mul (F := F) (e i + 1))
  simpa only [map_mul, map_pow, map_add, map_one, PowerSeries.rescale_X,
    map_neg, neg_mul, sub_eq_add_neg] using h



end Residues

end D1Bound5
end
