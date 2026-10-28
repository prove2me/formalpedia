-- Prove2me | solution 1 for D1Bound5.coherentQuotientForm_norm_le_remainder
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:42:15.167574+00:00
-- url     : https://prove2.me/submissions/4e22c431-6d4b-4e40-a2d7-ca907e1c7eb8

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentFormBounds_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Theorems.Thm_D1Bound5_coherentQuotientForm_normalized_eq

section
open Finset

namespace D1Bound5

/-- Exact-form norm control before inserting a numerical remainder
estimate.  This interface is shared by the parameter and four-anchor
lemmas. -/
theorem _root_.solution
    {m : ℕ} (a : Fin m → ℂ) (hm : 2 ≤ m)
    (ha : ∀ i, a i ≠ 0) (hinj : Function.Injective a)
    (Delta p q eta : ℂ) (hDelta : Delta ≠ 0) (heta : eta ≠ 0)
    (hp : ∀ i, ‖p⁻¹*(a i)⁻¹‖ < 1) (hq : ∀ i, ‖q⁻¹*(a i)⁻¹‖ < 1) :
    ‖coherentQuotientForm a Delta p q eta‖ ≤ ‖Delta‖*‖eta‖*
      (‖1-(1+p⁻¹*q⁻¹)^(1/2 : ℂ)‖ + ‖coherentRemainder a p q‖/(∏ i, ‖a i‖)) := by
  let c : ℂ := (-1)^ (m-1) * (∏ i, a i)⁻¹
  have hexact := coherentQuotientForm_normalized_eq a hm ha hinj Delta p q eta hDelta heta hp hq
  have hmul : coherentQuotientForm a Delta p q eta = (Delta*eta)*
      (1-(1+p⁻¹*q⁻¹)^(1/2 : ℂ)+c*coherentRemainder a p q) := by
    have h := (div_eq_iff (mul_ne_zero hDelta heta)).mp hexact
    simpa only [c, mul_comm] using h
  have hc : ‖c‖ = (∏ i, ‖a i‖)⁻¹ := by
    simp [c, norm_mul, norm_pow, norm_inv, norm_prod]
  rw [hmul, norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ ‖Delta‖*‖eta‖)
  calc
    _ ≤ ‖1-(1+p⁻¹*q⁻¹)^(1/2 : ℂ)‖ + ‖c*coherentRemainder a p q‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul, hc]; ring









end D1Bound5
end
