-- Prove2me | solution 1 for D1Bound5.coherentQuotientForm_zero_norm_relation
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:40:53.704803+00:00
-- url     : https://prove2.me/submissions/8fff541d-9e63-4369-b4e8-9b6a4b4ccb78

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



/-- A zero coherent form equates the exact remainder modulus to the
near-one defect modulus.  No asymptotic estimate is assumed. -/
theorem _root_.solution
    {m : ℕ} (a : Fin m → ℂ) (hm : 2 ≤ m)
    (ha : ∀ i, a i ≠ 0) (hinj : Function.Injective a)
    (Delta p q eta : ℂ) (hDelta : Delta ≠ 0) (heta : eta ≠ 0)
    (hp : ∀ i, ‖p⁻¹*(a i)⁻¹‖ < 1) (hq : ∀ i, ‖q⁻¹*(a i)⁻¹‖ < 1)
    (hL : coherentQuotientForm a Delta p q eta = 0) :
    ‖1-(1+p⁻¹*q⁻¹)^(1/2 : ℂ)‖ = ‖coherentRemainder a p q‖/(∏ i, ‖a i‖) := by
  let c : ℂ := (-1)^(m-1)*(∏ i, a i)⁻¹
  have h := coherentQuotientForm_normalized_eq a hm ha hinj Delta p q eta hDelta heta hp hq
  rw [hL, zero_div] at h
  have heq : 1-(1+p⁻¹*q⁻¹)^(1/2 : ℂ) = -c*coherentRemainder a p q := by
    linear_combination -h
  rw [heq, norm_mul, norm_neg]
  have hc : ‖c‖ = (∏ i, ‖a i‖)⁻¹ := by
    simp [c, norm_mul, norm_pow, norm_inv, norm_prod]
  rw [hc]
  ring







end D1Bound5
end
