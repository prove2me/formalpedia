-- Prove2me | solution 1 for D1Bound5.coherentQuotientForm_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:50.23699+00:00
-- url     : https://prove2.me/submissions/38b38974-a6e1-4c14-939d-f59d52022ba1

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
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_coherentQuotientForm_normalized_eq
import Theorems.Thm_D1Bound5_coherentRemainder_norm_sub_le
import Theorems.Thm_D1Bound5_coherent_half_binomial_manuscript_anchor_radius

section
open Finset

namespace D1Bound5







/-- An explicit upper bound for the actual coherent form, derived from
its exact analytic identity and the proved coefficient remainder.  This
is the common input for the numerical two-, three-, and four-anchor
estimates; no bound on an unspecified analytic remainder is assumed. -/
theorem _root_.solution
    {m : ℕ} (a : Fin m → ℂ) (hm : 2 ≤ m) (hinj : Function.Injective a)
    (Delta p q eta : ℂ) (hDelta : Delta ≠ 0) (heta : eta ≠ 0)
    (A P : ℝ) (hA : 0 < A) (hP : 0 < P) (ha : ∀ i, A ≤ ‖a i‖)
    (hp : ‖p⁻¹‖ ≤ 1 / P) (hq : ‖q⁻¹‖ ≤ 1 / P) (hAP : 1 < A * P) :
    ‖coherentQuotientForm a Delta p q eta‖ ≤ ‖Delta‖ * ‖eta‖ *
      (‖1 - ((1 + p⁻¹ * q⁻¹) ^ (1 / 2 : ℂ))‖ +
        (‖halfBinomialWeightedCoeff p⁻¹ q⁻¹ m‖ +
          (4 * |halfBinomialCoeff (m + 1)|) / P ^ m *
            (1 / (1 - 1 / (A * P)) ^ m - 1)) / (∏ i, ‖a i‖)) := by
  let E : ℝ := (4 * |halfBinomialCoeff (m + 1)|) / P ^ m *
    (1 / (1 - 1 / (A * P)) ^ m - 1)
  let c : ℂ := (-1 : ℂ) ^ (m - 1) * (∏ i, a i)⁻¹
  have han : ∀ i, a i ≠ 0 := by
    intro i
    exact norm_pos_iff.mp (hA.trans_le (ha i))
  have hxp : ∀ i, ‖p⁻¹ * (a i)⁻¹‖ < 1 := by
    intro i
    exact coherent_half_binomial_manuscript_anchor_radius Finset.univ a p⁻¹ A P
      hA hP (fun j _ => ha j) hp hAP i (Finset.mem_univ i)
  have hxq : ∀ i, ‖q⁻¹ * (a i)⁻¹‖ < 1 := by
    intro i
    exact coherent_half_binomial_manuscript_anchor_radius Finset.univ a q⁻¹ A P
      hA hP (fun j _ => ha j) hq hAP i (Finset.mem_univ i)
  have hexact := coherentQuotientForm_normalized_eq a hm han hinj
    Delta p q eta hDelta heta hxp hxq
  have hmul : coherentQuotientForm a Delta p q eta = (Delta * eta) *
      (1 - ((1 + p⁻¹ * q⁻¹) ^ (1 / 2 : ℂ)) + c * coherentRemainder a p q) := by
    have h := (div_eq_iff (mul_ne_zero hDelta heta)).mp hexact
    calc
      coherentQuotientForm a Delta p q eta =
        (1 - ((1 + p⁻¹ * q⁻¹) ^ (1 / 2 : ℂ)) + c * coherentRemainder a p q) *
          (Delta * eta) := h
      _ = _ := mul_comm _ _
  have htail : ‖coherentRemainder a p q - halfBinomialWeightedCoeff p⁻¹ q⁻¹ m‖ ≤ E :=
    coherentRemainder_norm_sub_le a hm p q A P hA hP ha hp hq hAP
  have hF : ‖coherentRemainder a p q‖ ≤ ‖halfBinomialWeightedCoeff p⁻¹ q⁻¹ m‖ + E := by
    have h := norm_add_le (coherentRemainder a p q - halfBinomialWeightedCoeff p⁻¹ q⁻¹ m)
      (halfBinomialWeightedCoeff p⁻¹ q⁻¹ m)
    rw [sub_add_cancel] at h
    linarith
  have hc : ‖c‖ = (∏ i, ‖a i‖)⁻¹ := by
    simp [c, norm_mul, norm_pow, norm_inv, norm_prod]
  have hprod0 : 0 ≤ ∏ i, ‖a i‖ := Finset.prod_nonneg (fun i _ => norm_nonneg _)
  rw [hmul, norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ ‖Delta‖ * ‖eta‖)
  calc
    ‖1 - ((1 + p⁻¹ * q⁻¹) ^ (1 / 2 : ℂ)) + c * coherentRemainder a p q‖ ≤
      ‖1 - ((1 + p⁻¹ * q⁻¹) ^ (1 / 2 : ℂ))‖ + ‖c * coherentRemainder a p q‖ :=
        norm_add_le _ _
    _ = ‖1 - ((1 + p⁻¹ * q⁻¹) ^ (1 / 2 : ℂ))‖ +
        (∏ i, ‖a i‖)⁻¹ * ‖coherentRemainder a p q‖ := by rw [norm_mul, hc]
    _ ≤ ‖1 - ((1 + p⁻¹ * q⁻¹) ^ (1 / 2 : ℂ))‖ +
        (∏ i, ‖a i‖)⁻¹ * (‖halfBinomialWeightedCoeff p⁻¹ q⁻¹ m‖ + E) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hF (inv_nonneg.mpr hprod0))
    _ = _ := by dsimp only [E]; ring

end D1Bound5
end
