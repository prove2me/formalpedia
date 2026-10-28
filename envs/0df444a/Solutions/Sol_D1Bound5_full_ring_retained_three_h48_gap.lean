-- Prove2me | solution 1 for D1Bound5.full_ring_retained_three_h48_gap
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:36:15.04362+00:00
-- url     : https://prove2.me/submissions/5667128c-ee0f-4b77-b5e2-49d3923753e8

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
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_coherent_cpow_half_sq
import Theorems.Thm_D1Bound5_coherent_retained_h48_size_parameters
import Theorems.Thm_D1Bound5_coherent_terminal_root_norm_sq_bounds
import Theorems.Thm_D1Bound5_coherent_three_vandermonde_ratio_bounds
import Theorems.Thm_D1Bound5_full_ring_coherent_two_strong_gap_main
import Theorems.Thm_D1Bound5_full_ring_retained_three_h48_lower_upper
import Theorems.Thm_D1Bound5_retained_three_h48_scalar_gap

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5

/-- The retained H48 gap for actual five tuple entries in the
no-small-entry branch.  The analytic forms, nonvanishing, integrality,
terminal norm bounds and normalized Vandermonde bounds are all derived;
no root witness or retained-gap inequality is assumed. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {Tup : Finset (𝓞 K)} (hTup : IsD1 Tup)
    (a : Fin 5 → 𝓞 K) (hinj : Function.Injective a) (hmem : ∀ i, a i ∈ Tup)
    (hA : 3 ≤ ‖phi (a 0 : K)‖)
    (hAB : ‖phi (a 0 : K)‖ ≤ ‖phi (a 1 : K)‖)
    (hBS : ‖phi (a 1 : K)‖ ≤ ‖phi (a 2 : K)‖)
    (hfrontier : 2*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖ < ‖phi (a 3 : K)‖)
    (hproduct : 3*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖ < ‖phi (a 4 : K)‖) :
    let v : Fin 3 → ℂ := fun i => phi (a (![0,1,2] i) : K)
    let R := ‖coherentVandermonde3 v‖/(‖phi (a 1 : K)‖*‖phi (a 2 : K)‖^2)
    ((9999/10000 : ℝ)*(200/19)^2) *
      (1/R-(51051/400000 : ℝ)/(‖phi (a 0 : K)‖^2*‖phi (a 1 : K)‖^2))^2 *
        (‖phi (a 0 : K)‖^2*‖phi (a 3 : K)‖^5/‖phi (a 2 : K)‖^2) < ‖phi (a 4 : K)‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let v : Fin 3 → ℂ := fun i => f (a (![0,1,2] i))
  let A := ‖f (a 0)‖
  let B := ‖f (a 1)‖
  let S := ‖f (a 2)‖
  let P := ‖f (a 3)‖
  let C := ‖f (a 4)‖
  let eta : ℂ := (f (a 3)*f (a 4))^(1/2 : ℂ)
  let Z := ‖coherentTerminalRoot (f (a 3)) (f (a 4)) eta‖
  let L := coherentQuotientForm v (coherentVandermonde3 v) (f (a 3)) (f (a 4)) eta
  let R := ‖coherentVandermonde3 v‖/(B*S^2)
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hv : Function.Injective v :=
    hf.comp (hinj.comp (by decide : Function.Injective (![0,1,2] : Fin 3 → Fin 5)))
  have hA0 : 0 < A := by change 0<‖phi (a 0 : K)‖; linarith only [hA]
  have hB3 : 3 ≤ B := hA.trans hAB
  have hS3 : 3 ≤ S := hB3.trans hBS
  have hB0 : 0 < B := by linarith
  have hS0 : 0 < S := by linarith
  have hparams := coherent_retained_h48_size_parameters A B S P C hA hAB hBS hfrontier hproduct
  have hP0 : 0 < P := by nlinarith only [hparams.1,hS3]
  have hC0 : 0 < C := by nlinarith only [hparams.2.2.2.1,hP0]
  have hSP : S ≤ P := by nlinarith only [hparams.1,hS0]
  have heta : eta^2 = f (a 3)*f (a 4) := coherent_cpow_half_sq _
  have hactual := full_ring_retained_three_h48_lower_upper hK phi hTup a hinj hmem
    hA hAB hBS hfrontier hproduct eta heta
  have hgap := full_ring_coherent_two_strong_gap_main hK phi hTup
    (hmem 1) (hmem 2) (hmem 3) (hmem 4)
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
    hBS hS3 hparams.1 hparams.2.1 (Or.inl hB3)
  have hratio := coherent_three_vandermonde_ratio_bounds v hv hA0 hAB hBS
  have hroots := coherent_terminal_root_norm_sq_bounds (f (a 3)) (f (a 4)) eta
    (norm_pos_iff.mp hP0) (norm_pos_iff.mp hC0) heta
    (by linarith only [hparams.2.2.2.2.1])
  have hZ : 0 < Z := by
    have hz0 : 0 ≤ Z := norm_nonneg _
    have hpos : 0 < (3999/4000 : ℝ)*P*C := by positivity
    nlinarith only [hz0,hpos,hroots.1]
  have hdelta : R*B*S^2 = ‖coherentVandermonde3 v‖ := by
    dsimp [R]
    field_simp
  have hupper : ‖L‖ < 51*(R*B*S^2)/(100*Z) +
      (19/200 : ℝ)*(R*B*S^2)*Z/(A*B*S*P^3) := by
    rw [hdelta]
    exact hactual.2.2
  exact retained_three_h48_scalar_gap A B S P C Z R ‖L‖
    hA hB3 hS3 hSP hZ hratio.1 hratio.2 hfrontier hgap
    hroots.1 hroots.2 hactual.2.1 hupper



end D1Bound5
end
