-- Prove2me | solution 1 for D1Bound5.full_ring_coherent_two_strong_gap_main
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:51:51.73754+00:00
-- url     : https://prove2.me/submissions/a74d48f2-49ef-4891-b06f-52e7965c57ce

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
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_coherent_cpow_half_sq
import Theorems.Thm_D1Bound5_coherent_two_main_size_parameters
import Theorems.Thm_D1Bound5_full_ring_coherent_two_strong_gap
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5



/-- A branch-witness-free strong gap for actual tuple entries in the
two main size regimes.  All analytic size premises and the auxiliary
square root are supplied internally. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {T : Finset (𝓞 K)} (hT : IsD1 T) {a b p q : 𝓞 K}
    (ha : a ∈ T) (hb : b ∈ T) (hp : p ∈ T) (hq : q ∈ T)
    (hab : a ≠ b) (hap : a ≠ p) (haq : a ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q) (hpq : p ≠ q)
    (hAB : ‖phi (a : K)‖ ≤ ‖phi (b : K)‖)
    (hB : 3 ≤ ‖phi (b : K)‖) (hP : 5 * ‖phi (b : K)‖ ≤ ‖phi (p : K)‖)
    (hQ : 5 * ‖phi (a : K)‖ * ‖phi (b : K)‖ * ‖phi (p : K)‖ ≤ ‖phi (q : K)‖)
    (hlarge : 3 ≤ ‖phi (a : K)‖ ∨ 48 ≤ ‖phi (p : K)‖) :
    ‖phi (a : K)‖ ^ 2 * ‖phi (p : K)‖ ^ 3 <
      (10001 / 10000 : ℝ) * ‖phi (q : K)‖ := by
  have hA := one_le_norm_integer hK phi (hT.1 a ha)
  have hparams := coherent_two_main_size_parameters ‖phi (a : K)‖ ‖phi (b : K)‖
    ‖phi (p : K)‖ ‖phi (q : K)‖ hA hAB hB hP hQ hlarge
  let eta : ℂ := (phi (p : K) * phi (q : K)) ^ (1 / 2 : ℂ)
  have heta : eta ^ 2 = phi (p : K) * phi (q : K) :=
    coherent_cpow_half_sq _
  exact full_ring_coherent_two_strong_gap hK phi hT
    ha hb hp hq hab hap haq hbp hbq hpq eta heta
    hAB hB hP hparams.1 hQ hparams.2

end D1Bound5
end
