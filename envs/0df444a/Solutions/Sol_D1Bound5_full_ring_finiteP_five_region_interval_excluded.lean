-- Prove2me | solution 1 for D1Bound5.full_ring_finiteP_five_region_interval_excluded
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:52:16.504976+00:00
-- url     : https://prove2.me/submissions/28ab5913-9d35-44ab-9332-4286e9a5b599

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_CommonIntervalWindows_Definitions
import Definitions.Def_D1Bound5_CoupledPhaseBounds_Definitions
import Definitions.Def_D1Bound5_FinitePAdaptiveResidual_Definitions
import Definitions.Def_D1Bound5_FiveRegionParameters_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_finitePAdaptiveRate_pos
import Theorems.Thm_D1Bound5_fiveRegion_parameters
import Theorems.Thm_D1Bound5_full_ring_finiteP_adaptive_closed_interval_excluded
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The actual adaptive P window, weakened only to the exact printed
rational residual rate for the chosen first-pair region. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {S : Finset (𝓞 K)} (hS : IsD1 S) (a : Fin 3 → 𝓞 K) (c d : 𝓞 K)
    (haS : ∀ j, a j ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hinj : Function.Injective a) (hac : ∀ j, a j ≠ c)
    (had : ∀ j, a j ≠ d) (hcd : c ≠ d)
    (hmon : Monotone (fun j => ‖phi (a j : K)‖))
    (hCT : 200*‖phi (a 2 : K)‖ ≤ ‖phi (c : K)‖)
    (hCD : ‖phi (c : K)‖ ≤ ‖phi (d : K)‖)
    (hAC : 1000 ≤ ‖phi (a 0 : K)‖*‖phi (c : K)‖)
    (r : Fin 5) (hratio : fiveRegionQ r*‖phi (a 0 : K)‖ ≤ ‖phi (a 1 : K)‖)
    (hleft : (commonWindowP ‖phi (a 0 : K)‖ ‖phi (a 1 : K)‖ ‖phi (a 2 : K)‖
      ‖phi (c : K)‖ (fiveRegionPResidual r)).1 ≤ ‖phi (d : K)‖)
    (hright : ‖phi (d : K)‖ ≤
      (commonWindowP ‖phi (a 0 : K)‖ ‖phi (a 1 : K)‖ ‖phi (a 2 : K)‖
        ‖phi (c : K)‖ (fiveRegionPResidual r)).2) : False := by
  have hq : 1 ≤ fiveRegionQ r := (fiveRegion_parameters r).2.2.2.1
  have hq0 : 0 < fiveRegionQ r := by linarith only [hq]
  have hR : 0 < finitePAdaptiveRate (1/fiveRegionQ r) :=
    finitePAdaptiveRate_pos _ (by positivity)
  have hRbound : finitePAdaptiveRate (1/fiveRegionQ r) < fiveRegionPResidual r :=
    (fiveRegion_parameters r).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hS1 := one_le_norm_integer hK phi (hS.1 _ (haS 2))
  have hS0 : 0 < ‖phi (a 2 : K)‖ := by linarith only [hS1]
  apply full_ring_finiteP_adaptive_closed_interval_excluded hK phi hS a c d
    haS hcS hdS hinj hac had hcd hmon hCT hCD hAC (fiveRegionQ r) hq hratio hleft
  apply hright.trans
  change ‖phi (a 0 : K)‖^6*‖phi (c : K)‖^9/
      (4*(fiveRegionPResidual r)^2*‖phi (a 2 : K)‖^4*(1+1/4000 : ℝ)) ≤ _
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  gcongr

end D1Bound5
end
