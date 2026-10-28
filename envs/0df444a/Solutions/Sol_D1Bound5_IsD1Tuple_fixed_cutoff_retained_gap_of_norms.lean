-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.fixed_cutoff_retained_gap_of_norms
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:46:58.333447+00:00
-- url     : https://prove2.me/submissions/317c7b11-8b8e-46aa-81ca-a5f9ab55f620

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_Regular_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_retained_gap_of_frontier
import Theorems.Thm_D1Bound5_IsD1Tuple_retained_start_of_frontier
import Theorems.Thm_D1Bound5_IsD1Tuple_tail_irregular_and_growth
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_coherent_fixed_retained_coefficient_lower
import Theorems.Thm_D1Bound5_coherent_three_vandermonde_ratio_bounds
import Theorems.Thm_D1Bound5_oneSmallCutoffRows_valid
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5

/-- Field-independent retained cutoff interface using exact squared
moduli and distances. It includes rational triples in every quadratic
field; no coordinate-ring equivalence is needed. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (r : OneSmallCutoffRow) (hr : r ∈ oneSmallCutoffRows)
    (hAsq : ‖phi (a 0 : K)‖^2 = (r.a0 : ℝ))
    (hBsq : ‖phi (a 1 : K)‖^2 = (r.b0 : ℝ))
    (hSsq : ‖phi (a 2 : K)‖^2 = (r.s0 : ℝ))
    (hdab : ‖phi (a 0 : K)-phi (a 1 : K)‖^2 = (r.dab : ℝ))
    (hdas : ‖phi (a 0 : K)-phi (a 2 : K)‖^2 = (r.das : ℝ))
    (hdbs : ‖phi (a 1 : K)-phi (a 2 : K)‖^2 = (r.dbs : ℝ))
    (hlarge : (r.triple.cutoff : ℝ) ≤ ‖phi (a 3 : K)‖^2) :
    let A := ‖phi (a 0 : K)‖
    let B := ‖phi (a 1 : K)‖
    let S := ‖phi (a 2 : K)‖
    let T := ‖phi (a 3 : K)‖
    let C := ‖phi (a 4 : K)‖
    let D := ‖phi (a 5 : K)‖
    (r.retainedCoefficient : ℝ)*T^5/S^2 < C ∧
      A^2*C^5/S^2 < D ∧ A^2*C^7/(S^2*T^4) < D ∧
      1000 < C ∧ 200*S < C ∧ 4*T < C ∧ 16*B*S*T < C ∧ 1000*C < D := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let A := ‖f (a 0)‖
  let B := ‖f (a 1)‖
  let S := ‖f (a 2)‖
  let T := ‖f (a 3)‖
  let C := ‖f (a 4)‖
  let D := ‖f (a 5)‖
  let v : Fin 3 → ℂ := fun i => f (a (![0,1,2] i))
  let R := ‖coherentVandermonde3 v‖/(B*S^2)
  change A^2 = (r.a0 : ℝ) at hAsq
  change B^2 = (r.b0 : ℝ) at hBsq
  change S^2 = (r.s0 : ℝ) at hSsq
  change ‖f (a 0)-f (a 1)‖^2 = (r.dab : ℝ) at hdab
  change ‖f (a 0)-f (a 2)‖^2 = (r.das : ℝ) at hdas
  change ‖f (a 1)-f (a 2)‖^2 = (r.dbs : ℝ) at hdbs
  obtain ⟨hcut,hAN,hBN,hBSN,hq,hqle,hq1,hDelta,hphi,hphi6,hphi5,hsep,hcoef,hrest⟩ :=
    oneSmallCutoffRows_valid r hr
  have hA : 1 ≤ A := one_le_norm_integer hK phi (ha.2.1 0)
  have hA0 : 0 < A := by linarith only [hA]
  have hB : 3 ≤ B := by
    have hn : (9 : ℝ) ≤ (r.b0 : ℝ) := by exact_mod_cast hBN
    have hBn : 0 ≤ B := norm_nonneg _
    nlinarith only [hn,hBsq,hBn]
  have hB0 : 0 < B := by linarith only [hB]
  have hBS : B ≤ S := hmon (by decide : (1 : Fin 6) ≤ 2)
  have hS0 : 0 < S := hB0.trans_le hBS
  have hlarge' : (r.triple.cutoff : ℝ) ≤ T^2 := hlarge
  have hT32 : 32 ≤ T := by
    have hn : (1024 : ℝ) ≤ r.triple.cutoff := by exact_mod_cast hcut
    have hTn : 0 ≤ T := norm_nonneg _
    nlinarith only [hn,hlarge',hTn]
  have hAT : 32 ≤ A*T := by nlinarith only [hA,hT32]
  let b : Fin 4 → 𝓞 K := fun i => a (Fin.castAdd 2 i)
  have hcast : Function.Injective (Fin.castAdd 2 : Fin 4 → Fin 6) := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin 6 => k.val) hij
  have hb : IsD1Tuple b := by
    refine ⟨ha.1.comp hcast,?_,?_⟩
    · intro i
      exact ha.2.1 (Fin.castAdd 2 i)
    · intro i j hij
      exact ha.2.2 (Fin.castAdd 2 i) (Fin.castAdd 2 j) (hcast.ne hij)
  have hbmon : Monotone (fun i => ‖phi (b i : K)‖) := by
    intro i j hij
    exact hmon hij
  have hfront : 2*A*B*S < T := by
    rcases hAN with hN | ⟨hN,hcut2⟩
    · have hn : (r.a0 : ℝ) = 1 := by exact_mod_cast hN
      have hAe : A=1 := by nlinarith only [hAsq,hA,hn]
      have ht := (IsD1Tuple.tail_irregular_and_growth hK phi b hb hbmon hB).2
      change 2*B*S < T at ht
      simpa only [hAe,mul_one] using ht
    · have hn : 4*(r.a0 : ℝ)*(r.b0 : ℝ)*(r.s0 : ℝ) < r.triple.cutoff := by
        exact_mod_cast hcut2
      have hs : (2*A*B*S)^2 < T^2 := by
        rw [←hAsq,←hBsq,←hSsq] at hn
        nlinarith only [hn,hlarge']
      exact (sq_lt_sq₀ (by positivity) (norm_nonneg _)).mp hs
  have hstart := IsD1Tuple.retained_start_of_frontier hK phi a ha hmon hB hfront hAT
  let c : Fin 5 → 𝓞 K := fun i => a (Fin.castAdd 1 i)
  have hcast5 : Function.Injective (Fin.castAdd 1 : Fin 5 → Fin 6) := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin 6 => k.val) hij
  have hc : IsD1Tuple c := by
    refine ⟨ha.1.comp hcast5,?_,?_⟩
    · intro i
      exact ha.2.1 (Fin.castAdd 1 i)
    · intro i j hij
      exact ha.2.2 (Fin.castAdd 1 i) (Fin.castAdd 1 j) (hcast5.ne hij)
  have hcmon : Monotone (fun i => ‖phi (c i : K)‖) := by
    intro i j hij
    exact hmon hij
  have hg := (IsD1Tuple.retained_gap_of_frontier hK phi c hc hcmon hB hfront
    32 (1/10) (179/10) (Or.inl ⟨rfl,rfl,rfl⟩) hAT).1
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hv : Function.Injective v :=
    hf.comp (ha.1.comp (by decide : Function.Injective (![0,1,2] : Fin 3 → Fin 6)))
  have hAB : A ≤ B := hmon (by decide : (0 : Fin 6) ≤ 1)
  have hR : 0 < R := (coherent_three_vandermonde_ratio_bounds v hv hA0 hAB hBS).1
  have hRsq : R^2 = ((r.dab*r.das*r.dbs/(r.b0*r.s0^2) : ℚ) : ℝ) := by
    change (‖coherentVandermonde3 v‖/(B*S^2))^2 = _
    simp only [coherentVandermonde3,norm_mul]
    change ((‖f (a 0)-f (a 1)‖*‖f (a 0)-f (a 2)‖*
      ‖f (a 1)-f (a 2)‖)/(B*S^2))^2 = _
    rw [div_pow,mul_pow,mul_pow,mul_pow,hdab,hdas,hdbs,hBsq,hSsq]
    push_cast <;> rfl
  have hq1real : 0 < (r.q1 : ℝ) := by exact_mod_cast hq1
  have hRle : R ≤ (r.q1 : ℝ) := by
    apply (sq_le_sq₀ hR.le hq1real.le).mp
    rw [hRsq]
    exact_mod_cast hDelta
  have hsepreal : (51051/400000 : ℝ)/B^2 < 1/(r.q1 : ℝ) := by
    rw [hBsq]
    have hs := (Rat.cast_lt (K := ℝ)).2 hsep
    push_cast at hs
    exact hs
  have hlower := coherent_fixed_retained_coefficient_lower A B R (r.q1 : ℝ)
    hA hB0 hR hRle hsepreal
  have hcoefeq : (r.retainedCoefficient : ℝ) =
      (9999/100 : ℝ)*A^2*(1/(r.q1 : ℝ)-(51051/400000 : ℝ)/B^2)^2 := by
    simp only [OneSmallCutoffRow.retainedCoefficient]
    push_cast
    rw [hAsq,hBsq]
  have hfinal : (r.retainedCoefficient : ℝ)*T^5/S^2 < C := by
    calc
      _ = (r.retainedCoefficient : ℝ)*(T^5/S^2) := by ring
      _ ≤ ((9999/100 : ℝ)*A^2*
          (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2)*(T^5/S^2) := by
        rw [hcoefeq]
        exact mul_le_mul_of_nonneg_right hlower (by positivity)
      _ < C := by
        have hcv : (fun i : Fin 3 => phi (c (![0,1,2] i) : K)) = v := by
          funext i
          fin_cases i <;> rfl
        rw [hcv] at hg
        change (9999/10000 : ℝ)/(1/10)^2*
          (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2*
          (A^2*T^5/S^2) < C at hg
        calc
          _ = (9999/100 : ℝ)*(1/R-(51051/400000 : ℝ)/(A^2*B^2))^2*
              (A^2*T^5/S^2) := by ring
          _ < C := by
            simpa only [show (9999/10000 : ℝ)/(1/10)^2 = 9999/100 by norm_num] using hg
  exact ⟨hfinal,hstart.2⟩





end D1Bound5
end
