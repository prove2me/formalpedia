-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.rational_first_pair_third_lt_fifteen
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:36:33.735293+00:00
-- url     : https://prove2.me/submissions/cbf4cef6-87e4-4d26-9f91-a80dccd006e9

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
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
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.SchurComplement
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_AllLargeWindows_Definitions
import Definitions.Def_D1Bound5_CommonIntervalWindows_Definitions
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FinitePAdaptiveResidual_Definitions
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_001
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_002
import Definitions.Def_D1Bound5_FirstPairGeometryFixedRows_Definitions
import Definitions.Def_D1Bound5_FirstPairGeometry_Definitions
import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_OrdinaryClosedIntervals_Definitions
import Theorems.Thm_D1Bound5_FirstPairGeometryMatches_residual_rates
import Theorems.Thm_D1Bound5_IsD1Tuple_finiteQ_upper_of_lower
import Theorems.Thm_D1Bound5_IsD1Tuple_first_pair_retained_packet_of_norms
import Theorems.Thm_D1Bound5_IsD1Tuple_ordinary_closed_interval_excluded
import Theorems.Thm_D1Bound5_IsD1Tuple_ordinary_tail_incompatible
import Theorems.Thm_D1Bound5_common_interval_window_overlaps
import Theorems.Thm_D1Bound5_firstPairGeometryRows_valid
import Theorems.Thm_D1Bound5_firstPairGeometry_common_overlap_bounds
import Theorems.Thm_D1Bound5_full_ring_finiteA3_rational_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteA4_rational_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteA5_rational_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteM_closed_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteN2_rational_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteN3Ab_rational_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteN3_phi_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteP_adaptive_closed_interval_excluded
import Theorems.Thm_D1Bound5_one_le_norm_integer
import Theorems.Thm_D1Bound5_rationalCutoff_pair_geometry
import Theorems.Thm_D1Bound5_window_upper_lt_of_excluded

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- The universal signed rational first pair also has S<15. Its actual
polynomial coefficients are evaluated under integer ring maps, so no
coordinate equivalence is required for the ambient imaginary field. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (sgn : Bool) (hx : a 0 = if sgn then -1 else 1)
    (hy : a 1 = if sgn then -3 else 3) :
    ‖phi (a 2 : K)‖ < 15 := by
  classical
  by_contra hn
  have hS15 := le_of_not_gt hn
  let g : FirstPairGeometryRow := firstPairGeometryRow_40
  let r : OneSmallCutoffRow := oneSmallCutoffRow_56
  have hg : g ∈ firstPairGeometryRows := by decide +kernel
  have hr : r ∈ oneSmallCutoffRows := by decide +kernel
  have hmatch : FirstPairGeometryMatches g r := by decide +kernel
  let A := ‖phi (a 0 : K)‖
  let B := ‖phi (a 1 : K)‖
  let S := ‖phi (a 2 : K)‖
  let T := ‖phi (a 3 : K)‖
  let C := ‖phi (a 4 : K)‖
  let D := ‖phi (a 5 : K)‖
  let Rbs : ℝ := (3535/409600)*firstPairPhi (phi (a 1 : K)) (phi (a 2 : K))
  have hAB : A ≤ B := hmon (by decide : (0 : Fin 6) ≤ 1)
  have hBS : B ≤ S := hmon (by decide : (1 : Fin 6) ≤ 2)
  have hST : S ≤ T := hmon (by decide : (2 : Fin 6) ≤ 3)
  have hCD : C ≤ D := hmon (by decide : (4 : Fin 6) ≤ 5)
  have hA1 : 1 ≤ A := one_le_norm_integer hK phi (ha.2.1 0)
  have hA : 0 < A := by linarith only [hA1]
  have hB : 0 < B := hA.trans_le hAB
  have hS : 0 < S := hB.trans_le hBS
  have hT : 0 < T := hS.trans_le hST
  have hv := firstPairGeometryRows_valid g hg
  obtain ⟨hAn,hBn,hdn⟩ := rationalCutoff_pair_geometry phi sgn (a 0) (a 1) hx hy
  have hAsq : ‖phi (a 0 : K)‖^2 = (g.a0 : ℝ) := by
    rw [hAn,show g.a0 = (1 : ℚ) by decide +kernel]
    norm_num
  have hBsq : ‖phi (a 1 : K)‖^2 = (g.b0 : ℝ) := by
    rw [hBn,show g.b0 = (9 : ℚ) by decide +kernel]
    norm_num
  have hdsq : ‖phi (a 0 : K)-phi (a 1 : K)‖^2 = (g.dab : ℝ) := by
    rw [hdn,show g.dab = (4 : ℚ) by decide +kernel]
    norm_num
  have hret := IsD1Tuple.first_pair_retained_packet_of_norms hK phi a ha hmon
    g hv hAsq hBsq hdsq hS15
  change (7/4 : ℝ)*T^5/S^2<C ∧ (g.G : ℝ)*B^5*S^3<C ∧
    (g.rho : ℝ)*Rbs*B^5*S^3<C ∧ C^7/(S^2*T^4)<D ∧
    1000<C ∧ 200*S<C ∧ 4*T<C ∧ 2*B*S<T at hret
  obtain ⟨hgap0,hgap,hgapbs,hstart,hC1000,hC200S,hC4T,hfront⟩ := hret
  have hC : 0 < C := by linarith only [hC1000]
  have hC200B : 200*B ≤ C := (by gcongr : 200*B ≤ 200*S).trans hC200S.le
  have hC4S : 4*S ≤ C := (by gcongr : 4*S ≤ 4*T).trans hC4T.le
  have hC4B : 4*B < C := by linarith only [hC200B,hB]
  have hAC : 1000 ≤ A*C := by
    have hh := mul_le_mul_of_nonneg_right hA1 hC.le
    linarith only [hh,hC1000]
  obtain ⟨haN,hbN,hdN,hA1p,hA1sq,hB0p,hB0sq,hB1p,hB1sq,hd1p,hd1sq,hq,hQ,hm,hK0,
    hG,hH,hF,hrho,hR2,hRn,hR3,hR4,hR5,hRp,hM2,hMn,hM3,hM4,hM5,hqs,htail⟩ := hv
  have hpG : (0 : ℝ) < (g.G : ℝ) := by exact_mod_cast hG
  have hprho : (0 : ℝ) < (g.rho : ℝ) := by exact_mod_cast hrho
  have hpR2 : (0 : ℝ) < (g.R2 : ℝ) := by exact_mod_cast hR2
  have hpRn : (0 : ℝ) < (g.Rn : ℝ) := by exact_mod_cast hRn
  have hpR3 : (0 : ℝ) < (g.R3 : ℝ) := by exact_mod_cast hR3
  have hpR4 : (0 : ℝ) < (g.R4 : ℝ) := by exact_mod_cast hR4
  have hpR5 : (0 : ℝ) < (g.R5 : ℝ) := by exact_mod_cast hR5
  have hpRp : (0 : ℝ) < (g.Rp : ℝ) := by exact_mod_cast hRp
  have hpM2 : (0 : ℝ) < (g.M2 : ℝ) := by exact_mod_cast hM2
  have hpMn : (0 : ℝ) < (g.Mn : ℝ) := by exact_mod_cast hMn
  have hpM3 : (0 : ℝ) < (g.M3 : ℝ) := by exact_mod_cast hM3
  have hpM4 : (0 : ℝ) < (g.M4 : ℝ) := by exact_mod_cast hM4
  have hpM5 : (0 : ℝ) < (g.M5 : ℝ) := by exact_mod_cast hM5
  have hpB0 : (0 : ℝ) < (g.B0 : ℝ) := by exact_mod_cast hB0p
  have hpA1 : (0 : ℝ) < (g.A1 : ℝ) := by exact_mod_cast hA1p
  have hsep : phi (a 1 : K)-phi (a 2 : K) ≠ 0 := by
    intro hh
    have he := phi.injective (sub_eq_zero.mp hh)
    exact (ha.1.ne (by decide : (1 : Fin 6) ≠ 2)) (Subtype.ext he)
  have hRbs : 0 < Rbs := by
    have hh : 0 < (‖phi (a 1 : K)-phi (a 2 : K)‖/S)^6 :=
      pow_pos (div_pos (norm_pos_iff.mpr hsep) hS) 6
    have hp : 0 < firstPairPhi (phi (a 1 : K)) (phi (a 2 : K)) :=
      hh.trans_le (le_max_left _ _)
    dsimp [Rbs]
    positivity
  have hnum := firstPairGeometry_common_overlap_bounds g (firstPairGeometryRows_valid g hg) B S hB hBsq hS15
  obtain ⟨hoStart,hoQN2,hoN2P,hoPN3,hoPA3,hoA3M,hoMN3,hoN3A4,hoN3bs,
    hoBsA4,hoA4O4,hoO4A5,hoA5O5,hoO5O6,hoRate⟩ :=
    common_interval_window_overlaps 1 B S T C g.G g.rho (7/4)
      g.M2 g.Mn g.M3 g.M4 g.M5 4143 g.R2 g.Rn g.R3 g.R4 g.R5 Rbs g.Rp
      (by norm_num) hB hS hBS hpG hprho (by norm_num)
      hpM2 hpMn hpM3 hpM4 hpM5 (by norm_num)
      hpR2 hpRn hpR3 hpR4 hpR5 hRbs hpRp hfront
      (by simpa only [one_pow,mul_one] using hgap0)
      (by simpa only [one_pow,one_mul,mul_assoc] using hgap)
      (by simpa only [one_pow,one_mul,mul_assoc] using hgapbs) hnum
  obtain ⟨hR2eq,hRneq,hR3eq,hR4eq,hR5eq⟩ :=
    FirstPairGeometryMatches.residual_rates g r hmatch
  obtain ⟨_,_,_,_,hM2eq,hMneq,hM3eq,hM4eq,hM5eq⟩ := hmatch
  let Tup : Finset (𝓞 K) := Finset.univ.image a
  have hmem (i : Fin 6) : a i ∈ Tup := Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  have hTup : IsD1 Tup := by
    constructor
    · intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact ha.2.1 i
    · intro x hx y hy hxy
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
      exact ha.2.2 i j (fun hij => hxy (congrArg a hij))
  have hN2 : ¬ ((commonWindowN2 1 B C g.M2 g.R2).1 ≤ D ∧
      D ≤ (commonWindowN2 1 B C g.M2 g.R2).2) := by
    rintro ⟨hl,hu⟩
    simp only [commonWindowN2,one_pow,one_mul,hM2eq,hR2eq] at hl hu
    exact full_ring_finiteN2_rational_interval_excluded hK phi hTup (a 0) (a 1) (a 4) (a 5)
      (hmem 0) (hmem 1) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hC1000.le hC200B hCD sgn hx hy hl hu
  have hN3 : ¬ ((commonWindowN3 1 B C g.Mn g.Rn).1 ≤ D ∧
      D ≤ (commonWindowN3 1 B C g.Mn g.Rn).2) := by
    rintro ⟨hl,hu⟩
    simp only [commonWindowN3,one_pow,one_mul,hMneq,hRneq] at hl hu
    exact full_ring_finiteN3Ab_rational_interval_excluded hK phi hTup (a 0) (a 1) (a 4) (a 5)
      (hmem 0) (hmem 1) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hC1000.le hC200B hCD sgn hx hy hl hu
  have hA3 : ¬ ((commonWindowA3 1 B C g.M3 g.R3).1 ≤ D ∧
      D ≤ (commonWindowA3 1 B C g.M3 g.R3).2) := by
    rintro ⟨hl,hu⟩
    simp only [commonWindowA3,one_pow,one_mul,hM3eq,hR3eq] at hl hu
    exact full_ring_finiteA3_rational_interval_excluded hK phi hTup (a 0) (a 1) (a 4) (a 5)
      (hmem 0) (hmem 1) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hC1000.le hC200B hCD sgn hx hy hl hu
  have hA4 : ¬ ((commonWindowA4 1 B C g.M4 g.R4).1 ≤ D ∧
      D ≤ (commonWindowA4 1 B C g.M4 g.R4).2) := by
    rintro ⟨hl,hu⟩
    simp only [commonWindowA4,one_pow,one_mul,hM4eq,hR4eq] at hl hu
    exact full_ring_finiteA4_rational_interval_excluded hK phi hTup (a 0) (a 1) (a 4) (a 5)
      (hmem 0) (hmem 1) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hC1000.le hC200B hCD sgn hx hy hl hu
  have hA5 : ¬ ((commonWindowA5 1 B C g.M5 g.R5).1 ≤ D ∧
      D ≤ (commonWindowA5 1 B C g.M5 g.R5).2) := by
    rintro ⟨hl,hu⟩
    simp only [commonWindowA5,one_pow,one_mul,hM5eq,hR5eq] at hl hu
    exact full_ring_finiteA5_rational_interval_excluded hK phi hTup (a 0) (a 1) (a 4) (a 5)
      (hmem 0) (hmem 1) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hC1000.le hC200B hCD sgn hx hy hl hu
  have hN3bs : ¬ ((commonWindowN3 B S C 4143 Rbs).1 ≤ D ∧
      D ≤ (commonWindowN3 B S C 4143 Rbs).2) := by
    rintro ⟨hl,hu⟩
    exact full_ring_finiteN3_phi_interval_excluded hK phi hTup (a 1) (a 2) (a 4) (a 5)
      (hmem 1) (hmem 2) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hBS hC1000.le hC200S.le hCD hl hu
  let i3 : Fin 3 → Fin 6 := ![0,1,2]
  let b3 : Fin 3 → 𝓞 K := fun i => a (i3 i)
  have hi3 : Function.Injective i3 := by decide
  have hb3 : Function.Injective b3 := ha.1.comp hi3
  have hm3 : Monotone i3 := by decide
  have hM : ¬ ((allLargeWindowM 1 B S C).1 ≤ D ∧ D ≤ (allLargeWindowM 1 B S C).2) := by
    rintro ⟨hl,hu⟩
    have hu' : D ≤ A^6*C^11/(4*(3920/81 : ℝ)^2*B^4*S^10*(1+1/4000 : ℝ)) := by
      apply hu.trans
      simp only [allLargeWindowM,one_pow,one_mul]
      gcongr
      have hA6 : (1 : ℝ) ≤ A^6 := one_le_pow₀ hA1
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hA6 (pow_nonneg hC.le 11)
    exact full_ring_finiteM_closed_interval_excluded hK phi hTup b3 (a 4) (a 5)
      (fun j => hmem (i3 j)) (hmem 4) (hmem 5) hb3
      (fun j => ha.1.ne (by fin_cases j <;> decide))
      (fun j => ha.1.ne (by fin_cases j <;> decide))
      (ha.1.ne (by decide : (4 : Fin 6) ≠ 5)) (hmon.comp hm3) hC4S hCD hAC hl hu'
  have hq1 : 1 ≤ (g.q : ℝ) := by exact_mod_cast (show (1 : ℚ) ≤ g.q by linarith only [hq])
  have hqAB : (g.q : ℝ)*A ≤ B := by
    have hAA : A ≤ (g.A1 : ℝ) := by
      have hh : A^2 ≤ (g.A1 : ℝ)^2 := by rw [hAsq]; exact_mod_cast hA1sq
      nlinarith only [hh,hA,hpA1]
    have hBB : (g.B0 : ℝ) ≤ B := by
      have hh : (g.B0 : ℝ)^2 ≤ B^2 := by rw [hBsq]; exact_mod_cast hB0sq
      nlinarith only [hh,hB,hpB0]
    calc
      (g.q : ℝ)*A ≤ (g.q : ℝ)*(g.A1 : ℝ) := by gcongr
      _ = (g.B0 : ℝ) := by
        simp only [FirstPairGeometryRow.q]
        push_cast
        field_simp [hpA1.ne']
      _ ≤ B := hBB
  have hRpEq : finitePAdaptiveRate (1/(g.q : ℝ)) = (g.Rp : ℝ) := by
    simp only [finitePAdaptiveRate,FirstPairGeometryRow.Rp]
    push_cast
    <;> ring
  have hP : ¬ ((commonWindowP 1 B S C g.Rp).1 ≤ D ∧ D ≤ (commonWindowP 1 B S C g.Rp).2) := by
    rintro ⟨hl,hu⟩
    have hu' : D ≤ A^6*C^9/(4*(finitePAdaptiveRate (1/(g.q : ℝ)))^2*S^4*(1+1/4000 : ℝ)) := by
      rw [hRpEq]
      apply hu.trans
      simp only [commonWindowP,one_pow,one_mul]
      gcongr
      have hA6 : (1 : ℝ) ≤ A^6 := one_le_pow₀ hA1
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hA6 (pow_nonneg hC.le 9)
    exact full_ring_finiteP_adaptive_closed_interval_excluded hK phi hTup b3 (a 4) (a 5)
      (fun j => hmem (i3 j)) (hmem 4) (hmem 5) hb3
      (fun j => ha.1.ne (by fin_cases j <;> decide))
      (fun j => ha.1.ne (by fin_cases j <;> decide))
      (ha.1.ne (by decide : (4 : Fin 6) ≠ 5)) (hmon.comp hm3) hC200S.le hCD hAC
      (g.q : ℝ) hq1 hqAB hl hu'
  let iAB : Fin 4 → Fin 6 := ![0,1,4,5]
  let tAB : Fin 4 → 𝓞 K := fun i => a (iAB i)
  have hiAB : Function.Injective iAB := by decide
  have htAB : IsD1Tuple tAB :=
    ⟨ha.1.comp hiAB,fun j => ha.2.1 _,fun j k hjk => ha.2.2 _ _ (hiAB.ne hjk)⟩
  have hOU (k : ℕ) : ordinaryWindowUpper 1 B C k ≤ ordinaryWindowUpper A B C k := by
    unfold ordinaryWindowUpper
    gcongr
  have hQupper : (allLargeWindowQ 1 T C).2 < D := by
    have hlo : (allLargeWindowQ 1 T C).1 ≤ D := by
      apply le_of_lt
      apply hoStart.trans
      simpa only [one_pow,one_mul] using hstart
    have hh := IsD1Tuple.finiteQ_upper_of_lower hK phi a ha hmon hC1000.le hC4T.le hlo
    simpa only [allLargeWindowQ,one_pow,one_mul] using hh
  have hN2upper := window_upper_lt_of_excluded _ D hN2 (hoQN2.trans hQupper).le
  have hPupper := window_upper_lt_of_excluded _ D hP (hoN2P.trans hN2upper).le
  have hN3upper : (commonWindowN3 1 B C g.Mn g.Rn).2 < D := by
    rcases le_total (B^2) S with h | h
    · exact window_upper_lt_of_excluded _ D hN3 ((hoPN3 h).trans hPupper).le
    · have hA3upper := window_upper_lt_of_excluded _ D hA3 (hoPA3.trans hPupper).le
      have hMupper := window_upper_lt_of_excluded _ D hM ((hoA3M h).trans hA3upper).le
      exact window_upper_lt_of_excluded _ D hN3 (hoMN3.trans hMupper).le
  have hA4upper : (commonWindowA4 1 B C g.M4 g.R4).2 < D := by
    rcases le_total (B^3) S with h | h
    · exact window_upper_lt_of_excluded _ D hA4 ((hoN3A4 h).trans hN3upper).le
    · have hBsupper := window_upper_lt_of_excluded _ D hN3bs ((hoN3bs h).trans hN3upper).le
      exact window_upper_lt_of_excluded _ D hA4 (hoBsA4.trans hBsupper).le
  have hO4lower : ordinaryWindowLower B C 4 ≤ D := (hoA4O4.trans hA4upper).le
  have hO4upper : ordinaryWindowUpper 1 B C 4 < D := by
    apply lt_of_not_ge
    intro h
    exact IsD1Tuple.ordinary_closed_interval_excluded hK phi tAB htAB hAB hAC hC4B hCD
      4 (by norm_num) hO4lower (h.trans (hOU 4))
  have hA5upper := window_upper_lt_of_excluded _ D hA5 (hoO4A5.trans hO4upper).le
  have hO5lower : ordinaryWindowLower B C 5 ≤ D := (hoA5O5.trans hA5upper).le
  have hrate : 42*B^3*C < 2*A*C^2/(5*B) := by
    apply hoRate.trans_le
    gcongr
  exact IsD1Tuple.ordinary_tail_incompatible hK phi tAB htAB hAB hAC hC4B hCD
    hrate (hoO5O6.le.trans (hOU 5)) hO5lower

end D1Bound5
end
