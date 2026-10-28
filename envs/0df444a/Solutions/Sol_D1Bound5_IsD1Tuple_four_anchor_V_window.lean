-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.four_anchor_V_window
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:06:46.112985+00:00
-- url     : https://prove2.me/submissions/01ed05a3-0535-4a43-b644-2b6e1051a2e5

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
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_coherent_analytic_terminal_root_sq
import Theorems.Thm_D1Bound5_coherent_cpow_half_sq
import Theorems.Thm_D1Bound5_finite_tuple_root_relative_norm
import Theorems.Thm_D1Bound5_four_anchor_V_window_scalar
import Theorems.Thm_D1Bound5_full_ring_four_anchor_three_separated_inequality
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5



/-- The V-window exclusion for an actual ordered D(1) sextuple.
Nonvanishing, integrality, root signs and root-size estimates are all
derived inside the theorem. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hP : 1000 ≤ ‖phi (a 4 : K)‖)
    (hTP : 4*‖phi (a 3 : K)‖ ≤ ‖phi (a 4 : K)‖)
    (hQ : 4*‖phi (a 4 : K)‖ ≤ ‖phi (a 5 : K)‖)
    (hsize : 32*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖/
      ‖phi (a 0 : K)‖^3 ≤ ‖phi (a 4 : K)‖^2) :
    ‖phi (a 5 : K)‖ < 101*‖phi (a 1 : K)‖^2*‖phi (a 3 : K)‖^4/
        ‖phi (a 4 : K)‖ ∨
      (2/5 : ℝ)*‖phi (a 0 : K)‖^2*‖phi (a 4 : K)‖^5/
        ‖phi (a 3 : K)‖^2 < ‖phi (a 5 : K)‖ := by
  classical
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let Tup : Finset (𝓞 K) := Finset.univ.image a
  have hmem (i : Fin 6) : a i ∈ Tup :=
    Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  have hTup : IsD1 Tup := by
    constructor
    · intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact ha.2.1 i
    · intro x hx y hy hxy
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
      exact ha.2.2 i j (fun hij => hxy (congrArg a hij))
  let b : Fin 4 → 𝓞 K := fun i => a (![0,1,2,3] i)
  have hb : Function.Injective b :=
    ha.1.comp (by decide : Function.Injective (![0,1,2,3] : Fin 4 → Fin 6))
  have hbmon : Monotone (fun i => ‖f (b i)‖) := by
    have hidx : Monotone (![0,1,2,3] : Fin 4 → Fin 6) := by decide
    exact fun i j hij => hmon (hidx hij)
  let p := f (a 4)
  let q := f (a 5)
  change 1000 ≤ ‖p‖ at hP
  change 4*‖p‖ ≤ ‖q‖ at hQ
  let eta : ℂ := (p*q)^(1/2 : ℂ)
  have heta : eta^2 = p*q := coherent_cpow_half_sq (p*q)
  have hp : 0 < ‖p‖ := (by norm_num : (0 : ℝ) < 1000).trans_le hP
  have hq : 0 < ‖q‖ := hp.trans_le (hmon (by decide : (4 : Fin 6) ≤ 5))
  have hpq : 4000 ≤ ‖p‖*‖q‖ := by
    have hh := mul_le_mul_of_nonneg_left hQ hp.le
    nlinarith only [hP,hh,sq_nonneg (‖p‖-1000)]
  have hform := full_ring_four_anchor_three_separated_inequality hK phi hTup
    (hmem 4) (hmem 5) (ha.1.ne (by decide)) b hb (fun i => hmem _)
    (by intro i; exact ha.1.ne (by fin_cases i <;> decide))
    (by intro i; exact ha.1.ne (by fin_cases i <;> decide))
    hbmon hP hTP hQ hsize eta heta
  let z := coherentTerminalRoot p q eta
  have hz : z^2 = p*q+1 := coherent_analytic_terminal_root_sq p q eta
    (norm_pos_iff.mp hp) (norm_pos_iff.mp hq) heta
  have hrel := finite_tuple_root_relative_norm p q z hz hpq
  have hZ : 0 < ‖z‖ := by
    have hh := hrel.1
    have hn := norm_nonneg z
    nlinarith only [hh,hpq,hn]
  have hnorm (i : Fin 6) : 0 < ‖f (a i)‖ := by
    have hh := one_le_norm_integer hK phi (ha.2.1 i)
    change 1 ≤ ‖f (a i)‖ at hh
    linarith only [hh]
  exact four_anchor_V_window_scalar ‖f (a 0)‖ ‖f (a 1)‖ ‖f (a 3)‖
    ‖p‖ ‖q‖ ‖z‖ (hnorm 0) (hnorm 1) (hnorm 3) hp hZ hrel.1 hrel.2 hform

end D1Bound5
end
