-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.finiteQ_upper_of_lower
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:51:25.050985+00:00
-- url     : https://prove2.me/submissions/b4608e28-701f-4dcc-8959-82e0aa99413a

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
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Theorems.Thm_D1Bound5_full_ring_finiteQ_closed_interval_excluded
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- The actual finite Q interval forces an ordered full-ring sextuple
past its upper endpoint as soon as it has passed the lower endpoint.
The lower anchor radius is one, obtained from integrality. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hC : 1000 ≤ ‖phi (a 4 : K)‖)
    (hCT : 4*‖phi (a 3 : K)‖ ≤ ‖phi (a 4 : K)‖)
    (hleft : 4*55^2*‖phi (a 3 : K)‖^6*‖phi (a 4 : K)‖^3/(1-1/4000 : ℝ) ≤
      ‖phi (a 5 : K)‖) :
    ‖phi (a 4 : K)‖^7/(9*‖phi (a 3 : K)‖^2*(1+1/4000 : ℝ)) <
      ‖phi (a 5 : K)‖ := by
  classical
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
  let b : Fin 4 → 𝓞 K := fun i => a (Fin.castAdd 2 i)
  have hcast : Function.Injective (Fin.castAdd 2 : Fin 4 → Fin 6) := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin 6 => k.val) hij
  have hbc (i : Fin 4) : b i ≠ a 4 := by
    apply ha.1.ne
    apply Fin.ne_of_val_ne
    have hi := i.isLt
    change i.val ≠ 4
    omega
  have hbd (i : Fin 4) : b i ≠ a 5 := by
    apply ha.1.ne
    apply Fin.ne_of_val_ne
    have hi := i.isLt
    change i.val ≠ 5
    omega
  have hlow (i : Fin 4) : (1 : ℝ) ≤ ‖phi (b i : K)‖ :=
    one_le_norm_integer hK phi (ha.2.1 (Fin.castAdd 2 i))
  have hhigh (i : Fin 4) : ‖phi (b i : K)‖ ≤ ‖phi (a 3 : K)‖ := by
    apply hmon
    change i.val ≤ 3
    omega
  by_contra hn
  have hright := le_of_not_gt hn
  exact full_ring_finiteQ_closed_interval_excluded hK phi hTup b (a 4) (a 5)
    (fun i => hmem (Fin.castAdd 2 i)) (hmem 4) (hmem 5)
    (ha.1.comp hcast) hbc hbd (ha.1.ne (by decide)) 1 ‖phi (a 3 : K)‖
    (by norm_num) hlow hhigh hCT (hmon (by decide))
    (by simpa only [one_mul] using hC) hleft
    (by simpa only [one_pow,one_mul] using hright)



end D1Bound5
end
