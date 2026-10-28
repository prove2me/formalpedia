-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.three_small_fifth_large
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T22:57:24.169991+00:00
-- url     : https://prove2.me/submissions/79a79810-caee-466f-a48d-4c837b0363e5

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_properCommonExtension_first_three
import Theorems.Thm_D1Bound5_IsD1Tuple_small_triple_bounded_extensions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg

section
open scoped NumberField Classical
open Module

namespace D1Bound5

private theorem norm_sq_le_ten_pow_eighty (z : ℂ)
    (hz : ‖z‖ ≤ (10 : ℝ)^40) : ‖z‖^2 ≤ (10 : ℝ)^80 := by
  have hp : 0 ≤ (10 : ℝ)^40 := by positivity
  have hid : ((10 : ℝ)^40)^2 = (10 : ℝ)^80 := by norm_num
  nlinarith only [hid, mul_nonneg (sub_nonneg.mpr hz)
    (add_nonneg hp (_root_.norm_nonneg z))]



/-- An ordered actual sextuple with three small initial entries must have
fifth modulus greater than 10^40. Its fourth modulus is either less than
85 or also greater than 10^40. This follows from complete bounded-extension
uniqueness, without any bound on the final tuple entry. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 6 → 𝓞 K) (ht : IsD1Tuple t)
    (hmon : Monotone (fun i => ‖phi (t i : K)‖))
    (hsmall : ‖phi (t 2 : K)‖ < 3) :
    (10 : ℝ)^40 < ‖phi (t 4 : K)‖ ∧
      (‖phi (t 3 : K)‖ < 85 ∨ (10 : ℝ)^40 < ‖phi (t 3 : K)‖) := by
  classical
  let j : Fin 3 → Fin 6 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  have hj : Function.Injective j := by
    intro i k hik
    apply Fin.ext
    exact congrArg (fun l : Fin 6 => l.val) hik
  let s : Fin 3 → 𝓞 K := fun i => t (j i)
  have hs : IsD1Tuple s := by
    refine ⟨ht.1.comp hj, fun i => ht.2.1 (j i), ?_⟩
    intro i k hik
    exact ht.2.2 (j i) (j k) (fun h => hik (hj h))
  have hs_small (i : Fin 3) : ‖phi (s i : K)‖ < 3 := by
    have hi : j i ≤ (2 : Fin 6) := by
      change i.val ≤ 2
      omega
    exact lt_of_le_of_lt (hmon hi) hsmall
  have hproperty := IsD1Tuple.small_triple_bounded_extensions hK phi s hs hs_small
  change
    (∀ z : 𝓞 K, ProperCommonExtension {t 0,t 1,t 2} z →
      ‖phi (z : K)‖^2 ≤ (10 : ℝ)^80 → ‖phi (z : K)‖ < 85) ∧
    (∀ z w : 𝓞 K, ProperCommonExtension {t 0,t 1,t 2} z →
      ProperCommonExtension {t 0,t 1,t 2} w →
      ‖phi (z : K)‖^2 ≤ (10 : ℝ)^80 →
      ‖phi (w : K)‖^2 ≤ (10 : ℝ)^80 → z = w) at hproperty
  have h3 := IsD1Tuple.properCommonExtension_first_three t ht 3 (by decide)
  have h4 := IsD1Tuple.properCommonExtension_first_three t ht 4 (by decide)
  constructor
  · by_contra h
    have hle4 : ‖phi (t 4 : K)‖ ≤ (10 : ℝ)^40 := le_of_not_gt h
    have hle3 : ‖phi (t 3 : K)‖ ≤ (10 : ℝ)^40 :=
      (hmon (by decide : (3 : Fin 6) ≤ 4)).trans hle4
    have heq := hproperty.2 (t 3) (t 4) h3 h4
      (norm_sq_le_ten_pow_eighty _ hle3) (norm_sq_le_ten_pow_eighty _ hle4)
    exact (by decide : (3 : Fin 6) ≠ 4) (ht.1 heq)
  · by_cases hle3 : ‖phi (t 3 : K)‖ ≤ (10 : ℝ)^40
    · exact Or.inl (hproperty.1 (t 3) h3 (norm_sq_le_ten_pow_eighty _ hle3))
    · exact Or.inr (lt_of_not_ge hle3)

end D1Bound5
end
