-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.tail_irregular_and_growth_of_four_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:48:54.014718+00:00
-- url     : https://prove2.me/submissions/e894e9ec-52e5-43e6-ad1b-096cd29ff6fe

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_Regular_Definitions
import Theorems.Thm_D1Bound5_irregular_growth
import Theorems.Thm_D1Bound5_tail_irregular_of_four_le

section
open scoped NumberField
open Module

namespace D1Bound5






/-- The large-C tail lemma and its growth consequence for an actual
ordered D(1) quadruple. Monotonicity allows equal moduli. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 4 → 𝓞 K) (ht : IsD1Tuple t)
    (hmon : Monotone (fun i => ‖phi (t i : K)‖))
    (hB : 3 ≤ ‖phi (t 1 : K)‖) (hC : 4 ≤ ‖phi (t 2 : K)‖) :
    regularDefect (t 1) (t 2) (t 3) ≠ 0 ∧
      2*‖phi (t 1 : K)‖*‖phi (t 2 : K)‖ < ‖phi (t 3 : K)‖ := by
  have roots (i j : Fin 4) (hij : i ≠ j) :
      ∃ r : 𝓞 K, r^2 = t i*t j+1 := by
    simpa only [pow_two] using ht.2.2 i j hij
  have hirr := tail_irregular_of_four_le hK phi (t 0) (t 1) (t 2) (t 3)
    (ht.2.1 0) (roots 0 1 (by decide)) (roots 0 2 (by decide))
    (roots 0 3 (by decide)) (roots 1 2 (by decide))
    (hmon (by decide : (0 : Fin 4) ≤ 1)) hB hC
    (hmon (by decide : (2 : Fin 4) ≤ 3))
  obtain ⟨r,hr⟩ := roots 1 2 (by decide)
  obtain ⟨s,hs⟩ := roots 1 3 (by decide)
  obtain ⟨v,hv⟩ := roots 2 3 (by decide)
  exact ⟨hirr,irregular_growth hK phi (t 1) (t 2) (t 3) r s v hr hs hv hirr
    hB (hmon (by decide : (1 : Fin 4) ≤ 2))
    (hmon (by decide : (2 : Fin 4) ≤ 3))⟩

end D1Bound5
end
