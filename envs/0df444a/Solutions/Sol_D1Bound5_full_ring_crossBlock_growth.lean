-- Prove2me | solution 1 for D1Bound5.full_ring_crossBlock_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:58:22.153376+00:00
-- url     : https://prove2.me/submissions/87cfb3d8-741a-4bc1-86ac-9579b3cafa90

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_crossBlock_growth
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped BigOperators NumberField
open Module

namespace D1Bound5







/-- The complete cross-block growth lemma for the full integer ring of an
arbitrary imaginary quadratic field. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a b : Fin 3 → 𝓞 K) (M : Fin 3 → Fin 3 → 𝓞 K)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hroot : ∀ i j, (M i j)^2 = a i*b j+1)
    (hmonA : Monotone (fun i => ‖phi (a i : K)‖))
    (hmonB : Monotone (fun i => ‖phi (b i : K)‖))
    (hlarge : 9 ≤ ‖phi (a 0 : K)‖*‖phi (b 0 : K)‖) :
    (‖phi (a 0 : K)‖*‖phi (b 0 : K)‖)^3*
        (‖phi (a 1 : K)‖*‖phi (b 1 : K)‖)/7 <
      ‖phi (a 2 : K)‖*‖phi (b 2 : K)‖ := by
  exact crossBlock_growth (phi.comp (algebraMap (𝓞 K) K))
    (fun x hx => one_le_norm_integer hK phi hx)
    a b M ha hb hroot hmonA hmonB hlarge



end D1Bound5
end
