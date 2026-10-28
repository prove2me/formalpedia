-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.unit_pair_cubic_iteration
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:38:48.450001+00:00
-- url     : https://prove2.me/submissions/966441da-2dac-4727-8dfb-6a79d3dde8a7

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_discrete_unit_pair_symmetric_obstruction
import Theorems.Thm_D1Bound5_full_ring_unit_pair_cubic_growth
import Theorems.Thm_D1Bound5_one_le_norm_integer
import Theorems.Thm_D1Bound5_unit_pair_three_cubic_gaps

section
open scoped NumberField
open Module

namespace D1Bound5



/-- The actual unit-pair sextuple already supplies every opposite-pair
exclusion through the symmetric-five obstruction. Thus the three cubic
steps require no extra hypothesis about signs of its four extensions. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hminus : a 0 = -1) (hplus : a 1 = 1)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hS : 9 ≤ ‖phi (a 2 : K)‖) :
    ‖phi (a 2 : K)‖^27/8192 < ‖phi (a 5 : K)‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hdiscrete (x : 𝓞 K) (hx : x ≠ 0) : 1 ≤ ‖f x‖ :=
    one_le_norm_integer hK phi hx
  have hlarge (i : Fin 6) (hi : 2 ≤ i) : 9 ≤ ‖f (a i)‖ :=
    hS.trans (hmon hi)
  have hroots (i : Fin 6) (hi : 2 ≤ i) :
      (∃ r : 𝓞 K, r^2 = a i+1) ∧ (∃ r : 𝓞 K, r^2 = 1-a i) := by
    obtain ⟨p,hp⟩ := ha.2.2 1 i (by omega)
    obtain ⟨m,hm⟩ := ha.2.2 0 i (by omega)
    constructor
    · exact ⟨p,by simpa only [pow_two,hplus,one_mul] using hp⟩
    · refine ⟨m,?_⟩
      rw [pow_two,hm,hminus]
      ring
  have hnoOpp (i j k : Fin 6) (hi : 2 ≤ i) (hk : 2 ≤ k)
      (hik : i ≠ k) (hjk : j ≠ k) : a j ≠ -a i := by
    intro hopp
    obtain ⟨hip,him⟩ := hroots i hi
    obtain ⟨hkp,hkm⟩ := hroots k hk
    obtain ⟨p,hp⟩ := ha.2.2 i k hik
    obtain ⟨m,hm⟩ := ha.2.2 j k hjk
    apply discrete_unit_pair_symmetric_obstruction f hdiscrete (a i) (a k)
      (by linarith only [hlarge i hi]) (by linarith only [hlarge k hk])
      him (by simpa only [add_comm] using hip)
      hkm (by simpa only [add_comm] using hkp)
    · refine ⟨m,?_⟩
      rw [pow_two,hm,hopp]
      ring
    · exact ⟨p,by simpa only [pow_two,add_comm] using hp⟩
  have hgap (i j k : Fin 6) (hi : 2 ≤ i) (hj : 2 ≤ j) (hk : 2 ≤ k)
      (hij : i < j) (hik : i ≠ k) (hjk : j ≠ k) :
      ‖f (a i)‖^3/2 < ‖f (a j)‖ := by
    obtain ⟨hip,him⟩ := hroots i hi
    obtain ⟨hjp,hjm⟩ := hroots j hj
    obtain ⟨r,hr⟩ := ha.2.2 i j (ne_of_lt hij)
    exact full_ring_unit_pair_cubic_growth hK phi (a i) (a j)
      (hlarge i hi) (hmon hij.le) (hnoOpp i j k hi hk hik hjk)
      hip him hjp hjm ⟨r,by simpa only [pow_two] using hr⟩
  exact unit_pair_three_cubic_gaps ‖f (a 2)‖ ‖f (a 3)‖ ‖f (a 4)‖ ‖f (a 5)‖ hS
    (hgap 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hgap 3 4 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hgap 4 5 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

end D1Bound5
end
