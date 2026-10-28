-- Prove2me | solution 1 for D1Bound5.full_ring_finiteQRowForm_exists_one_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:51:13.852818+00:00
-- url     : https://prove2.me/submissions/d9bbdd42-f3d5-4236-9efd-17367f0c71b6

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQIntegralRows_Definitions
import Theorems.Thm_D1Bound5_finiteQRowForm_exists_ne_zero
import Theorems.Thm_D1Bound5_map_finiteQRowForm
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]















/-- Full-ring arithmetic lower bound for one actual finite Q row. The
selected row is an integer polynomial combination of the supplied roots,
and its nonvanishing comes from the explicit determinant above. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a b s t c z rA rB rS rT : 𝓞 K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hat : a ≠ t)
    (hbs : b ≠ s) (hbt : b ≠ t) (hst : s ≠ t) (hz : z ≠ 0) :
    ∃ i : Fin 5, 1 ≤ ‖finiteQRowForm
      (phi (a : K)) (phi (b : K)) (phi (s : K)) (phi (t : K)) (phi (c : K))
      (phi (z : K)) (phi (rA : K)) (phi (rB : K)) (phi (rS : K)) (phi (rT : K)) i‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hnonzero (x : 𝓞 K) (hx : x ≠ 0) : f x ≠ 0 := by
    intro h
    apply hx
    apply hf
    simpa only [map_zero] using h
  obtain ⟨i, hi⟩ := finiteQRowForm_exists_ne_zero
    (f a) (f b) (f s) (f t) (f c) (f z) (f rA) (f rB) (f rS) (f rT)
    (hnonzero a ha) (hnonzero b hb) (hnonzero s hs) (hnonzero t ht)
    (fun h => hab (hf h)) (fun h => has (hf h)) (fun h => hat (hf h))
    (fun h => hbs (hf h)) (fun h => hbt (hf h)) (fun h => hst (hf h)) (hnonzero z hz)
  let L := finiteQRowForm a b s t c z rA rB rS rT i
  have hL : f L = finiteQRowForm (f a) (f b) (f s) (f t) (f c)
      (f z) (f rA) (f rB) (f rS) (f rT) i := map_finiteQRowForm f _ _ _ _ _ _ _ _ _ _ i
  have hL0 : L ≠ 0 := by
    intro hzero
    apply hi
    rw [← hL, hzero, map_zero]
  have hbound := one_le_norm_integer hK phi hL0
  change 1 ≤ ‖f L‖ at hbound
  rw [hL] at hbound
  exact ⟨i, hbound⟩

end D1Bound5
end
