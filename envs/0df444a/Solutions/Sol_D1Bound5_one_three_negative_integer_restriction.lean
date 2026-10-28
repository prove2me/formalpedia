-- Prove2me | solution 1 for D1Bound5.one_three_negative_integer_restriction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:56:36.909276+00:00
-- url     : https://prove2.me/submissions/1a429165-9f09-438e-ad5e-533bb925a6d3

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_D1Bound5_one_three_negative_parameter

section
open scoped NumberField
open Module

namespace D1Bound5




















/-- Fixed-field version of the negative common-extension restriction. -/
theorem _root_.solution {K : Type*} [Field K]
    [NumberField K] [NumberField.IsTotallyComplex K]
    (d : ℤ) (hd : 0 < d)
    (hparam : ∀ m : ℤ, m ≤ 0 → (∃ r : 𝓞 K, r*r = (m : 𝓞 K)) →
      ∃ y : ℤ, m = -d*y^2)
    {n : ℤ} (hn : n < 0)
    (hr : ∃ r : 𝓞 K, r*r = (n : 𝓞 K)+1)
    (hs : ∃ s : 𝓞 K, s*s = 3*(n : 𝓞 K)+1) :
    d=2 ∧ n%2=1 := by
  obtain ⟨u,hu⟩ := hparam (n+1) (by omega) (by simpa using hr)
  obtain ⟨v,hv⟩ := hparam (3*n+1) (by omega) (by simpa using hs)
  obtain ⟨hd2,hodd⟩ := one_three_negative_parameter hd
    (x := -n) (u := u) (v := v) (by nlinarith [hu]) (by nlinarith [hv])
  exact ⟨hd2, by omega⟩










end D1Bound5
end
