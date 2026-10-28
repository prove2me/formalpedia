-- Prove2me | solution 1 for D1Bound5.coherent_anchor_power_moment_high
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:47:28.343347+00:00
-- url     : https://prove2.me/submissions/1f1fb4ab-8089-4e39-96fb-1cabbde748b1

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Theorems.Thm_D1Bound5_reciprocal_anchor_sum_eq_hsymm

section
open Finset Polynomial

namespace D1Bound5



/-- Every remaining Taylor moment is a complete homogeneous polynomial
in the reciprocal anchors, with the exact sign and product denominator. -/
theorem _root_.solution
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F) (hs : s.Nonempty)
    (ha : ∀ i ∈ s, a i ≠ 0) (hinj : Set.InjOn a s) (k : ℕ) :
    (∑ i ∈ s, ((a i) ^ (s.card - 1) /
      (∏ j ∈ s.erase i, (a i - a j))) * ((a i)⁻¹) ^ (s.card + k)) =
      ((-1 : F) ^ (s.card - 1) * (∏ i ∈ s, a i)⁻¹) *
        MvPolynomial.aeval (fun i : s => (a i)⁻¹)
          (MvPolynomial.hsymm s F k) := by
  have hcard : 0 < s.card := hs.card_pos
  have hexp : s.card + k = (s.card - 1) + (k + 1) := by omega
  have hterm (i : ι) (hi : i ∈ s) :
      (a i) ^ (s.card - 1) * ((a i)⁻¹) ^ (s.card + k) =
        ((a i)⁻¹) ^ (k + 1) := by
    rw [hexp, pow_add, ← mul_assoc, ← mul_pow]
    simp [ha i hi]
  calc
    (∑ i ∈ s, ((a i) ^ (s.card - 1) /
        (∏ j ∈ s.erase i, (a i - a j))) * ((a i)⁻¹) ^ (s.card + k)) =
      ∑ i ∈ s, ((a i)⁻¹) ^ (k + 1) /
        (∏ j ∈ s.erase i, (a i - a j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        ((a i) ^ (s.card - 1) /
            (∏ j ∈ s.erase i, (a i - a j))) * ((a i)⁻¹) ^ (s.card + k) =
          ((a i) ^ (s.card - 1) * ((a i)⁻¹) ^ (s.card + k)) /
            (∏ j ∈ s.erase i, (a i - a j)) := by ring
        _ = _ := by rw [hterm i hi]
    _ = _ := reciprocal_anchor_sum_eq_hsymm s a hs ha hinj k









end D1Bound5




open Finset

namespace D1Bound5



end D1Bound5




open Finset

namespace D1Bound5





end D1Bound5




namespace D1Bound5









end D1Bound5
end
