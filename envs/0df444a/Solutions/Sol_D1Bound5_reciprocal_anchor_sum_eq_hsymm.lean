-- Prove2me | solution 1 for D1Bound5.reciprocal_anchor_sum_eq_hsymm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:13.301+00:00
-- url     : https://prove2.me/submissions/196ef9fa-49e7-4088-9d03-c23b9bdf1b61

import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Theorems.Thm_D1Bound5_lagrange_power_moment_eq_hsymm
import Theorems.Thm_D1Bound5_reciprocal_anchor_sum_transfer

section
open Finset

namespace D1Bound5

/-- The all-order negative-power interpolation identity from the frozen
manuscript, with its exact parity sign and product denominator. -/
theorem _root_.solution
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F) (hs : s.Nonempty)
    (ha : ∀ i ∈ s, a i ≠ 0) (hinj : Set.InjOn a s) (k : ℕ) :
    (∑ i ∈ s, ((a i)⁻¹) ^ (k + 1) /
      (∏ j ∈ s.erase i, (a i - a j))) =
      ((-1 : F) ^ (s.card - 1) * (∏ i ∈ s, a i)⁻¹) *
        MvPolynomial.aeval (fun i : s => (a i)⁻¹) (MvPolynomial.hsymm s F k) := by
  have hinv : Set.InjOn (fun i => (a i)⁻¹) s := by
    intro i hi j hj hij
    apply hinj hi hj
    simpa only [inv_inv] using congrArg Inv.inv hij
  have hp : 0 < s.card := hs.card_pos
  have hexp : k + s.card - 1 = s.card - 1 + k := by omega
  rw [reciprocal_anchor_sum_transfer s a ha k, hexp,
    lagrange_power_moment_eq_hsymm s (fun i => (a i)⁻¹) hs hinv k]

end D1Bound5
end
