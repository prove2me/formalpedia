-- Prove2me | solution 1 for D1Bound5.pairResidueMaskNatBool_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:19:18.158518+00:00
-- url     : https://prove2.me/submissions/fc78275f-3877-40b0-b064-56c053651e9b

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairResidueMaskNat_Definitions

section
namespace D1Bound5



/-- Exact equality with the accepted cached mask predicate for every input.
No signature validity, residue bound, mask validity, or discriminant premise
is needed. In particular, modulus one is included. -/
theorem _root_.solution (tau nu : ℤ) (k mask : ℕ) (u v : ℕ × ℕ) :
    pairResidueMaskNatBool tau nu k mask u v = pairResidueMaskBool tau nu k mask u v := by
  have hre :
      (u.1 * v.1 + (-(nu : ZMod (k + 1))).val * u.2 * v.2 + 1) % (k + 1) =
        ((u.1 : ZMod (k + 1)) * (v.1 : ZMod (k + 1)) +
          (-(nu : ZMod (k + 1))) * (u.2 : ZMod (k + 1)) * (v.2 : ZMod (k + 1)) + 1).val := by
    rw [← ZMod.val_natCast]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, ZMod.natCast_zmod_val]
  have him :
      (u.1 * v.2 + u.2 * v.1 + (tau : ZMod (k + 1)).val * u.2 * v.2) % (k + 1) =
        ((u.1 : ZMod (k + 1)) * (v.2 : ZMod (k + 1)) +
          (u.2 : ZMod (k + 1)) * (v.1 : ZMod (k + 1)) +
          (tau : ZMod (k + 1)) * (u.2 : ZMod (k + 1)) * (v.2 : ZMod (k + 1))).val := by
    rw [← ZMod.val_natCast]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  dsimp only [pairResidueMaskNatBool, pairResidueMaskBool]
  rw [hre, him]

end D1Bound5
end
