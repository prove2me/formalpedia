-- Prove2me | solution 1 for D1Bound5.pairLightSelectedMaskRejectBool_eq_raw
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:16.93502+00:00
-- url     : https://prove2.me/submissions/f0f5e665-ae8d-44de-9619-f41af5882edb

import Init
import Mathlib.Algebra.Order.Ring.Abs
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
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairRawSelectedFloorWitnesses_Definitions
import Definitions.Def_D1Bound5_PairResidueMaskNat_Definitions
import Theorems.Thm_D1Bound5_pairLight_intCast_val

section
namespace D1Bound5





















/-- Equality is unconditional, so unsupported traces and all malformed
natural signatures retain exactly the accepted mask behavior. -/
theorem pairLightResidueMaskNatBool_eq_raw (tau nu : ℤ) (k mask : ℕ) (u v : ℕ × ℕ) :
    pairLightResidueMaskNatBool tau nu k mask u v = pairResidueMaskNatBool tau nu k mask u v := by
  have hn : (-(nu : ZMod (k + 1))).val = ((-nu) % Int.ofNat (k + 1)).toNat := by
    simpa only [Int.cast_neg] using pairLight_intCast_val k (-nu)
  simp only [pairLightResidueMaskNatBool, pairResidueMaskNatBool, hn, pairLight_intCast_val]

theorem _root_.solution (tau nu : ℤ) (sieve : List (ℕ × ℕ))
    (xs ys : PairLightSignature) (i : ℕ) :
    pairLightSelectedMaskRejectBool tau nu sieve xs ys i =
      pairSelectedCachedMaskNatRejectBool tau nu sieve xs ys i := by
  cases hm : sieve[i]? with
  | none => simp only [pairLightSelectedMaskRejectBool, pairSelectedCachedMaskNatRejectBool, hm]
  | some item =>
      rcases item with ⟨k, mask⟩
      cases hx : xs[i]? <;> cases hy : ys[i]? <;>
        simp only [pairLightSelectedMaskRejectBool, pairSelectedCachedMaskNatRejectBool,
          hm, hx, hy, pairLightResidueMaskNatBool_eq_raw]

















end D1Bound5
end
