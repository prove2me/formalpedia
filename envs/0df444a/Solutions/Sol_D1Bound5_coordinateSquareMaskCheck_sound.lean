-- Prove2me | solution 1 for D1Bound5.coordinateSquareMaskCheck_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:41:40.419702+00:00
-- url     : https://prove2.me/submissions/b9828a95-501d-4a0d-a04b-05d7a32cd3e3

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_CoordinateSquareMaskCheck_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions

section
namespace D1Bound5





/-- Every accepted integer residue check proves the original modular
mask validity. The modulus is positive, all residue pairs are covered,
and the zero square remains included. -/
theorem _root_.solution (tau nu : ℤ) (k mask : ℕ)
    (h : coordinateSquareMaskCheck tau nu k mask = true) :
    CoordinateSquareMaskValid tau nu k mask := by
  intro x y
  have hx : x.val ∈ List.range (k+1) := List.mem_range.mpr x.val_lt
  have hy : y.val ∈ List.range (k+1) := List.mem_range.mpr y.val_lt
  have hrow := List.all_eq_true.mp h x.val hx
  have hxy := List.all_eq_true.mp hrow y.val hy
  have val_cast (z : ℤ) : (z : ZMod (k+1)).val = (z % (k+1 : ℕ)).toNat := by
    simpa only [Int.toNat_natCast] using
      congrArg Int.toNat (ZMod.val_intCast (n := k+1) z)
  have hxcast : ((x.val : ℤ) : ZMod (k+1)) = x := by
    simp only [Int.cast_natCast,ZMod.natCast_zmod_val]
  have hycast : ((y.val : ℤ) : ZMod (k+1)) = y := by
    simp only [Int.cast_natCast,ZMod.natCast_zmod_val]
  have hre : (x*x+(-(nu : ZMod (k+1)))*y*y).val =
      ((((x.val : ℤ)*(x.val : ℤ)-nu*(y.val : ℤ)*(y.val : ℤ)) %
        (k+1 : ℕ)).toNat) := by
    rw [←val_cast]
    congr 1
    simp only [Int.cast_sub,Int.cast_mul,hxcast,hycast]
    ring
  have him : (x*y+y*x+(tau : ZMod (k+1))*y*y).val =
      ((((x.val : ℤ)*(y.val : ℤ)+(y.val : ℤ)*(x.val : ℤ)+
        tau*(y.val : ℤ)*(y.val : ℤ)) % (k+1 : ℕ)).toNat) := by
    rw [←val_cast]
    congr 1
    simp only [Int.cast_add,Int.cast_mul,hxcast,hycast]
  rw [hre,him]
  exact hxy

end D1Bound5

namespace D1Bound5





end D1Bound5
end
