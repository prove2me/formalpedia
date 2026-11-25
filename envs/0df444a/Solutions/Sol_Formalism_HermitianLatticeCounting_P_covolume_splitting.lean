-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.covolume_splitting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:25:17.903927+00:00
-- url     : https://prove2.me/submissions/c38d84f2-dc86-4b98-b66f-67bef9d96598

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : CovSplit := by
  intro f r k v cc hf hv hcc hlo hhi
  set w : ℝ := 2 * v with hw
  have hw0 : 0 < w := by positivity
  have hF : (0 : ℝ) < f := by exact_mod_cast hf
  have hroot : (w ^ ((f : ℝ) / 2)) ^ (1 / (f : ℝ)) = w ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul hw0.le]; congr 1; field_simp
  have hs : 0 < w ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hw0 _
  have h2root : (((2 : ℝ) ^ f)⁻¹) ^ (1 / (f : ℝ)) = 1 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num), ← Real.rpow_mul (by norm_num)]
    have : -(f : ℝ) * (1 / (f : ℝ)) = -1 := by field_simp
    rw [this, Real.rpow_neg_one]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · have := Real.rpow_le_rpow (by positivity) hlo (by positivity : (0 : ℝ) ≤ 1 / (f : ℝ))
    rw [Real.mul_rpow (by positivity) (by positivity), hroot, h2root] at this
    rw [← div_eq_mul_inv, le_div_iff₀ hs]; exact this
  · have := Real.rpow_le_rpow hcc.le hhi (by positivity : (0 : ℝ) ≤ 1 / (f : ℝ))
    rw [hroot] at this
    rw [← div_eq_mul_inv, div_le_one hs]; exact this
  · have hN : r * (k + 1) + r * (r - 1) = r * k + r ^ 2 := by
      cases r with
      | zero => simp
      | succ n => simp only [Nat.add_sub_cancel]; ring
    rw [hN, Real.mul_rpow (by positivity) (by positivity)]
    have e1 : (w ^ (f * (r * k + r ^ 2))) ^ (1 / (f : ℝ)) = w ^ (r * k) * w ^ ((r : ℝ) ^ 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hw0.le, ← Real.rpow_natCast, ← Real.rpow_add hw0]
      congr 1; push_cast; field_simp
    have e2 : (cc ^ r) ^ (1 / (f : ℝ)) = (cc ^ (1 / (f : ℝ))) ^ r := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hcc.le, ← Real.rpow_natCast, ← Real.rpow_mul hcc.le,
        mul_comm]
    have e3 : w ^ ((r : ℝ) ^ 2 + (r : ℝ) / 2) = w ^ ((r : ℝ) ^ 2) * (w ^ (1 / 2 : ℝ)) ^ r := by
      rw [Real.rpow_add hw0, ← Real.rpow_natCast (w ^ (1 / 2 : ℝ)), ← Real.rpow_mul hw0.le]
      congr 2; ring
    rw [e1, e2, e3, mul_pow (cc ^ (1 / (f : ℝ))), inv_pow]
    have hsr : (w ^ (1 / 2 : ℝ)) ^ r ≠ 0 := by positivity
    field_simp
end Formalism.HermitianLatticeCounting.P
