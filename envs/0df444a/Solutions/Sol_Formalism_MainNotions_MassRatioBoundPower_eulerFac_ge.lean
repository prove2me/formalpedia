-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioBoundPower.eulerFac_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:41:33.836302+00:00
-- url     : https://prove2.me/submissions/9e6e0bfc-b126-4174-9aca-7469861c8d61

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBoundPower
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_rpow_bounds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioBoundPower
open NumberField Formalism.MainNotions.MassRatioZetaBound
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.MainNotions.MassRatioBoundPower
theorem _root_.solution [StarRing K] {M : ℕ} (hM : 3 ≤ M) (P : Ideal (𝓞 K)) (hN : 2 ≤ Ideal.absNorm P) :
    Real.exp (-(2 * (1 / ((Ideal.absNorm P : ℕ) : ℝ) ^ ((3 : ℝ) / 2)))) ≤ Formalism.HermitianLatticesTheory.eulerFac K M P := by
  set N : ℝ := ((Ideal.absNorm P : ℕ) : ℝ) with hNdef
  have hN2 : (2 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hN
  have hN0 : 0 < N := by linarith
  obtain ⟨hb1, hb2⟩ := rpow_bounds hN2 hM
  set y : ℝ := 1 / N ^ ((3 : ℝ) / 2) with hy
  have hy0 : 0 ≤ y := by positivity
  have hle1 : Real.exp (-(2 * y)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  unfold Formalism.HermitianLatticesTheory.eulerFac
  split_ifs with hc
  · have hx : Real.sqrt N ^ (-(M : ℤ)) = N ^ (-(M : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hN0.le]
      congr 1; push_cast; ring
    rw [← hNdef, hx]
    set x : ℝ := N ^ (-(M : ℝ) / 2) with hxdef
    have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 _
    have h1 : x ≤ 1 / 2 := hb1.trans hb2
    rcases Nat.even_or_odd M with he | ho
    · rw [he.neg_one_pow, one_mul]
      calc Real.exp (-(2 * y)) ≤ 1 := hle1
        _ ≤ (1 - x)⁻¹ := one_le_inv₀ (by linarith) |>.2 (by linarith)
    · rw [ho.neg_one_pow, neg_one_mul, sub_neg_eq_add]
      calc Real.exp (-(2 * y)) ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)
        _ = (Real.exp x)⁻¹ := Real.exp_neg x
        _ ≤ (1 + x)⁻¹ := by
            rw [inv_le_inv₀ (Real.exp_pos _) (by linarith)]
            linarith [Real.add_one_le_exp x]
  · rw [← hNdef]
    set z : ℝ := N ^ (-(M : ℤ)) with hz
    have hz0 : 0 < z := zpow_pos hN0 _
    have hzx : z ≤ N ^ (-(M : ℝ) / 2) := by
      rw [hz, ← Real.rpow_intCast]
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      push_cast
      have : (0 : ℝ) ≤ M := by positivity
      linarith
    have hz1 : z ≤ 1 / 2 := hzx.trans (hb1.trans hb2)
    have hpos : 0 < 1 - z := by linarith
    have e : (1 - z) ^ ((-1 : ℝ) / 2) = ((1 - z)⁻¹) ^ ((1 : ℝ) / 2) := by
      rw [Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le]; congr 1; ring
    rw [e]
    have hge1 : 1 ≤ (1 - z)⁻¹ := one_le_inv₀ hpos |>.2 (by linarith)
    calc Real.exp (-(2 * y)) ≤ 1 := hle1
      _ ≤ ((1 - z)⁻¹) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hge1 (by norm_num)
end Formalism.MainNotions.MassRatioBoundPower
