-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioZetaBound.eulerFac_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:11.987617+00:00
-- url     : https://prove2.me/submissions/392482f0-271d-4fc3-a0ec-d72c537302f8

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_inv_one_sub_le_exp
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
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioZetaBound
open NumberField
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.MainNotions.MassRatioZetaBound
theorem _root_.solution [StarRing K] {M : ℕ} (hM : 3 ≤ M) (P : Ideal (𝓞 K)) (hN : 2 ≤ Ideal.absNorm P) :
    0 < Formalism.HermitianLatticesTheory.eulerFac K M P ∧
      Formalism.HermitianLatticesTheory.eulerFac K M P ≤ Real.exp (2 * (1 / ((Ideal.absNorm P : ℕ) : ℝ) ^ ((3 : ℝ) / 2))) := by
  set N : ℝ := ((Ideal.absNorm P : ℕ) : ℝ) with hNdef
  have hN2 : (2 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hN
  have hN0 : 0 < N := by linarith
  obtain ⟨hb1, hb2⟩ := rpow_bounds hN2 hM
  set y : ℝ := 1 / N ^ ((3 : ℝ) / 2) with hy
  have hy0 : 0 ≤ y := by positivity
  unfold Formalism.HermitianLatticesTheory.eulerFac
  split_ifs with hc
  ·
    have hx : Real.sqrt N ^ (-(M : ℤ)) = N ^ (-(M : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hN0.le]
      congr 1; push_cast; ring
    rw [← hNdef, hx]
    set x : ℝ := N ^ (-(M : ℝ) / 2) with hxdef
    have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 _
    rcases Nat.even_or_odd M with he | ho
    · rw [he.neg_one_pow, one_mul]
      have h1 : x ≤ 1 / 2 := hb1.trans hb2
      refine ⟨inv_pos.2 (by linarith), ?_⟩
      calc (1 - x)⁻¹ ≤ Real.exp (2 * x) := inv_one_sub_le_exp hx0.le h1
        _ ≤ Real.exp (2 * y) := Real.exp_le_exp.2 (by linarith)
    · rw [ho.neg_one_pow, neg_one_mul, sub_neg_eq_add]
      refine ⟨inv_pos.2 (by linarith), ?_⟩
      calc (1 + x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
        _ ≤ Real.exp (2 * y) := Real.one_le_exp (by positivity)
  ·
    rw [← hNdef]
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
    refine ⟨Real.rpow_pos_of_pos hpos _, ?_⟩
    have e : (1 - z) ^ ((-1 : ℝ) / 2) = ((1 - z)⁻¹) ^ ((1 : ℝ) / 2) := by
      rw [Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le]; congr 1; ring
    rw [e]
    have hge1 : 1 ≤ (1 - z)⁻¹ := one_le_inv₀ hpos |>.2 (by linarith)
    calc ((1 - z)⁻¹) ^ ((1 : ℝ) / 2) ≤ ((1 - z)⁻¹) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hge1 (by norm_num)
      _ = (1 - z)⁻¹ := Real.rpow_one _
      _ ≤ Real.exp (2 * z) := inv_one_sub_le_exp hz0.le hz1
      _ ≤ Real.exp (2 * y) := Real.exp_le_exp.2 (by linarith [hzx.trans hb1])
end Formalism.MainNotions.MassRatioZetaBound
