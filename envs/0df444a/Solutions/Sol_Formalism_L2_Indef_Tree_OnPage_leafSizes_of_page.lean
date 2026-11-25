-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.OnPage.leafSizes_of_page
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:16:18.142574+00:00
-- url     : https://prove2.me/submissions/c8166bb7-c521-4aa9-b2ff-beedcde96bc2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONPage
import Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_L_eq_rpow
import Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_one_le_b
import Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_one_le_Xp
import Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_wt_bound
import Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_dfx_bound
import Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_two_cube_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.L2.Indef.Tree.OnPage
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}
set_option maxHeartbeats 1000000
namespace Formalism.L2.Indef.Tree.OnPage
theorem _root_.solution (O : OnObj S P c) (C2 : ℝ) (hC2 : 0 ≤ C2) (hC : 1 ≤ c.C)
    (hx : 3 ≤ O.x) (hxC : 3 * c.C * C2 ≤ O.x)
    (hEps : ExponentSmallBound O) (hN4 : HalfDegreeAtLeastFour O) (h1246 : DegreeAtLeastFortyFour O) (h29 : DimensionExceedsDegreeByThree O) (h21 : RankAndLengthLowerBounds O) (hW : LeafW O)
    (h14 : SupportGapBounds O) (h011 : EtaPowerBound O) (hSg : LeafSign O) (h1243 : NodeCountBound O) (h13 : DiscriminantDegreeBound O)
    (h231 : ProductLowerBoundTwist O) (h44 : TwistDensityBounds O) (tX2 : SecondRatioDefinition O) (tZ3 : TimeDiscriminantBound O C2) : LeafSizes O := by
  have hx0 : 0 ≤ O.x := by linarith
  have hxp : 0 < O.x := by linarith
  have hb := one_le_b O hx0
  have hbpos : 0 < O.b := by linarith
  have hXp := one_le_Xp O hx0
  have hn4 : 4 ≤ nH O := hN4
  have hf : 8 ≤ O.f := by
    have h4 : 4 ≤ O.f / 2 := hN4
    linarith
  have hm : 44 ≤ O.m := h1246.1
  have hk : O.m + 3 ≤ O.k := h29
  have hL : 10 ≤ O.L := h21.2
  have hLx : O.L = O.x ^ O.eps := L_eq_rpow O
  have he0 : 0 < O.eps := hEps.1
  have hkX : O.k ≤ Xp O := by
    obtain ⟨t, ht, hN⟩ := h1243
    have : 0 ≤ O.m * (t + 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hkpos : 0 < O.k := by linarith
  have hlogk : Real.log O.k ≤ O.L := by
    calc Real.log O.k ≤ Real.log (Xp O) := Real.log_le_log hkpos hkX
      _ = O.x ^ (O.eps / 3) := Real.log_exp _
      _ ≤ O.x ^ O.eps := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = O.L := hLx.symm
  obtain ⟨hDF0, nW, hnW, hDF2⟩ := h13
  have hDF1 : 1 < O.DF := by
    have hpi := Real.pi_gt_three
    have h80 : 1 < O.DF ^ 2 := by nlinarith
    by_contra hc
    push_neg at hc
    have : O.DF ^ 2 ≤ 1 := by nlinarith
    linarith
  have hY1 : 1 < O.Y := by
    show 1 < c.C * O.DF
    nlinarith
  obtain ⟨PP, D, hPP, hD, hT⟩ := h231
  obtain ⟨hde0', Lw, hLw, hde1'⟩ := h44
  have hde0 : 0 ≤ dl2 O := le_trans (Real.rpow_nonneg hx0 _) hde0'
  have hde1 : dl2 O ≤ 1 := by
    have : 1 / (4 * Lw) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hDFx := dfx_bound O.DF O.x O.k O.f O.m O.b O.T (dl2 O) PP D C2 hDF0 hPP hD hT hde0 hde1 tZ3 hC2 hkpos
    (by linarith) hx0 (by linarith) hbpos.le
  have hYmb : O.Y ≤ O.m * O.b := by
    show c.C * O.DF ≤ O.m * O.b
    have h1' : (c.C * O.DF) * O.x ≤ c.C * (3 * C2 * O.m * O.b) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hDFx (by linarith)
    have hmb : 0 ≤ O.m * O.b := mul_nonneg (by linarith) hbpos.le
    have h2' : c.C * (3 * C2 * O.m * O.b) ≤ (O.m * O.b) * O.x := by
      calc c.C * (3 * C2 * O.m * O.b) = (3 * c.C * C2) * (O.m * O.b) := by ring
        _ ≤ O.x * (O.m * O.b) := mul_le_mul_of_nonneg_right hxC hmb
        _ = (O.m * O.b) * O.x := by ring
    exact le_of_mul_le_mul_right (le_trans h1' h2') hxp
  have hlogY : Real.log O.Y ≤ 2 * O.L := by
    have hY0 : 0 < O.Y := by linarith
    have hmp : 0 < O.m := by linarith
    have hlm : Real.log O.m ≤ Real.log O.k := Real.log_le_log hmp (by linarith)
    calc Real.log O.Y ≤ Real.log (O.m * O.b) := Real.log_le_log hY0 hYmb
      _ = Real.log O.m + O.L := by rw [Real.log_mul hmp.ne' hbpos.ne']; rfl
      _ ≤ 2 * O.L := by linarith
  have hy : O.x ^ O.eps = (O.x ^ (O.eps / 3)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  have hy0 : 0 ≤ O.x ^ (O.eps / 3) := Real.rpow_nonneg hx0 _
  have hy3 : O.L = (O.x ^ (O.eps / 3)) ^ 3 := by rw [hLx, hy]
  have hy2 : 2 ≤ O.x ^ (O.eps / 3) := by
    by_contra hc
    push_neg at hc
    have : (O.x ^ (O.eps / 3)) ^ 3 < 2 ^ 3 := pow_lt_pow_left₀ hc hy0 (by norm_num)
    linarith
  have hkb : O.k ≤ O.b ^ ((4 : ℝ) / 5) := by
    have hb45 : O.b ^ ((4 : ℝ) / 5) = Real.exp ((O.x ^ (O.eps / 3)) ^ 3 * (4 / 5)) := by
      show (Real.exp (O.x ^ O.eps)) ^ ((4 : ℝ) / 5) = _
      rw [← Real.exp_mul, hy]
    rw [hb45]
    have hyy : O.x ^ (O.eps / 3) ≤ (O.x ^ (O.eps / 3)) ^ 3 * (4 / 5) := by
      have h4 : (0 : ℝ) ≤ (O.x ^ (O.eps / 3)) ^ 2 * (4 / 5) - 1 := by nlinarith
      nlinarith [mul_nonneg hy0 h4]
    calc O.k ≤ Xp O := hkX
      _ = Real.exp (O.x ^ (O.eps / 3)) := rfl
      _ ≤ Real.exp ((O.x ^ (O.eps / 3)) ^ 3 * (4 / 5)) := Real.exp_le_exp.mpr hyy
  have hXn : 0 < Xp O * nH O := mul_pos (by linarith) (by linarith)
  have hwpp : wpp O = O.b / (Xp O * nH O) := by
    unfold wpp aa
    have : O.x ≠ 0 := hxp.ne'
    have : Xp O ≠ 0 := by linarith
    have : nH O ≠ 0 := by linarith
    field_simp
  have hkS : O.k * O.Se ≤ 2 * wpp O := by
    have a1 : O.k * O.Sc ≤ wpp O := h14.1
    have a2 : O.k * O.eta ≤ wpp O := by
      have h' : O.eta * O.b ^ ((4 : ℝ) / 5) ≤ wpp O := h011
      have : O.k * O.eta ≤ O.b ^ ((4 : ℝ) / 5) * O.eta := mul_le_mul_of_nonneg_right hkb hSg.2
      linarith
    show O.k * (O.Sc + O.eta) ≤ _
    linarith
  have hexp : 2 * O.L ≤ Xp O * nH O := by
    rw [hy3]
    exact two_cube_le _ _ hy0 hn4
  have hkSL : O.k * O.Se * O.L ≤ O.m * O.b := by
    have hL0 : 0 ≤ O.L := by linarith
    calc O.k * O.Se * O.L ≤ 2 * wpp O * O.L := mul_le_mul_of_nonneg_right hkS hL0
      _ = O.b * (2 * O.L) / (Xp O * nH O) := by rw [hwpp]; ring
      _ ≤ O.b * (Xp O * nH O) / (Xp O * nH O) := by
          apply div_le_div_of_nonneg_right _ hXn.le
          exact mul_le_mul_of_nonneg_left hexp hbpos.le
      _ = O.b := by field_simp
      _ = 1 * O.b := by ring
      _ ≤ O.m * O.b := mul_le_mul_of_nonneg_right (by linarith) hbpos.le
  have hX2 : O.k ≤ O.X2 := by
    rw [tX2, hwpp]
    unfold aa
    have e : O.x * O.b / (O.b / (Xp O * nH O)) = (O.x * nH O) * Xp O := by
      field_simp
    rw [e]
    have hxn : 1 ≤ O.x * nH O := by nlinarith
    calc O.k ≤ Xp O := hkX
      _ = 1 * Xp O := by ring
      _ ≤ (O.x * nH O) * Xp O := mul_le_mul_of_nonneg_right hxn (le_trans zero_le_one hXp)
  exact ⟨fun j => wt_bound O hW j, hY1, hlogY, hYmb, hkSL, hX2, hlogk, le_trans (by norm_num : (1 : ℝ) ≤ 10) hL⟩
end Formalism.L2.Indef.Tree.OnPage
