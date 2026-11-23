-- Prove2me | solution 1 for Formalism.DivisionValues.error_absorption
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:19.921989+00:00
-- url     : https://prove2.me/submissions/2e0c425e-d773-47ab-83bd-cd6e3184db8b

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementE
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AbsorbE
import Theorems.Thm_Formalism_DivisionValues_absE_ssum_le
import Theorems.Thm_Formalism_DivisionValues_absE_dsum_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
set_option maxHeartbeats 800000
namespace Formalism.DivisionValues
theorem _root_.solution : AbsorbE := by
  intro J Pl _ _ TT _ x eps L b a rd La B0 Nc xe m f k N S t η w'' b' dC lam0 C0 Lpass Eb e6 eP
    logOm kk eK pq w eE δ hx heps hL hb ha hrd hrdL hxL hLa hB0 hNc hxe hJ hPl hm hf hk hN hS ht
    hη hdC hw hpq hOm hlam0 hNd hmNL hmηNL hkN hkS hmtη hNw hb'N hmkb' hC0 hLpass hEb heK he6 heP
    heE hδ

  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ L := by rw [hL]; exact Real.one_le_rpow hx heps.le
  have hb1 : 1 ≤ b := by rw [hb]; exact Real.one_le_exp (by linarith)
  have hb0 : 0 < b := by linarith
  have hrd0 : 0 < rd := by linarith
  have ha0 : 0 < a := by rw [ha]; exact mul_pos hx0 hb0
  have hLa_eq : La = Real.log x + L + Real.log rd := by
    rw [hLa, Real.log_mul ha0.ne' hrd0.ne', ha, Real.log_mul hx0.ne' hb0.ne', hb, Real.log_exp]
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlrd : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have hLa0 : 0 ≤ La := by rw [hLa_eq]; linarith
  have hLa3 : La ≤ 3 * L := by rw [hLa_eq]; linarith
  rw [← hL] at hxe hB0
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hf0 : (0 : ℝ) ≤ f := by linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hfmbL : 0 ≤ f * m * b * L := mul_nonneg (mul_nonneg (mul_nonneg hf0 hm0) hb0.le) hL0
  have hB0n : 0 ≤ B0 := by rw [hB0]; exact hfmbL
  have hT2n : 0 ≤ m * (B0 + Nc) * xe := mul_nonneg (mul_nonneg hm0 (by linarith)) (by linarith)

  have hFM2 : m * (f * m * b * L) ≤ m * (B0 + Nc) * xe := by
    have h1 : m * B0 ≤ m * (B0 + Nc) := mul_le_mul_of_nonneg_left (by linarith) hm0
    have h2 : m * (B0 + Nc) * 1 ≤ m * (B0 + Nc) * xe :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hm0 (by linarith))
    have h3 : m * B0 = m * (f * m * b * L) := by rw [hB0]
    linarith
  have hFM : f * m * b * L ≤ m * (B0 + Nc) * xe := by
    have h4 := mul_le_mul_of_nonneg_right hm hfmbL
    linarith
  have hfbL : f * b ≤ f * b * L := by
    have := mul_le_mul_of_nonneg_left hL1 (mul_nonneg hf0 hb0.le); linarith
  have hfb_fmb : f * b * L ≤ f * m * b * L := by
    have := mul_le_mul_of_nonneg_right hm (mul_nonneg (mul_nonneg hf0 hb0.le) hL0); linarith
  have hb_T : b ≤ m * (B0 + Nc) * xe := by
    have h1 : 1 * b ≤ f * b := mul_le_mul_of_nonneg_right hf hb0.le
    linarith
  have hone_T : 1 ≤ m * (B0 + Nc) * xe := by linarith

  have hN2 : N ^ 2 ≤ b := by
    have := mul_le_mul_of_nonneg_left hdC (sq_nonneg N); linarith
  have hN2La : N ^ 2 * La ≤ b * (3 * L) := mul_le_mul hN2 hLa3 hLa0 hb0.le
  have hw''0 : 0 ≤ w'' := by have := mul_nonneg hk0 hS; linarith
  have hSw : S ≤ w'' := by have := mul_le_mul_of_nonneg_right hk hS; linarith
  have hSN : S * N ≤ b := by have := mul_le_mul_of_nonneg_right hSw hN0; linarith
  have hw''b : w'' ≤ b := by have := mul_le_mul_of_nonneg_right hN hw''0; linarith

  have hLp : Lpass ≤ (1 + C0) * (m * (B0 + Nc) * xe) := by
    have h1 := mul_le_mul_of_nonneg_left hlam0 hC0
    have h2 := mul_le_mul_of_nonneg_left hb_T hC0
    linarith
  have hEb' : Eb ≤ C0 * (m * (B0 + Nc) * xe) := by linarith

  have heKs : ∑ j, eK j ≤ 5 * C0 * (m * (B0 + Nc) * xe) := by
    have hs := absE_ssum_le eK _ m hJ heK
    have e1 := mul_le_mul_of_nonneg_left hN2La hf0
    have e2 := mul_le_mul_of_nonneg_left hNd hf0
    have e3 := mul_le_mul_of_nonneg_left hmNL hf0
    have hX : f * N ^ 2 * (La + dC) + f * m ^ 3 * N ^ 2 * L ≤ 3 * (f * b * L) + 2 * (f * b) := by
      linarith
    have hX' := mul_le_mul_of_nonneg_left hX hm0
    have hY : m * (3 * (f * b * L) + 2 * (f * b)) ≤ 5 * (m * (B0 + Nc) * xe) := by
      have := mul_le_mul_of_nonneg_left hfbL hm0
      linarith
    have hZ := mul_le_mul_of_nonneg_left (hX'.trans hY) hC0
    linarith
  have he6' : e6 ≤ 3 * C0 * (m * (B0 + Nc) * xe) := by
    have h1 := mul_le_mul_of_nonneg_left hN2La (mul_nonneg (mul_nonneg hC0 hm0) hf0)
    have h2 := mul_le_mul_of_nonneg_left hFM hC0
    linarith

  have hTTa : (TT.card : ℝ) * b' * N * La ≤ (TT.card : ℝ) * a * La := by
    have hc : (0 : ℝ) ≤ TT.card := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hb'N (mul_nonneg hc hLa0)
    linarith
  have hmηN : m * η * N * La ≤ 3 * b := by
    have h0 : 0 ≤ m * η * N := mul_nonneg (mul_nonneg hm0 hη) hN0
    have := mul_le_mul_of_nonneg_left hLa3 h0
    linarith
  have hSNLa : S * N * La ≤ b * (3 * L) := mul_le_mul hSN hLa3 hLa0 hb0.le
  have heP' : eP ≤ C0 * ((TT.card : ℝ) * a * La) + 9 * C0 * (m * (B0 + Nc) * xe) := by
    have hY : ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La ≤
        (TT.card : ℝ) * a * La + 9 * (f * b * L) := by
      have e1 := mul_le_mul_of_nonneg_left hmηN hf0
      have e2 := mul_le_mul_of_nonneg_left hSNLa hf0
      have e3 := mul_le_mul_of_nonneg_left hN2La hf0
      linarith
    have h1 := mul_le_mul_of_nonneg_left hY hC0
    have h2 := mul_le_mul_of_nonneg_left (hfb_fmb.trans hFM) hC0
    linarith

  have heEs : ∑ j, ∑ ρ, eE j ρ ≤ 15 * C0 * (m * (B0 + Nc) * xe) := by
    have hc : 0 ≤ C0 * (15 * (b * L)) :=
      mul_nonneg hC0 (mul_nonneg (by norm_num) (mul_nonneg hb0.le hL0))
    have hs := absE_dsum_le eE (C0 * (15 * (b * L))) m f hc hJ hPl (fun j ρ => by
      have hwj := hw j ρ
      have hin : w j ρ + S + N ^ 2 + m * (t + 1) * η ≤ 5 * b := by linarith [hwj.2]
      have h1 : (w j ρ + S + N ^ 2 + m * (t + 1) * η) * La ≤ (5 * b) * (3 * L) :=
        mul_le_mul hin hLa3 hLa0 (by linarith)
      have h2 := mul_le_mul_of_nonneg_left h1 hC0
      have h3 := heE j ρ
      linarith)
    have h4 := mul_le_mul_of_nonneg_left hFM hC0
    linarith
  have hpqs : ∑ j, ∑ ρ, |pq j - kk| * |w j ρ| * |logOm| ≤ 6 * (m * (B0 + Nc) * xe) := by
    have hc : 0 ≤ 6 * (m * b * L) := by
      have := mul_nonneg (mul_nonneg hm0 hb0.le) hL0; linarith
    have hs : ∑ j, ∑ ρ, |pq j - kk| * |w j ρ| * |logOm| ≤ m * (f * (6 * (m * b * L))) :=
      absE_dsum_le _ _ m f hc hJ hPl (fun j ρ => by
        have hwj := hw j ρ
        have habs : |w j ρ| ≤ 2 * b := by rw [abs_of_nonneg hwj.1]; exact hwj.2
        have h1 : |pq j - kk| * |w j ρ| ≤ m * (2 * b) :=
          mul_le_mul (hpq j) habs (abs_nonneg _) hm0
        have h2 : |pq j - kk| * |w j ρ| * |logOm| ≤ m * (2 * b) * La :=
          mul_le_mul h1 hOm (abs_nonneg _) (mul_nonneg hm0 (by linarith))
        have h3 : m * (2 * b) * La ≤ m * (2 * b) * (3 * L) :=
          mul_le_mul_of_nonneg_left hLa3 (mul_nonneg hm0 (by linarith))
        linarith)
    have h4 : m * (f * (6 * (m * b * L))) = 6 * (m * (f * m * b * L)) := by ring
    linarith

  have hite : ∀ c : ℝ, ∑ ρ : Pl, (if ρ ∈ TT then c else 0) = (TT.card : ℝ) * c := by
    intro c
    have hfl : Finset.univ.filter (· ∈ TT) = TT := by ext ρ; simp
    rw [← Finset.sum_filter, hfl, Finset.sum_const, nsmul_eq_mul]
  have hδs : ∑ j, ∑ ρ, |δ j ρ| * |logOm| ≤
      C0 * ((TT.card : ℝ) * a * La) + 15 * C0 * (m * (B0 + Nc) * xe) := by
    have hpt : ∀ j ρ, |δ j ρ| * |logOm| ≤
        C0 * (5 * b) * La + (if ρ ∈ TT then C0 * (k * b') * La else 0) := by
      intro j ρ
      have hwj := hw j ρ
      have h1 := hδ j ρ
      have h2 : |δ j ρ| * |logOm| ≤
          C0 * (w j ρ + k * (N + S) + m * (t + 1) * η + (if ρ ∈ TT then k * b' else 0)) * La :=
        mul_le_mul h1 hOm (abs_nonneg _) ((abs_nonneg _).trans h1)
      by_cases hρ : ρ ∈ TT
      · rw [if_pos hρ] at h2 ⊢
        have h3 : w j ρ + k * (N + S) + m * (t + 1) * η + k * b' ≤ 5 * b + k * b' := by
          linarith [hwj.2]
        have h4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hC0) hLa0
        linarith
      · rw [if_neg hρ] at h2 ⊢
        have h3 : w j ρ + k * (N + S) + m * (t + 1) * η + 0 ≤ 5 * b := by linarith [hwj.2]
        have h4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hC0) hLa0
        linarith
    have hsum : ∑ j, ∑ ρ, |δ j ρ| * |logOm| ≤
        ∑ j : J, ∑ ρ : Pl, (C0 * (5 * b) * La + (if ρ ∈ TT then C0 * (k * b') * La else 0)) :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun ρ _ => hpt j ρ))
    have hinner : ∀ j : J, ∑ ρ : Pl, (C0 * (5 * b) * La + (if ρ ∈ TT then C0 * (k * b') * La else 0)) =
        (Fintype.card Pl : ℝ) * (C0 * (5 * b) * La) + (TT.card : ℝ) * (C0 * (k * b') * La) := by
      intro j
      rw [Finset.sum_add_distrib, hite, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hR : ∑ j : J, ∑ ρ : Pl, (C0 * (5 * b) * La + (if ρ ∈ TT then C0 * (k * b') * La else 0)) =
        m * ((Fintype.card Pl : ℝ) * (C0 * (5 * b) * La) + (TT.card : ℝ) * (C0 * (k * b') * La)) := by
      rw [Finset.sum_congr rfl (fun j _ => hinner j), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hJ]
    rw [hR] at hsum
    have hA : 0 ≤ C0 * (5 * b) * La := mul_nonneg (mul_nonneg hC0 (by linarith)) hLa0
    have e1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPl hA) hm0
    have e2 : C0 * (5 * b) * La ≤ C0 * (5 * b) * (3 * L) :=
      mul_le_mul_of_nonneg_left hLa3 (mul_nonneg hC0 (by linarith))
    have e2' := mul_le_mul_of_nonneg_left e2 (mul_nonneg hm0 hf0)
    have e3 := mul_le_mul_of_nonneg_left hmkb'
      (mul_nonneg (mul_nonneg hC0 (Nat.cast_nonneg TT.card)) hLa0)
    have h4 := mul_le_mul_of_nonneg_left hFM hC0
    linarith

  have hT1n : 0 ≤ (TT.card : ℝ) * a * La :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ha0.le) hLa0
  have hC1 := mul_nonneg hC0 hT1n
  have hC2 := mul_nonneg hC0 hT2n
  linarith
end Formalism.DivisionValues
