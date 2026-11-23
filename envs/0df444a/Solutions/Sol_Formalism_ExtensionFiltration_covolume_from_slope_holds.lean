-- Prove2me | solution 1 for Formalism.ExtensionFiltration.covolume_from_slope_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:08.10092+00:00
-- url     : https://prove2.me/submissions/13538dc1-8714-4127-a01c-deffc5933035

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeIntoDivisionHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_Assembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module NumberField
open Formalism Formalism.ExtensionFiltration
namespace Formalism.ExtensionFiltration
theorem _root_.solution : CovolumeFromSlope := by
  intro Pl _ w c1 ua lcvD C Cc pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η
    hmain hc1 hua hw hkS hkη hcard hm hf hq0 hqm hx heps hL hb hrd hrdL hchi0 hchiL hlx hll hLL0 hB0 hC hCc
  have hL1 : 1 ≤ L := by rw [hL]; exact Real.one_le_rpow hx heps.le
  have hb1 : 1 ≤ b := by rw [hb]; exact Real.one_le_exp (by linarith)
  have hb0 : 0 < b := by linarith
  have hrd0 : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have hlogb : Real.log (b * rd) = L + Real.log rd := by
    rw [Real.log_mul (by positivity) (by positivity), hb, Real.log_exp]
  have hB0' : B0 = f * m * b * L := by rw [hB0, hL]
  have hfmb : 0 ≤ f * m * b := by positivity
  have hn0 : (0 : ℝ) ≤ (Fintype.card Pl : ℝ) := by positivity

  have hW : (∑ τ, w τ) ≤ 2 * (f * b) := by
    calc (∑ τ, w τ) ≤ ∑ _τ : Pl, 2 * b := Finset.sum_le_sum (fun τ _ => (hw τ).2)
      _ = (Fintype.card Pl : ℝ) * (2 * b) := by simp
      _ ≤ f * (2 * b) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * (f * b) := by ring
  have hW0 : 0 ≤ ∑ τ, w τ := Finset.sum_nonneg (fun τ _ => (hw τ).1)
  have hU0 : 0 ≤ ∑ τ, ua τ := Finset.sum_nonneg (fun τ _ => (hua τ).1)
  have hU : (∑ τ, ua τ) ≤ 8 * (f * m * b) := by
    have h1 : ∀ τ, ua τ ≤ 8 * (m * b) := by
      intro τ
      have h2 := (hua τ).2
      have h3 : m * w τ ≤ m * (2 * b) := mul_le_mul_of_nonneg_left (hw τ).2 (by linarith)
      have h4 : b ≤ m * b := le_mul_of_one_le_left hb0.le hm
      linarith
    calc (∑ τ, ua τ) ≤ ∑ _τ : Pl, 8 * (m * b) := Finset.sum_le_sum (fun τ _ => h1 τ)
      _ = (Fintype.card Pl : ℝ) * (8 * (m * b)) := by simp
      _ ≤ f * (8 * (m * b)) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 8 * (f * m * b) := by ring

  set E : ℝ := Cc * q' * (Real.log rd + Lchi) with hE
  have hE0 : 0 ≤ E := by positivity
  have hEle : E ≤ Cc * m * (2 * L) := by
    have : Cc * q' ≤ Cc * m := mul_le_mul_of_nonneg_left hqm hCc
    exact mul_le_mul this (by linarith) (by linarith) (by positivity)
  have hsum : -(2 * ∑ τ, w τ * c1 τ) ≤ (∑ ρ, pq * w ρ * logOm) + 2 * (E * ∑ τ, w τ) := by
    have h1 : ∀ τ, -(pq * w τ * logOm) / 2 - E * w τ ≤ w τ * c1 τ := by
      intro τ
      have h2 := (abs_le.mp (hc1 τ)).1
      have h3 : w τ * (-E) ≤ w τ * (c1 τ + pq * logOm / 2) :=
        mul_le_mul_of_nonneg_left h2 (hw τ).1
      have e1 : w τ * (-E) = -(E * w τ) := by ring
      have e2 : w τ * (c1 τ + pq * logOm / 2) = w τ * c1 τ + (pq * w τ * logOm) / 2 := by ring
      rw [e1, e2] at h3
      linarith
    have h4 : ∑ τ, (-(pq * w τ * logOm) / 2 - E * w τ) ≤ ∑ τ, w τ * c1 τ :=
      Finset.sum_le_sum (fun τ _ => h1 τ)
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_neg_distrib, ← Finset.mul_sum] at h4
    linarith
  have hEW : E * (∑ τ, w τ) ≤ Cc * m * (2 * L) * (2 * (f * b)) :=
    mul_le_mul hEle hW hW0 (by positivity)

  have hLLle : LL0 ≤ 4 * (L * llx) := by
    rw [hLL0, hlogb]
    have h1 : (L + Real.log rd) * llx ≤ (2 * L) * llx :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : L ≤ L * llx := le_mul_of_one_le_right (by linarith) hll
    linarith
  have hLU : LL0 * (∑ τ, ua τ) ≤ 4 * (L * llx) * (8 * (f * m * b)) :=
    mul_le_mul hLLle hU hU0 (by positivity)
  have hCLU : C * (LL0 * (∑ τ, ua τ)) ≤ C * (4 * (L * llx) * (8 * (f * m * b))) :=
    mul_le_mul_of_nonneg_left hLU hC
  have hBll : B0 ≤ B0 * llx := by
    have : 0 ≤ B0 := by rw [hB0']; positivity
    exact le_mul_of_one_le_right this hll
  have hbB : b ≤ B0 := by
    rw [hB0']
    have h1 : 1 ≤ f * m := one_le_mul_of_one_le_of_one_le hf hm
    have h2 : b ≤ f * m * b := le_mul_of_one_le_left hb0.le h1
    exact le_trans h2 (le_mul_of_one_le_right hfmb hL1)
  have hCcB : Cc * B0 ≤ Cc * (B0 * llx) := mul_le_mul_of_nonneg_left hBll hCc
  have e1 : Cc * m * (2 * L) * (2 * (f * b)) = 4 * (Cc * B0) := by rw [hB0']; ring
  have e2 : C * (4 * (L * llx) * (8 * (f * m * b))) = 32 * (C * (B0 * llx)) := by rw [hB0']; ring
  rw [e1] at hEW
  rw [e2] at hCLU
  clear_value E
  linarith
end Formalism.ExtensionFiltration
