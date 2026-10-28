-- Prove2me | solution 1 for FrictionInvest.Benefit.loan_pricing
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T04:35:16.611141+00:00
-- url     : https://prove2.me/submissions/fc9ec576-a133-4e1a-952c-ae01ed0dfda0

import Mathlib
import Definitions.Def_FrictionInvest_Benefit_Model

namespace Aux_FIBlp
open FrictionInvest.Benefit

lemma receipt_formula (P : Params) (hp : 0 < P.p) (ha : 0 < P.a) (γ q F : ℝ) (hF0 : 0 ≤ F)
    (hFq : F < q * P.p) (hFa : F / P.p ≤ P.a) :
    bankReceipt P γ q F = F - (1 + γ) * F ^ 2 / (2 * P.a * P.p) := by
  have hb0 : 0 ≤ F / P.p := div_nonneg hF0 hp.le
  have hbq : F / P.p < q := by rw [div_lt_iff₀ hp]; exact hFq
  set g : ℝ → ℝ := fun ξ => min (revenue P q ξ) F - γ * revenue P q ξ *
      (if revenue P q ξ ≤ F then 1 else 0) with hg
  have heq1 : Set.EqOn g (fun ξ => (1 - γ) * P.p * ξ) (Set.uIoc 0 (F / P.p)) := by
    intro ξ hξ
    rw [Set.uIoc_of_le hb0] at hξ
    have hξq : ξ ≤ q := hξ.2.trans hbq.le
    have hrev : revenue P q ξ = P.p * ξ := by simp [revenue, min_eq_right hξq]
    have hle : P.p * ξ ≤ F := by
      have := hξ.2; rw [le_div_iff₀ hp] at this; linarith
    simp only [hg, hrev, if_pos hle, min_eq_left hle]
    ring
  have heq2 : Set.EqOn g (fun _ => F) (Set.uIoc (F / P.p) P.a) := by
    intro ξ hξ
    rw [Set.uIoc_of_le hFa] at hξ
    have hgt : F < revenue P q ξ := by
      unfold revenue
      rcases le_total q ξ with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]
        have := hξ.1; rw [div_lt_iff₀ hp] at this; linarith
    simp only [hg, if_neg (not_le.2 hgt), min_eq_right hgt.le]
    ring
  have hi1 : IntervalIntegrable g MeasureTheory.volume 0 (F / P.p) :=
    (intervalIntegrable_congr heq1).2 ((continuous_const.mul continuous_id).intervalIntegrable _ _)
  have hi2 : IntervalIntegrable g MeasureTheory.volume (F / P.p) P.a :=
    (intervalIntegrable_congr heq2).2 (continuous_const.intervalIntegrable _ _)
  unfold bankReceipt
  rw [← hg, ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => heq1 hx)),
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => heq2 hx)),
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

end Aux_FIBlp

open FrictionInvest.Benefit Aux_FIBlp in
theorem solution (P : Params) (hp : 0 < P.p) (ha : 0 < P.a)
    (γ c y q : ℝ) (hγ : 0 ≤ γ ∧ γ ≤ 1) (hc : 0 < c) (hy : 0 ≤ y)
    (hq : 0 ≤ q) (hborrow : y < c * q)
    (hbound : 2 * (1 + γ) * (c * q - y) < P.a * P.p)
    (hloan : faceValue P γ c y q < q * P.p) :
    0 < faceValue P γ c y q ∧
    (1 + γ) * faceValue P γ c y q < P.a * P.p ∧
    bankReceipt P γ q (faceValue P γ c y q) = c * q - y ∧
    ∀ F' : ℝ, 0 ≤ F' → (1 + γ) * F' < P.a * P.p → F' < q * P.p →
      bankReceipt P γ q F' = c * q - y → F' = faceValue P γ c y q := by
  have hap : 0 < P.a * P.p := mul_pos ha hp
  have hγ1 : 0 < 1 + γ := by linarith
  set D := c * q - y with hD
  have hDpos : 0 < D := by linarith
  set t := 2 * (1 + γ) * D / (P.a * P.p) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one hap]; exact hbound
  set u := Real.sqrt (1 - t) with hu
  have hu2 : u ^ 2 = 1 - t := Real.sq_sqrt (by linarith)
  have hu0 : 0 < u := Real.sqrt_pos.2 (by linarith)
  have hu1 : u < 1 := by nlinarith
  have hF : faceValue P γ c y q = P.a * P.p / (1 + γ) * (1 - u) := by
    unfold faceValue
    rw [if_neg (not_le.2 hborrow)]
  set F := faceValue P γ c y q with hFdef
  have hFpos : 0 < F := by rw [hF]; apply mul_pos (div_pos hap hγ1); linarith
  have hFb : (1 + γ) * F < P.a * P.p := by
    rw [hF]; field_simp; nlinarith
  have hFa : F / P.p ≤ P.a := by
    rw [div_le_iff₀ hp]
    have : F ≤ (1 + γ) * F := by nlinarith
    linarith
  have hrec : ∀ F' : ℝ, 0 ≤ F' → (1 + γ) * F' < P.a * P.p → F' < q * P.p →
      bankReceipt P γ q F' = F' - (1 + γ) * F' ^ 2 / (2 * P.a * P.p) := by
    intro F' h0 h1 h2
    apply receipt_formula P hp ha γ q F' h0 h2
    rw [div_le_iff₀ hp]
    have : F' ≤ (1 + γ) * F' := by nlinarith
    linarith
  -- F solves the quadratic
  have hquad : F - (1 + γ) * F ^ 2 / (2 * P.a * P.p) = D := by
    rw [hF]
    have htD : D = t * (P.a * P.p) / (2 * (1 + γ)) := by
      rw [ht]; field_simp
    rw [htD]
    field_simp
    nlinarith [hu2]
  refine ⟨hFpos, hFb, ?_, ?_⟩
  · rw [hrec F hFpos.le hFb hloan, hquad]
  · intro F' h0 h1 h2 h3
    rw [hrec F' h0 h1 h2] at h3
    -- both F and F' solve (1+γ) X^2 - 2ap X + 2ap D = 0
    have e1 : (1 + γ) * F' ^ 2 - 2 * (P.a * P.p) * F' + 2 * (P.a * P.p) * D = 0 := by
      field_simp at h3; linarith
    have e2 : (1 + γ) * F ^ 2 - 2 * (P.a * P.p) * F + 2 * (P.a * P.p) * D = 0 := by
      have := hquad; field_simp at this; linarith
    have hfac : (F' - F) * ((1 + γ) * (F' + F) - 2 * (P.a * P.p)) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.1 hfac with h | h
    · linarith
    · exfalso
      nlinarith
