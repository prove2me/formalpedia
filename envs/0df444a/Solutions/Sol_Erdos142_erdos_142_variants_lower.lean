-- Prove2me | solution 1 for Erdos142.erdos_142_variants_lower
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T08:52:09.068553+00:00
-- url     : https://prove2.me/submissions/d787adf1-50bf-42b0-90df-f002cae83f11
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos142Basic
import Theorems.Thm_OAI_Erdos3_manuscriptQuantitativeDensityTheorem
import Theorems.Thm_Erdos142_apFree_iff

open Filter Asymptotics

namespace Erdos142Lower

/-- For `k ≥ 2`, `r k N` is at most OpenAI's `extremalNumber k N`. -/
theorem r_le_extremalNumber (k N : ℕ) (hk : 2 ≤ k) :
    Erdos142.r k N ≤ OAI.Erdos3.extremalNumber k N := by
  classical
  unfold Erdos142.r
  refine csSup_le ⟨0, ∅, by simp,
    by simpa using Erdos142.isAPOfLengthFree_empty (α := ℕ) k, rfl⟩ ?_
  rintro m ⟨S, hS, hfree, rfl⟩
  have hap : Erdos142.APFree k S := (Erdos142.apFree_iff k hk S).2 hfree
  unfold OAI.Erdos3.extremalNumber
  apply Finset.le_sup (f := Finset.card)
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hS, fun h => hap h⟩

/-- A set free of 2-term progressions has at most one element. -/
theorem extremalNumber_two_le (N : ℕ) : OAI.Erdos3.extremalNumber 2 N ≤ 1 := by
  classical
  unfold OAI.Erdos3.extremalNumber
  refine Finset.sup_le ?_
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hne
  apply hS.2
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨a, b - a, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using ha
    · simpa [Nat.add_sub_cancel' h.le] using hb
  · refine ⟨b, a - b, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using hb
    · simpa [Nat.add_sub_cancel' h.le] using ha

/-- `L - c L^(1+η) → -∞`. -/
theorem tendsto_sub_rpow (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    Tendsto (fun L : ℝ => L - c * L ^ (1 + η)) atTop atBot := by
  have h1 : Tendsto (fun L : ℝ => c * L ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).const_mul_atTop hc
  have hev : ∀ᶠ L : ℝ in atTop, L - c * L ^ (1 + η) ≤ -L := by
    filter_upwards [h1.eventually_ge_atTop 2, eventually_gt_atTop (0 : ℝ)] with L h2 hL
    rw [Real.rpow_add hL, Real.rpow_one]
    nlinarith
  exact tendsto_atBot_mono' atTop hev tendsto_neg_atTop_atBot

/-- The quantitative bound is `o(x / log x)`. -/
theorem bound_isLittleO (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    (fun x : ℝ => x * Real.exp (-c * (Real.log (Real.log x)) ^ (1 + η))) =o[atTop]
      (fun x : ℝ => x / Real.log x) := by
  have hL : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hh : Tendsto (fun x : ℝ => Real.exp (Real.log (Real.log x) -
      c * (Real.log (Real.log x)) ^ (1 + η))) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_sub_rpow c η hc hη).comp hL)
  have ho : (fun x : ℝ => Real.exp (Real.log (Real.log x) -
      c * (Real.log (Real.log x)) ^ (1 + η))) =o[atTop] (fun _ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 hh
  have := (isBigO_refl (fun x : ℝ => x / Real.log x) atTop).mul_isLittleO ho
  simp only [mul_one] at this
  refine this.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  rw [Real.exp_sub, Real.exp_log hlog, neg_mul, Real.exp_neg]
  field_simp

end Erdos142Lower

namespace Erdos142

open Erdos142Lower in
theorem erdos_142_variants_lower_aux (k : ℕ) (hk : 1 < k) :
    (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  rcases Nat.lt_or_ge k 3 with h2 | h3
  · obtain rfl : k = 2 := by omega
    have hone : (fun N => (r 2 N : ℝ)) =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
      refine IsBigO.of_bound 1 (Eventually.of_forall fun N => ?_)
      have := (r_le_extremalNumber 2 N le_rfl).trans (extremalNumber_two_le N)
      simp only [Real.norm_natCast, norm_one, one_mul]
      exact_mod_cast this
    refine hone.trans_isLittleO ?_
    have hreal : (fun _ : ℝ => (1 : ℝ)) =o[atTop] (fun x : ℝ => x / Real.log x) := by
      have := Real.isLittleO_log_id_atTop.mul_isBigO
        (isBigO_refl (fun x : ℝ => (Real.log x)⁻¹) atTop)
      refine this.congr' ?_ ?_
      · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
        exact mul_inv_cancel₀ (Real.log_pos hx).ne'
      · exact Eventually.of_forall fun x => by simp [div_eq_mul_inv]
    exact hreal.comp_tendsto hcast
  · obtain ⟨C, c, η, hC, hc, hη, hbound⟩ := OAI.Erdos3.manuscriptQuantitativeDensityTheorem k h3
    have hb := (bound_isLittleO c η hc hη).comp_tendsto hcast
    refine IsBigO.trans_isLittleO ?_ hb
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop 3] with N hN
    have h1 := hbound N hN
    have h2 : (r k N : ℝ) ≤ OAI.Erdos3.extremalNumber k N := by
      exact_mod_cast r_le_extremalNumber k N (by omega)
    have h3 : 0 ≤ (N : ℝ) * Real.exp (-c * Real.log (Real.log N) ^ (1 + η)) := by positivity
    simp only [Function.comp, Real.norm_eq_abs, abs_of_nonneg h3, Nat.abs_cast]
    linarith

end Erdos142

open Erdos142 in
theorem solution (k : ℕ) (hk : 1 < k) : (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log) :=
  Erdos142.erdos_142_variants_lower_aux k hk
