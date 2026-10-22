-- Prove2me | solution 1 for CropMSP.MarketUnc.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:44:34.876772+00:00
-- url     : https://prove2.me/submissions/6a1fb22b-7763-49ed-9c29-d7a3203a8812

import Mathlib
import Definitions.Def_CropMSP_MarketUnc_Model
import Theorems.Thm_CropMSP_MarketUnc_theorem_1
import Theorems.Thm_CropMSP_MarketUnc_b_identity
import Theorems.Thm_CropMSP_MarketUnc_v_identity

open CropMSP.MarketUnc

theorem solution (P : Params) (hS : P.Standing) :
    (P.a ≤ 3 / 2 → ∀ m q, IsEquilibrium P m q → Admissible P m q →
      tau0 P ≤ m → m ≤ 1 → (0 ≤ netBenefit P m q ↔ m ≤ 2 * P.a / 3)) ∧
    (∃ qB, IsEquilibrium P (max (tau0 P) (min 1 (P.a / 3))) qB ∧
      Admissible P (max (tau0 P) (min 1 (P.a / 3))) qB ∧
      ∀ m q, IsEquilibrium P m q → Admissible P m q →
        netBenefit P m q ≤
          netBenefit P (max (tau0 P) (min 1 (P.a / 3))) qB) ∧
    (∀ m q m' q', IsEquilibrium P m q → Admissible P m q →
      IsEquilibrium P m' q' → Admissible P m' q' →
      ((m ≤ tau0 P ∧ m' ≤ tau0 P) ∨ (1 ≤ m ∧ 1 ≤ m')) →
      netBenefit P m q = netBenefit P m' q') ∧
    (∀ m q, IsEquilibrium P m q → Admissible P m q →
      0 < netSocialValue P m q) ∧
    (∃ qV, IsEquilibrium P (min 1 (P.a / 2)) qV ∧
      Admissible P (min 1 (P.a / 2)) qV ∧
      ∀ m q, IsEquilibrium P m q → Admissible P m q →
        netSocialValue P m q ≤
          netSocialValue P (min 1 (P.a / 2)) qV) := by
  obtain ⟨hα0, hα1, hθ, ha, ht1⟩ := hS
  have hS' : P.Standing := ⟨hα0, hα1, hθ, ha, ht1⟩
  have ht0def : tau0 P = (P.a - (1 - 2 * P.α) * P.θ) / 2 := rfl
  have hprod : 0 < (1 - 2 * P.α) * P.θ := mul_pos (by linarith) hθ
  have hprod2 : (1 - 2 * P.α) * P.θ < P.θ := by nlinarith
  have ht0pos : 1 / 2 < tau0 P := by rw [ht0def]; linarith
  have ht0lo : P.a - P.θ ≤ 2 * tau0 P := by rw [ht0def]; linarith
  have ht0hi : 2 * tau0 P ≤ P.a := by rw [ht0def]; linarith
  -- bounds on tau
  have htau_lo : ∀ m, tau0 P ≤ tau P m := by
    intro m; unfold tau
    exact le_min ht1.le (le_max_right _ _)
  have htau_hi : ∀ m, tau P m ≤ 1 := fun m => min_le_left _ _
  have htau_eq : ∀ m, tau0 P ≤ m → m ≤ 1 → tau P m = m := by
    intro m h1 h2; unfold tau; rw [max_eq_left h1, min_eq_right h2]
  have hB := fun m q h1 h2 => b_identity P hS' m q h1 h2
  have hV := fun m q h1 h2 => v_identity P hS' m q h1 h2
  -- the optimizers
  set mB := max (tau0 P) (min 1 (P.a / 3)) with hmB
  set mV := min 1 (P.a / 2) with hmV
  have hmB_lo : tau0 P ≤ mB := le_max_left _ _
  have hmB_hi : mB ≤ 1 := max_le ht1.le (min_le_left _ _)
  have hmV_hi : mV ≤ 1 := min_le_left _ _
  have hmV_lo : tau0 P ≤ mV := le_min ht1.le (by linarith)
  have htB : tau P mB = mB := htau_eq mB hmB_lo hmB_hi
  have htV : tau P mV = mV := htau_eq mV hmV_lo hmV_hi
  have hAdmB : Admissible P mB (tau P mB) := by
    rw [htB]; constructor
    · linarith
    · have : mB ≤ tau0 P ∨ mB ≤ P.a / 3 := by
        rcases le_total (tau0 P) (min 1 (P.a / 3)) with h | h
        · right; rw [hmB, max_eq_right h]; exact min_le_right _ _
        · left; rw [hmB, max_eq_left h]
      rcases this with h | h <;> linarith
  have hAdmV : Admissible P mV (tau P mV) := by
    rw [htV]; constructor
    · rcases le_total 1 (P.a / 2) with h | h
      · rw [hmV, min_eq_left h]; rw [ht0def] at ht1; linarith
      · rw [hmV, min_eq_right h]; linarith
    · have : mV ≤ P.a / 2 := min_le_right _ _
      linarith
  have hEqB := (theorem_1 P hS' mB hAdmB).1
  have hEqV := (theorem_1 P hS' mV hAdmV).1
  refine ⟨?_, ⟨tau P mB, hEqB, hAdmB, ?_⟩, ?_, ?_, ⟨tau P mV, hEqV, hAdmV, ?_⟩⟩
  · intro _ m q h1 h2 hm1 hm2
    rw [hB m q h1 h2, htau_eq m hm1 hm2]
    have hm : 0 < m := by linarith
    constructor
    · intro h
      by_contra hc
      push Not at hc
      nlinarith
    · intro h; nlinarith
  · intro m q h1 h2
    rw [hB m q h1 h2, hB mB _ hEqB hAdmB, htB]
    have l := htau_lo m
    have u := htau_hi m
    set t := tau P m
    rcases le_total (tau0 P) (min 1 (P.a / 3)) with h | h
    · rw [hmB, max_eq_right h] at *
      rcases le_total 1 (P.a / 3) with h' | h'
      · rw [min_eq_left h']
        nlinarith
      · rw [min_eq_right h']
        nlinarith [sq_nonneg (t - P.a / 3)]
    · rw [hmB, max_eq_left h] at *
      have : P.a / 3 ≤ tau0 P := by
        rcases le_total 1 (P.a / 3) with h' | h'
        · rw [min_eq_left h'] at h; linarith
        · rw [min_eq_right h'] at h; exact h
      nlinarith
  · intro m q m' q' h1 h2 h3 h4 hc
    rw [hB m q h1 h2, hB m' q' h3 h4]
    have : tau P m = tau P m' := by
      rcases hc with ⟨hm, hm'⟩ | ⟨hm, hm'⟩
      · unfold tau; rw [max_eq_right hm, max_eq_right hm']
      · unfold tau
        rw [min_eq_left (le_trans hm (le_max_left _ _)),
          min_eq_left (le_trans hm' (le_max_left _ _))]
    rw [this]
  · intro m q h1 h2
    rw [hV m q h1 h2]
    have l := htau_lo m
    have u := htau_hi m
    apply mul_pos <;> linarith
  · intro m q h1 h2
    rw [hV m q h1 h2, hV mV _ hEqV hAdmV, htV]
    have l := htau_lo m
    have u := htau_hi m
    set t := tau P m
    rcases le_total 1 (P.a / 2) with h' | h'
    · rw [hmV, min_eq_left h']
      nlinarith
    · rw [hmV, min_eq_right h']
      nlinarith [sq_nonneg (t - P.a / 2)]
