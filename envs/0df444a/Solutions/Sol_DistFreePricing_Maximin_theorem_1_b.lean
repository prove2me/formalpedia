-- Prove2me | solution 1 for DistFreePricing.Maximin.theorem_1_b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:32:26.884299+00:00
-- url     : https://prove2.me/submissions/ab7529b4-169f-4a89-b4d5-33cf9cbde513

import Mathlib
import Definitions.Def_DistFreePricing_Maximin_Setting
import Theorems.Thm_DistFreePricing_Maximin_eq_OA_3
import Theorems.Thm_DistFreePricing_Maximin_kStar_le
import Theorems.Thm_DistFreePricing_Maximin_eq_OA_4_cardano
import Theorems.Thm_DistFreePricing_Maximin_eq_OA_5

open MeasureTheory DistFreePricing.Maximin

theorem solution (c μ σ : ℝ) (hc : 0 ≤ c) (hcμ : c ≤ μ) (hσ : 0 < σ) :
    0 ≤ kStar (tau c μ σ) ∧
    ∀ F ∈ valClass μ σ, lowerL c μ σ ≤ profit c (pStar c μ σ) F := by
  have ht0 : 0 ≤ tau c μ σ := div_nonneg (by linarith) hσ.le
  have hk0 : 0 ≤ kStar (tau c μ σ) := (eq_OA_4_cardano (tau c μ σ) ht0).2.2.2.2
  refine ⟨hk0, ?_⟩
  intro F hF
  obtain ⟨hkle, hle2, _⟩ := kStar_le c μ σ hc hcμ hσ
  have hkτ : kStar (tau c μ σ) ≤ tau c μ σ := le_trans hkle hle2
  have h3 := eq_OA_3 c μ σ hc hcμ hσ (kStar (tau c μ σ)) hk0 hkτ F hF
  unfold pStar
  refine le_trans (le_of_eq ?_) h3
  have htσ : tau c μ σ * σ = μ - c := by unfold tau; field_simp
  set t := tau c μ σ with ht
  set K := kStar t with hK
  rcases ht0.lt_or_eq with htp | hteq
  · have h5 := (eq_OA_5 t htp).2.2.2
    unfold phi at h5
    rw [← hK] at h5
    unfold lowerL
    rw [← ht, ← hK, ← h5]
    rw [show μ = t * σ + c by linarith]
    field_simp
    ring
  · have hK0 : K = 0 := by
      have : K ≤ 2 * t / 3 := hkle
      rw [← hteq] at this; linarith
    have hμc : μ - c = 0 := by rw [← htσ, ← hteq]; ring
    unfold lowerL
    rw [← ht, ← hK, hK0]
    have : μ = c := by linarith
    rw [this]; ring
