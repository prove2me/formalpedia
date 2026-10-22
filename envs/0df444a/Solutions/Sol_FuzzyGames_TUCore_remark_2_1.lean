-- Prove2me | solution 1 for FuzzyGames.TUCore.remark_2_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:33:04.57002+00:00
-- url     : https://prove2.me/submissions/00793e36-a612-484b-b19c-a78a403a293a

import Mathlib
import Definitions.Def_FuzzyGames_TUCore_Basic

set_option autoImplicit false
open FuzzyGames.TUCore

theorem solution {n : ℕ} (v : (Fin n → ℝ) → ℝ) (hv : IsFuzzyTUGame v) :
    ConcaveOn ℝ (Set.Ici (0 : Fin n → ℝ)) v ↔
      ∀ τ σ : Fin n → ℝ, 0 ≤ τ → 0 ≤ σ → v (τ + σ) ≥ v τ + v σ := by
  obtain ⟨h0, hh⟩ := hv
  constructor
  · intro hc τ σ hτ hσ
    have hτ' : τ ∈ Set.Ici (0 : Fin n → ℝ) := hτ
    have hσ' : σ ∈ Set.Ici (0 : Fin n → ℝ) := hσ
    have hmid := hc.2 hτ' hσ' (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num)
    have hx : (0 : Fin n → ℝ) ≤ (1/2 : ℝ) • τ + (1/2 : ℝ) • σ := by
      have := smul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) hτ
      have := smul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) hσ
      positivity
    have h2 := hh 2 (by norm_num) _ hx
    have e : (2:ℝ) • ((1/2 : ℝ) • τ + (1/2 : ℝ) • σ) = τ + σ := by
      rw [smul_add, smul_smul, smul_smul]; norm_num
    rw [e] at h2
    simp only [smul_eq_mul] at hmid
    linarith
  · intro hs
    refine ⟨convex_Ici _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hx' : 0 ≤ x := hx
    have hy' : 0 ≤ y := hy
    have hax : 0 ≤ a • x := smul_nonneg ha hx'
    have hby : 0 ≤ b • y := smul_nonneg hb hy'
    have h1 := hs _ _ hax hby
    have hva : v (a • x) = a * v x := by
      rcases ha.eq_or_lt with rfl | hpos
      · simp [h0]
      · exact hh a hpos x hx'
    have hvb : v (b • y) = b * v y := by
      rcases hb.eq_or_lt with rfl | hpos
      · simp [h0]
      · exact hh b hpos y hy'
    simp only [smul_eq_mul]
    rw [hva, hvb] at h1
    linarith
