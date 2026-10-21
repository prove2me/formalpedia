-- Prove2me | solution 1 for DynOpaque.TwoPeriod.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T02:06:02.3884+00:00
-- url     : https://prove2.me/submissions/c51b6b90-caf4-43c1-9a32-812c49ce67e3

import Mathlib
import Definitions.Def_DynOpaque_TwoPeriod_Model

namespace DynOpaqueLemma1Aux
open DynOpaque.TwoPeriod

theorem est1 : estimate 1 = 1 / 2 := by simp [estimate, estimateK]; norm_num
theorem est0 : estimate 0 = 0 := by simp [estimate, estimateK]

/-- Lemma 1-type price reduction for one period. -/
theorem term_le (vH vL cH cL h ξ p : ℝ) (hv : vL < vH) (hp : p ≤ vHL vH vL) (hh : 0 ≤ h) :
    frac vH vL h p * margin cH cL ξ p ≤ frac vH vL h vL * margin cH cL ξ vL ∨
    frac vH vL h p * margin cH cL ξ p ≤
      frac vH vL h (vHL vH vL) * margin cH cL ξ (vHL vH vL) := by
  have hp' : p ≤ 1 / 2 * vH + (1 - 1 / 2) * vL := by unfold vHL at hp; linarith
  have hvl : 1 / 2 * vH + (1 - 1 / 2) * vL ≥ vL := by linarith
  have hvhl : ¬ (0 * vH + (1 - 0) * vL ≥ vHL vH vL) := by unfold vHL; intro h; linarith
  have hvhl2 : 1 / 2 * vH + (1 - 1 / 2) * vL ≥ vHL vH vL := by unfold vHL; linarith
  by_cases hpl : p ≤ vL
  · left
    have h1 : 0 * vH + (1 - 0) * vL ≥ p := by linarith
    have h2 : 0 * vH + (1 - 0) * vL ≥ vL := by linarith
    simp only [frac, buys, est1, est0, if_pos hp', if_pos h1, if_pos hvl, if_pos h2, margin]
    nlinarith
  · right
    have h1 : ¬ (0 * vH + (1 - 0) * vL ≥ p) := by intro h; apply hpl; linarith
    simp only [frac, buys, est1, est0, if_pos hp', if_neg h1, if_pos hvhl2, if_neg hvhl, margin]
    nlinarith


theorem frac_vHL (vH vL h : ℝ) (hv : vL < vH) : frac vH vL h (vHL vH vL) = h := by
  have hvhl : ¬ (0 * vH + (1 - 0) * vL ≥ vHL vH vL) := by unfold vHL; intro h; linarith
  have hvhl2 : 1 / 2 * vH + (1 - 1 / 2) * vL ≥ vHL vH vL := by unfold vHL; linarith
  simp only [frac, buys, est1, est0, if_pos hvhl2, if_neg hvhl]; ring

theorem frac_vL (vH vL h : ℝ) (hv : vL < vH) : frac vH vL h vL = 1 := by
  have hvl : 1 / 2 * vH + (1 - 1 / 2) * vL ≥ vL := by linarith
  have h2 : 0 * vH + (1 - 0) * vL ≥ vL := by linarith
  simp only [frac, buys, est1, est0, if_pos hvl, if_pos h2]; ring

end DynOpaqueLemma1Aux

open DynOpaque.TwoPeriod DynOpaqueLemma1Aux in
theorem solution (vH vL cH cL α ξ₁ ξ₂ : ℝ) (hS : Standing vH vL cH cL α)
    (hξ₁ : ξ₁ ∈ Set.Icc (0 : ℝ) 1) (hξ₂ : ξ₂ ∈ Set.Icc (0 : ℝ) 1) :
    (frac vH vL ξ₁ (vHL vH vL) = ξ₁ ∧ frac vH vL ξ₁ vL = 1 ∧
      frac vH vL (α * ξ₁ + (1 - α) * ξ₂) (vHL vH vL) = α * ξ₁ + (1 - α) * ξ₂ ∧
      frac vH vL (α * ξ₁ + (1 - α) * ξ₂) vL = 1) ∧
    ∀ p₁ p₂ : ℝ, p₁ ≤ vHL vH vL → p₂ ≤ vHL vH vL →
      ∃ p₁' ∈ ({vL, vHL vH vL} : Set ℝ), ∃ p₂' ∈ ({vL, vHL vH vL} : Set ℝ),
        opaqueProfit vH vL cH cL α p₁ p₂ ξ₁ ξ₂ ≤ opaqueProfit vH vL cH cL α p₁' p₂' ξ₁ ξ₂ := by
  obtain ⟨hv, hc, h0, h1, hl⟩ := hS
  refine ⟨⟨frac_vHL _ _ _ hv, frac_vL _ _ _ hv, frac_vHL _ _ _ hv, frac_vL _ _ _ hv⟩, ?_⟩
  intro p₁ p₂ hp1 hp2
  have hh : 0 ≤ α * ξ₁ + (1 - α) * ξ₂ := by
    have : 0 ≤ 1 - α := by linarith
    have := hξ₁.1; have := hξ₂.1
    positivity
  have hm1 : vL ∈ ({vL, vHL vH vL} : Set ℝ) := Or.inl rfl
  have hm2 : vHL vH vL ∈ ({vL, vHL vH vL} : Set ℝ) := Or.inr rfl
  simp only [opaqueProfit]
  rcases term_le vH vL cH cL ξ₁ ξ₁ p₁ hv hp1 hξ₁.1 with t1 | t1 <;>
  rcases term_le vH vL cH cL (α * ξ₁ + (1 - α) * ξ₂) ξ₂ p₂ hv hp2 hh with t2 | t2
  · exact ⟨_, hm1, _, hm1, by linarith⟩
  · exact ⟨_, hm1, _, hm2, by linarith⟩
  · exact ⟨_, hm2, _, hm1, by linarith⟩
  · exact ⟨_, hm2, _, hm2, by linarith⟩
