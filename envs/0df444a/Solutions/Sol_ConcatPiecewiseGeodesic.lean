-- Prove2me | solution 1 for ConcatPiecewiseGeodesic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:56:59.376706+00:00
-- url     : https://prove2.me/submissions/af078ab7-dddb-4268-988c-716bfabc4b09

import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_IsPiecewiseGeodesicWith
import Definitions.Def_Tablet_ConcatPiecewiseGeodesic

set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ₁ γ₂ : Curve E)
    (h : γ₁.toFun γ₁.len = γ₂.toFun 0) (k₁ k₂ : ℕ)
    (h₁ : IsPiecewiseGeodesicWith γ₁ k₁) (h₂ : IsPiecewiseGeodesicWith γ₂ k₂) :
    IsPiecewiseGeodesicWith (curveConcat γ₁ γ₂ h) (k₁ + k₂) := by
-- BODY
  classical
  obtain ⟨s₁, hm₁, hz₁, he₁, hg₁⟩ := h₁
  obtain ⟨s₂, hm₂, hz₂, he₂, hg₂⟩ := h₂
  set C := curveConcat γ₁ γ₂ h with hC
  have hCval : ∀ t : ℝ, C.toFun t = if t ≤ γ₁.len then γ₁.toFun t else γ₂.toFun (t - γ₁.len) :=
    fun t => rfl
  have hs₁le : ∀ i ≤ k₁, s₁ i ≤ γ₁.len := by
    intro i hi
    have := hm₁ (Set.mem_Icc.mpr ⟨Nat.zero_le _, hi⟩) (Set.mem_Icc.mpr ⟨Nat.zero_le _, le_rfl⟩) hi
    rwa [he₁] at this
  have hs₂nonneg : ∀ i ≤ k₂, 0 ≤ s₂ i := by
    intro i hi
    have := hm₂ (Set.mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, hi⟩) (Nat.zero_le _)
    rwa [hz₂] at this
  have hCsecond : ∀ t : ℝ, γ₁.len ≤ t → C.toFun t = γ₂.toFun (t - γ₁.len) := by
    intro t ht
    rw [hCval]
    split
    · next hle =>
      have : t = γ₁.len := le_antisymm hle ht
      subst this
      simpa using h
    · rfl
  set s : ℕ → ℝ := fun j => if j ≤ k₁ then s₁ j else γ₁.len + s₂ (j - k₁) with hs
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [hs]
    have hbk : b ≤ k₁ + k₂ := (Set.mem_Icc.mp hb).2
    by_cases ha1 : a ≤ k₁ <;> by_cases hb1 : b ≤ k₁
    · simp only [if_pos ha1, if_pos hb1]
      exact hm₁ (Set.mem_Icc.mpr ⟨Nat.zero_le _, ha1⟩) (Set.mem_Icc.mpr ⟨Nat.zero_le _, hb1⟩) hab
    · simp only [if_pos ha1, if_neg hb1]
      have := hs₁le a ha1
      have := hs₂nonneg (b - k₁) (by omega)
      linarith
    · omega
    · simp only [if_neg ha1, if_neg hb1]
      have := hm₂ (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
        (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩) (by omega : a - k₁ ≤ b - k₁)
      linarith
  · simp only [hs, if_pos (Nat.zero_le k₁), hz₁]
  · simp only [hs]
    by_cases hk₂ : k₂ = 0
    · subst hk₂
      have hz : γ₂.len = 0 := by rw [← he₂, hz₂]
      simp only [Nat.add_zero, if_pos (le_refl k₁), he₁]
      show γ₁.len = γ₁.len + γ₂.len
      rw [hz, add_zero]
    · rw [if_neg (by omega)]
      show γ₁.len + s₂ (k₁ + k₂ - k₁) = γ₁.len + γ₂.len
      rw [Nat.add_sub_cancel_left, he₂]
  · intro i hi
    by_cases hi1 : i + 1 ≤ k₁
    · have hik : i ≤ k₁ := by omega
      simp only [hs, if_pos hik, if_pos hi1]
      intro u hu v hv
      have hule : u ≤ γ₁.len := le_trans hu.2 (hs₁le _ hi1)
      have hvle : v ≤ γ₁.len := le_trans hv.2 (hs₁le _ hi1)
      rw [hCval u, hCval v, if_pos hule, if_pos hvle]
      exact hg₁ i (by omega) u hu v hv
    · have hik : ¬ (i + 1 ≤ k₁) := hi1
      have hik2 : ¬ (i ≤ k₁) ∨ i = k₁ := by omega
      have hiexp : s i = γ₁.len + s₂ (i - k₁) := by
        simp only [hs]
        rcases hik2 with hk | hk
        · rw [if_neg hk]
        · subst hk; rw [if_pos (le_refl _), Nat.sub_self, hz₂, add_zero, he₁]
      have hi1exp : s (i + 1) = γ₁.len + s₂ (i + 1 - k₁) := by
        simp only [hs, if_neg hik]
      rw [hiexp, hi1exp]
      intro u hu v hv
      have hs₂0 : 0 ≤ s₂ (i - k₁) := hs₂nonneg _ (by omega)
      have huge : γ₁.len ≤ u := by have := hu.1; linarith
      have hvge : γ₁.len ≤ v := by have := hv.1; linarith
      rw [hCsecond u huge, hCsecond v hvge]
      have hsub : i + 1 - k₁ = (i - k₁) + 1 := by omega
      have := hg₂ (i - k₁) (by omega) (u - γ₁.len)
        ⟨by have := hu.1; linarith, by have h2 := hu.2; rw [hsub] at h2; linarith⟩
        (v - γ₁.len) ⟨by have := hv.1; linarith, by have h2 := hv.2; rw [hsub] at h2; linarith⟩
      rw [this]
      congr 1
      ring
