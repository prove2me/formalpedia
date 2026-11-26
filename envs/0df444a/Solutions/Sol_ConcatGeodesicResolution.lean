-- Prove2me | solution 1 for ConcatGeodesicResolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:27.417364+00:00
-- url     : https://prove2.me/submissions/254959ac-3722-488d-a247-cb806873b4fb

import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_ConcatGeodesicResolution

set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (η₁ η₂ : Curve E)
    (h : η₁.toFun η₁.len = η₂.toFun 0) (K₁ K₂ : ℕ) (r₁ r₂ : ℕ → ℝ)
    (h₁ : IsGeodesicResolution η₁ K₁ r₁) (h₂ : IsGeodesicResolution η₂ K₂ r₂) :
    IsGeodesicResolution (curveConcat η₁ η₂ h) (K₁ + K₂)
      (fun i => if i ≤ K₁ then r₁ i else η₁.len + r₂ (i - K₁)) := by
-- BODY
  classical
  obtain ⟨hm₁, hz₁, he₁, hg₁⟩ := h₁
  obtain ⟨hm₂, hz₂, he₂, hg₂⟩ := h₂
  set C := curveConcat η₁ η₂ h with hC
  have hCval : ∀ t : ℝ, C.toFun t = if t ≤ η₁.len then η₁.toFun t else η₂.toFun (t - η₁.len) :=
    fun t => rfl
  have hr₁le : ∀ i ≤ K₁, r₁ i ≤ η₁.len := by
    intro i hi
    have := hm₁ (Set.mem_Icc.mpr ⟨Nat.zero_le _, hi⟩) (Set.mem_Icc.mpr ⟨Nat.zero_le _, le_rfl⟩) hi
    rwa [he₁] at this
  have hr₂nonneg : ∀ i ≤ K₂, 0 ≤ r₂ i := by
    intro i hi
    have := hm₂ (Set.mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, hi⟩) (Nat.zero_le _)
    rwa [hz₂] at this
  have hCsecond : ∀ t : ℝ, η₁.len ≤ t → C.toFun t = η₂.toFun (t - η₁.len) := by
    intro t ht
    rw [hCval]
    split
    · next hle =>
      have : t = η₁.len := le_antisymm hle ht
      subst this
      simpa using h
    · rfl
  set s : ℕ → ℝ := fun j => if j ≤ K₁ then r₁ j else η₁.len + r₂ (j - K₁) with hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [hs]
    have hbk : b ≤ K₁ + K₂ := (Set.mem_Icc.mp hb).2
    by_cases ha1 : a ≤ K₁ <;> by_cases hb1 : b ≤ K₁
    · simp only [if_pos ha1, if_pos hb1]
      exact hm₁ (Set.mem_Icc.mpr ⟨Nat.zero_le _, ha1⟩) (Set.mem_Icc.mpr ⟨Nat.zero_le _, hb1⟩) hab
    · simp only [if_pos ha1, if_neg hb1]
      have := hr₁le a ha1
      have := hr₂nonneg (b - K₁) (by omega)
      linarith
    · omega
    · simp only [if_neg ha1, if_neg hb1]
      have := hm₂ (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
        (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩) (by omega : a - K₁ ≤ b - K₁)
      linarith
  · simp only [hs, if_pos (Nat.zero_le K₁), hz₁]
  · simp only [hs]
    by_cases hK₂ : K₂ = 0
    · subst hK₂
      have hz : η₂.len = 0 := by rw [← he₂, hz₂]
      simp only [Nat.add_zero, if_pos (le_refl K₁), he₁]
      show η₁.len = C.len
      show η₁.len = η₁.len + η₂.len
      rw [hz, add_zero]
    · rw [if_neg (by omega)]
      show η₁.len + r₂ (K₁ + K₂ - K₁) = C.len
      show η₁.len + r₂ (K₁ + K₂ - K₁) = η₁.len + η₂.len
      rw [Nat.add_sub_cancel_left, he₂]
  · intro i hi
    by_cases hi1 : i + 1 ≤ K₁
    · have hik : i ≤ K₁ := by omega
      simp only [hs, if_pos hik, if_pos hi1]
      intro u hu v hv
      have hule : u ≤ η₁.len := le_trans hu.2 (hr₁le _ hi1)
      have hvle : v ≤ η₁.len := le_trans hv.2 (hr₁le _ hi1)
      rw [hCval u, hCval v, if_pos hule, if_pos hvle]
      exact hg₁ i (by omega) u hu v hv
    · have hik : ¬ (i + 1 ≤ K₁) := hi1
      have hik2 : ¬ (i ≤ K₁) ∨ i = K₁ := by omega
      have hiexp : (if i ≤ K₁ then r₁ i else η₁.len + r₂ (i - K₁)) = η₁.len + r₂ (i - K₁) := by
        rcases hik2 with hk | hk
        · rw [if_neg hk]
        · subst hk; rw [if_pos (le_refl _), Nat.sub_self, hz₂, add_zero, he₁]
      simp only [hs]
      rw [hiexp, if_neg hik]
      intro u hu v hv
      have hr₂0 : 0 ≤ r₂ (i - K₁) := hr₂nonneg _ (by omega)
      have huge : η₁.len ≤ u := by have := hu.1; linarith
      have hvge : η₁.len ≤ v := by have := hv.1; linarith
      rw [hCsecond u huge, hCsecond v hvge]
      have hsub : i + 1 - K₁ = (i - K₁) + 1 := by omega
      have := hg₂ (i - K₁) (by omega) (u - η₁.len)
        ⟨by have := hu.1; linarith, by have h2 := hu.2; rw [hsub] at h2; linarith⟩
        (v - η₁.len) ⟨by have := hv.1; linarith, by have h2 := hv.2; rw [hsub] at h2; linarith⟩
      rw [this]
      congr 1
      ring
