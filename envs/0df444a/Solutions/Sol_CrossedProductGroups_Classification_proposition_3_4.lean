-- Prove2me | solution 1 for CrossedProductGroups.Classification.proposition_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T22:07:37.158391+00:00
-- url     : https://prove2.me/submissions/7d18c0df-58ee-4b04-a631-4ef362c259ff

import Mathlib
import Definitions.Def_CrossedProductGroups_Classification_E2

open CrossedProductGroups.Classification

namespace CPG34Aux

variable {H G : Type*} [Group H] [Group G]

lemma alpha_one (c : E2 H G) (h : H) : c.1.1 1 h = h := by
  have := c.2.1.twisted 1 1 h
  rw [c.2.2, one_mul, one_mul, inv_one, mul_one] at this
  exact (c.1.1 1).injective this

lemma f_one_left (c : E2 H G) (g : G) : c.1.2 1 g = 1 := by
  have := c.2.1.cocycle 1 1 g
  rw [c.2.2, one_mul, one_mul, alpha_one, one_mul] at this
  exact (mul_eq_left.mp this.symm)

lemma f_one_right (c : E2 H G) (g : G) : c.1.2 g 1 = 1 := by
  have := c.2.1.cocycle g 1 1
  rw [c.2.2, mul_one, mul_one, map_one, one_mul] at this
  exact mul_eq_right.mp this

end CPG34Aux

open CPG34Aux

theorem solution {H G : Type*} [Group H] [Group G] (c c' : E2 H G)
    (η : H →* H) (γ : G →* G) (ψ : H × G → H × G) :
    (∃ m : E2Hom c c', m.η = η ∧ m.γ = γ ∧ m.ψ = ψ) ↔
      ∃! r : G → H,
        (∀ g : G, ∀ h : H, η (c.1.1 g h) * r g = r g * c'.1.1 (γ g) (η h)) ∧
        (∀ g₁ g₂ : G, r g₁ * c'.1.1 (γ g₁) (r g₂) * c'.1.2 (γ g₁) (γ g₂) =
          η (c.1.2 g₁ g₂) * r (g₁ * g₂)) ∧
        ∀ h : H, ∀ g : G, ψ (h, g) = (η h * r g, γ g) := by
  constructor
  · rintro ⟨m, rfl, rfl, rfl⟩
    have hform : ∀ h g, m.ψ (h, g) = (m.η h * (m.ψ (1, g)).1, m.γ g) := by
      intro h g
      have hx : ((h, g) : H × G) = crossedMul c.1.1 c.1.2 (h, 1) (1, g) := by
        simp [crossedMul, alpha_one, f_one_left]
      rw [hx, m.map_mul, m.comm_inl]
      have h2 := m.comm_snd (1, g)
      simp only [crossedMul, alpha_one, f_one_left, one_mul]
      rw [h2]
      simp [alpha_one, f_one_left]
    refine ⟨fun g => (m.ψ (1, g)).1, ⟨?_, ?_, hform⟩, ?_⟩
    · intro g h
      have e := m.map_mul (1, g) (h, 1)
      have hl : crossedMul c.1.1 c.1.2 (1, g) (h, 1) = (c.1.1 g h, g) := by
        simp [crossedMul, f_one_right]
      rw [hl, hform, hform 1 g, m.comm_inl] at e
      have e1 := congrArg Prod.fst e
      simp only [crossedMul, map_one, one_mul, f_one_right] at e1
      simpa [f_one_right] using e1
    · intro g₁ g₂
      have e := m.map_mul (1, g₁) (1, g₂)
      have hl : crossedMul c.1.1 c.1.2 (1, g₁) (1, g₂) = (c.1.2 g₁ g₂, g₁ * g₂) := by
        simp [crossedMul]
      rw [hl, hform, hform 1 g₁, hform 1 g₂] at e
      have e1 := congrArg Prod.fst e
      simp only [crossedMul, map_one, one_mul] at e1
      exact e1.symm
    · rintro r ⟨_, _, hr⟩
      funext g
      rw [hr 1 g]; simp
  · rintro ⟨r, ⟨h1, h2, h3⟩, -⟩
    have hr1 : r 1 = 1 := by
      have := h2 1 1
      rw [map_one, alpha_one, c'.2.2, c.2.2, map_one, mul_one, one_mul, mul_one] at this
      exact mul_eq_right.mp this
    have hψ : ψ = fun x => (η x.1 * r x.2, γ x.2) := by
      funext x; exact h3 x.1 x.2
    subst hψ
    refine ⟨⟨η, γ, fun x => (η x.1 * r x.2, γ x.2), ?_, ?_, ?_⟩, rfl, rfl, rfl⟩
    · rintro ⟨a₁, g₁⟩ ⟨a₂, g₂⟩
      simp only [crossedMul, map_mul, Prod.mk.injEq, and_true]
      have k1 := h1 g₁ a₂
      have k2 := h2 g₁ g₂
      calc η a₁ * η (c.1.1 g₁ a₂) * η (c.1.2 g₁ g₂) * r (g₁ * g₂)
          = η a₁ * η (c.1.1 g₁ a₂) * (η (c.1.2 g₁ g₂) * r (g₁ * g₂)) := by group
        _ = η a₁ * (η (c.1.1 g₁ a₂) * r g₁) * c'.1.1 (γ g₁) (r g₂) * c'.1.2 (γ g₁) (γ g₂) := by
            rw [← k2]; group
        _ = η a₁ * r g₁ * (c'.1.1 (γ g₁) (η a₂) * c'.1.1 (γ g₁) (r g₂)) *
              c'.1.2 (γ g₁) (γ g₂) := by rw [k1]; group
        _ = _ := by rw [← map_mul]
    · intro h; simp [hr1]
    · intro x; rfl
