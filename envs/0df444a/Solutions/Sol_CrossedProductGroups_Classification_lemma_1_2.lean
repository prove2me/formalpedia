-- Prove2me | solution 1 for CrossedProductGroups.Classification.lemma_1_2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T21:46:54.258846+00:00
-- url     : https://prove2.me/submissions/5869a68f-79e8-402c-8c3c-f393790a4cdc

import Mathlib
import Definitions.Def_CrossedProductGroups_Classification_CrossedSystem

open CrossedProductGroups.Classification

theorem solution {H G : Type*} [Group H] [Group G] (α : G → MulAut H) (f : G → G → H)
    (hc : IsCrossedSystem α f) :
    (∀ g : G, f g 1 = α g (f 1 1)) ∧
    (∀ h : H, α 1 h = f 1 1 * h * (f 1 1)⁻¹) ∧
    (∀ g : G, f 1 g = f 1 1) ∧
    (f 1 1 = 1 → (∀ g : G, f 1 g = 1 ∧ f g 1 = 1) ∧ ∀ h : H, α 1 h = h) := by
  have h1 : ∀ g : G, f g 1 = α g (f 1 1) := by
    intro g
    have := hc.cocycle g 1 1
    rw [mul_one, mul_one] at this
    exact mul_right_cancel this
  have h2 : ∀ h : H, α 1 h = f 1 1 * h * (f 1 1)⁻¹ := by
    intro h
    have t := hc.twisted 1 1 h
    rw [mul_one] at t
    have e : f 1 1 = α 1 (f 1 1) := h1 1
    apply (α 1).injective
    rw [t, map_mul, map_mul, map_inv, ← e]
  have h3 : ∀ g : G, f 1 g = f 1 1 := by
    intro g
    have c := hc.cocycle 1 1 g
    rw [one_mul, one_mul, h2] at c
    have c' : f 1 1 * f 1 g * 1 = f 1 1 * f 1 g * ((f 1 1)⁻¹ * f 1 g) := by
      conv_lhs => rw [mul_one, c]
      simp only [mul_assoc]
    have := mul_left_cancel c'
    exact (inv_mul_eq_one.mp this.symm).symm
  refine ⟨h1, h2, h3, fun h11 => ⟨fun g => ⟨by rw [h3, h11], by rw [h1, h11, map_one]⟩, fun h => ?_⟩⟩
  rw [h2, h11]; group
