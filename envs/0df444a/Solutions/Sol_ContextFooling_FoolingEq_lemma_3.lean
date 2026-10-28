-- Prove2me | solution 1 for ContextFooling.FoolingEq.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:44:11.99085+00:00
-- url     : https://prove2.me/submissions/f202236e-b3c4-4b77-90c8-4e3b021e1f9e

import Mathlib
import Definitions.Def_ContextFooling_FoolingEq_Model

namespace Aux_ContextFooling_lemma_3

theorem sign_neg (X Y β β0 : ℝ) (hlt : β < β0) (h1 : 0 ≤ X + β * Y) (h2 : X + β0 * Y ≤ 0)
    (h3 : 0 < X + β * Y ∨ X + β0 * Y < 0) : Y < 0 := by
  by_contra hY
  push_neg at hY
  have := mul_nonneg (sub_nonneg.mpr hlt.le) hY
  rcases h3 with h | h <;> nlinarith

theorem sign_pos (X Y β β0 : ℝ) (hlt : β0 < β) (h1 : 0 ≤ X + β * Y) (h2 : X + β0 * Y ≤ 0)
    (h3 : 0 < X + β * Y ∨ X + β0 * Y < 0) : 0 < Y := by
  by_contra hY
  push_neg at hY
  have := mul_nonneg (sub_nonneg.mpr hlt.le) (neg_nonneg.mpr hY)
  rcases h3 with h | h <;> nlinarith

end Aux_ContextFooling_lemma_3

open ContextFooling.FoolingEq Aux_ContextFooling_lemma_3 in
theorem solution (β β0 qlow ubar qt : ℝ) (hβ : 1 < β) (hβ0 : 1 < β0) (hqlow : 0 < qlow)
    (hubar : 0 ≤ ubar) (hqt : qlow ≤ qt) :
    -- a) fooling a pessimist forces a price strictly below p⁰_t
    (β < β0 → ∀ a t : Product, t.q = qt → Fools β β0 a t → qlow ≤ a.q → ubar ≤ u a →
        t.p < qt - ubar) ∧
    -- b) fooling an optimist is profitable with the listed context pairs
    (β0 < β →
      (qlow < qt → ∃ a t : Product, a.θ = Ctx.Q ∧ t.θ = Ctx.Q ∧ t.q = qt ∧ qlow ≤ a.q ∧
          ubar ≤ u a ∧ Fools β β0 a t ∧ a.q < qt ∧ qt - ubar < t.p) ∧
      (∃ a t : Product, a.θ = Ctx.P ∧ t.θ = Ctx.P ∧ t.q = qt ∧ qlow ≤ a.q ∧
          ubar ≤ u a ∧ Fools β β0 a t ∧ t.p < a.p ∧ qt - ubar < t.p) ∧
      (∀ θa θt : Ctx,
          (θa, θt) = (Ctx.P, Ctx.Q) ∨ (θa, θt) = (Ctx.P, Ctx.N) ∨ (θa, θt) = (Ctx.N, Ctx.Q) →
        ∃ a t : Product, a.θ = θa ∧ t.θ = θt ∧ t.q = qt ∧ qlow ≤ a.q ∧
          ubar ≤ u a ∧ Fools β β0 a t ∧ qt - ubar < t.p) ∧
      -- Moreover: with (Q,Q) fooling up-sells, with (P,P) it down-sells,
      (∀ a t : Product, a.θ = Ctx.Q → t.θ = Ctx.Q → Fools β β0 a t → a.q < t.q ∧ a.p < t.p) ∧
      (∀ a t : Product, a.θ = Ctx.P → t.θ = Ctx.P → Fools β β0 a t → t.q < a.q ∧ t.p < a.p) ∧
      -- and contexts favouring the attraction product cannot fool at any p_t ≥ 0
      (∀ a t : Product,
          (a.θ, t.θ) = (Ctx.Q, Ctx.P) ∨ (a.θ, t.θ) = (Ctx.Q, Ctx.N) ∨ (a.θ, t.θ) = (Ctx.N, Ctx.P) →
          qlow ≤ a.q → 0 ≤ t.p → ¬ Fools β β0 a t)) := by
  have hqt0 : 0 < qt := lt_of_lt_of_le hqlow hqt
  refine ⟨?_, ?_⟩
  · -- part (a)
    intro hlt a t htq hF haq hua
    obtain ⟨aq, ap, aθ⟩ := a
    obtain ⟨tq, tp, tθ⟩ := t
    simp only at htq haq ⊢
    subst htq
    obtain ⟨-, h1, h2, h3⟩ := hF
    have hu : ubar ≤ aq - ap := hua
    have hb1 : 0 < β - 1 := by linarith
    cases aθ <;> cases tθ <;> simp only [val] at h1 h2 h3
    · -- N N
      exfalso
      have := sign_neg (tq - tp - (aq - ap)) 0 β β0 hlt (by linarith) (by linarith)
        (by rcases h3 with h | h; left; linarith; right; linarith)
      linarith
    · -- N Q
      exfalso
      have := sign_neg (ap - aq - tp) tq β β0 hlt (by linarith) (by linarith)
        (by rcases h3 with h | h; left; linarith; right; linarith)
      linarith
    · -- N P
      have hY := sign_neg (tq - (aq - ap)) (-tp) β β0 hlt (by linarith) (by linarith)
        (by rcases h3 with h | h; left; linarith; right; linarith)
      nlinarith
    · -- Q N
      have hY := sign_neg (tq - tp + ap) (-aq) β β0 hlt (by linarith) (by linarith)
        (by rcases h3 with h | h; left; linarith; right; linarith)
      nlinarith
    · -- Q Q
      have hY := sign_neg (ap - tp) (tq - aq) β β0 hlt (by linarith) (by linarith)
        (by rcases h3 with h | h; left; linarith; right; linarith)
      have := mul_pos hb1 (by linarith : 0 < aq - tq)
      nlinarith
    · -- Q P
      have hY := sign_neg (tq + ap) (-tp - aq) β β0 hlt (by linarith) (by linarith)
        (by rcases h3 with h | h; left; linarith; right; linarith)
      set W := tq + aq - ubar with hW
      have hpos : 0 < tp + aq := by linarith
      have hβW : β * (tp + aq) ≤ W := by rw [hW]; linarith
      have hW0 : 0 < W := lt_of_lt_of_le (mul_pos (by linarith) hpos) hβW
      by_contra hc
      push_neg at hc
      have : β * (tq - ubar + aq) ≤ β * (tp + aq) := mul_le_mul_of_nonneg_left (by linarith)
        (by linarith)
      nlinarith
    · -- P N
      have hY := sign_neg (tq - tp - aq) ap β β0 hlt (by linarith) (by linarith)
        (by rcases h3 with h | h; left; linarith; right; linarith)
      have := mul_pos hb1 (by linarith : 0 < -ap)
      nlinarith
    · -- P Q
      have hY := sign_neg (-tp - aq) (tq + ap) β β0 hlt (by linarith) (by linarith)
        (by rcases h3 with h | h; left; linarith; right; linarith)
      have := mul_pos hb1 (by linarith : 0 < -(tq + ap))
      nlinarith
    · -- P P
      have hY := sign_neg (tq - aq) (ap - tp) β β0 hlt (by linarith) (by linarith)
        (by rcases h3 with h | h; left; linarith; right; linarith)
      have hq : 0 < tq - aq := by nlinarith
      have h4 : β * (tp - ap) ≤ tq - aq := by linarith
      have := mul_pos hb1 (by linarith : 0 < tp - ap)
      nlinarith
  · intro hlt
    have hb1 : 0 < β - 1 := by linarith
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hql
      refine ⟨⟨qlow, qlow - ubar, Ctx.Q⟩, ⟨qt, β * (qt - qlow) + qlow - ubar, Ctx.Q⟩,
        rfl, rfl, rfl, le_rfl, ?_, ⟨?_, ?_, ?_, ?_⟩, hql, ?_⟩
      · simp only [u]; linarith
      · intro h; have := congrArg Product.q h; simp only at this; linarith
      · simp only [val]; linarith
      · simp only [val]
        nlinarith [mul_pos (by linarith : 0 < β - β0) (by linarith : 0 < qt - qlow)]
      · right; simp only [val]
        nlinarith [mul_pos (by linarith : 0 < β - β0) (by linarith : 0 < qt - qlow)]
      · simp only
        nlinarith [mul_pos hb1 (by linarith : 0 < qt - qlow)]
    · refine ⟨⟨qt + β, qt - ubar + β, Ctx.P⟩, ⟨qt, qt - ubar + (β - 1), Ctx.P⟩,
        rfl, rfl, rfl, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · simp only; linarith
      · simp only [u]; linarith
      · intro h; have := congrArg Product.q h; simp only at this; linarith
      · simp only [val]; nlinarith
      · simp only [val]; nlinarith
      · right; simp only [val]; nlinarith
      · simp only; linarith
      · simp only; linarith
    · intro θa θt h
      rcases h with h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
      · refine ⟨⟨qlow + ubar, qlow, Ctx.P⟩, ⟨qt, β * (qt + qlow) - (qlow + ubar), Ctx.Q⟩,
          rfl, rfl, rfl, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · simp only; linarith
        · simp only [u]; linarith
        · intro h; have := congrArg Product.θ h; simp at this
        · simp only [val]; linarith
        · simp only [val]
          nlinarith [mul_pos (by linarith : 0 < β - β0) (by linarith : 0 < qt + qlow)]
        · right; simp only [val]
          nlinarith [mul_pos (by linarith : 0 < β - β0) (by linarith : 0 < qt + qlow)]
        · simp only
          nlinarith [mul_pos hb1 (by linarith : 0 < qt + qlow)]
      · refine ⟨⟨ubar + qlow, qlow, Ctx.P⟩, ⟨qt, qt - (ubar + qlow - β * qlow), Ctx.N⟩,
          rfl, rfl, rfl, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · simp only; linarith
        · simp only [u]; linarith
        · intro h; have := congrArg Product.θ h; simp at this
        · simp only [val]; linarith
        · simp only [val]
          nlinarith [mul_pos (by linarith : 0 < β - β0) hqlow]
        · right; simp only [val]
          nlinarith [mul_pos (by linarith : 0 < β - β0) hqlow]
        · simp only
          nlinarith [mul_pos hb1 hqlow]
      · refine ⟨⟨qlow, qlow - ubar, Ctx.N⟩, ⟨qt, β * qt - ubar, Ctx.Q⟩,
          rfl, rfl, rfl, le_rfl, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · simp only [u]; linarith
        · intro h; have := congrArg Product.θ h; simp at this
        · simp only [val]; linarith
        · simp only [val]
          nlinarith [mul_pos (by linarith : 0 < β - β0) hqt0]
        · right; simp only [val]
          nlinarith [mul_pos (by linarith : 0 < β - β0) hqt0]
        · simp only
          nlinarith [mul_pos hb1 hqt0]
    · intro a t ha ht hF
      obtain ⟨-, h1, h2, h3⟩ := hF
      simp only [val, ha, ht] at h1 h2 h3
      have hY := sign_pos (a.p - t.p) (t.q - a.q) β β0 hlt (by linarith) (by linarith)
        (by rcases h3 with h | h; left; linarith; right; linarith)
      refine ⟨by linarith, ?_⟩
      nlinarith [mul_pos (by linarith : (0 : ℝ) < β0) hY]
    · intro a t ha ht hF
      obtain ⟨-, h1, h2, h3⟩ := hF
      simp only [val, ha, ht] at h1 h2 h3
      have hY := sign_pos (t.q - a.q) (a.p - t.p) β β0 hlt (by linarith) (by linarith)
        (by rcases h3 with h | h; left; linarith; right; linarith)
      refine ⟨?_, by linarith⟩
      nlinarith [mul_pos (by linarith : (0 : ℝ) < β0) hY]
    · intro a t h haq htp hF
      obtain ⟨-, h1, h2, h3⟩ := hF
      rcases h with h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨ha, ht⟩ := h <;>
        simp only [val, ha, ht] at h1 h2 h3
      · have := sign_pos (t.q + a.p) (-t.p - a.q) β β0 hlt (by linarith) (by linarith)
          (by rcases h3 with h | h; left; linarith; right; linarith)
        linarith
      · have := sign_pos (t.q - t.p + a.p) (-a.q) β β0 hlt (by linarith) (by linarith)
          (by rcases h3 with h | h; left; linarith; right; linarith)
        linarith
      · have := sign_pos (t.q - (a.q - a.p)) (-t.p) β β0 hlt (by linarith) (by linarith)
          (by rcases h3 with h | h; left; linarith; right; linarith)
        linarith
