-- Prove2me | solution 1 for ContextFooling.FoolingEq.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:40:55.779689+00:00
-- url     : https://prove2.me/submissions/9f7005cd-748c-4d5e-ac9d-4158a90fcb22

import Mathlib
import Definitions.Def_ContextFooling_FoolingEq_Model

namespace Aux_CF_l2
open ContextFooling.FoolingEq

lemma real_part (A B β β0 : ℝ) (hβ : 1 < β) (hβ0 : 1 < β0) (h1 : 0 ≤ A + B * β)
    (h2 : A + B * β0 ≤ 0) (h3 : 0 < A + B * β ∨ A + B * β0 < 0) :
    β0 ≠ β ∧ (β < β0 → (∀ γ, γ < β → 0 < A + B * γ) ∧ 0 < A + B * 1) ∧
      (β0 < β → (∀ γ, β < γ → 0 < A + B * γ) ∧ A + B * 1 < 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [h] at h2
    rcases h3 with h3 | h3 <;> [linarith; (rw [h] at h3; linarith)]
  · intro hlt
    have hB : B ≤ 0 := by
      by_contra hB; push_neg at hB
      nlinarith [mul_pos hB (sub_pos.mpr hlt)]
    have key : ∀ γ, γ < β → 0 < A + B * γ := by
      intro γ hγ
      rcases h3 with h | h
      · nlinarith [mul_nonneg_of_nonpos_of_nonpos hB (sub_nonpos.mpr hγ.le)]
      · have hB' : B < 0 := by
          by_contra hB'; push_neg at hB'
          have : B = 0 := le_antisymm hB hB'
          subst this; linarith
        nlinarith [mul_pos_of_neg_of_neg hB' (sub_neg.mpr hγ)]
    exact ⟨key, key 1 hβ⟩
  · intro hlt
    have hB : 0 ≤ B := by
      by_contra hB; push_neg at hB
      nlinarith [mul_neg_of_neg_of_pos hB (sub_pos.mpr hlt)]
    constructor
    · intro γ hγ
      rcases h3 with h | h
      · nlinarith [mul_nonneg hB (sub_nonneg.mpr hγ.le)]
      · have hB' : 0 < B := by
          by_contra hB'; push_neg at hB'
          have : B = 0 := le_antisymm hB' hB
          subst this; linarith
        nlinarith [mul_pos hB' (sub_pos.mpr hγ)]
    · rcases h3 with h | h
      · have hB' : 0 < B := by
          by_contra hB'; push_neg at hB'
          have : B = 0 := le_antisymm hB' hB
          subst this; linarith
        nlinarith [mul_pos hB' (sub_pos.mpr hβ0)]
      · nlinarith [mul_nonneg hB (sub_nonneg.mpr hβ0.le)]

lemma aff (j : Product) : ∃ x y : ℝ, ∀ γ, val γ j = x + y * γ := by
  rcases j with ⟨q, p, θ⟩
  cases θ
  · exact ⟨q - p, 0, fun γ => by dsimp only [val]; ring⟩
  · exact ⟨-p, q, fun γ => by dsimp only [val]; ring⟩
  · exact ⟨q, -p, fun γ => by dsimp only [val]; ring⟩

lemma val_one (j : Product) : val 1 j = u j := by
  rcases j with ⟨q, p, θ⟩
  cases θ <;> simp [val, u]

end Aux_CF_l2

open ContextFooling.FoolingEq in
theorem solution (β β0 : ℝ) (hβ : 1 < β) (hβ0 : 1 < β0) (a t : Product)
    (hfool : Fools β β0 a t) :
    (a.θ, t.θ) ≠ (Ctx.N, Ctx.N) ∧ β0 ≠ β ∧
    (β < β0 → (∀ γ : ℝ, γ < β → val γ a < val γ t) ∧ u a < u t) ∧
    (β0 < β → (∀ γ : ℝ, β < γ → val γ a < val γ t) ∧ u t < u a) := by
  obtain ⟨-, hle1, hle2, hstrict⟩ := hfool
  obtain ⟨xa, ya, ha⟩ := Aux_CF_l2.aff a
  obtain ⟨xt, yt, ht⟩ := Aux_CF_l2.aff t
  have hD : ∀ γ, val γ t - val γ a = (xt - xa) + (yt - ya) * γ := by
    intro γ; rw [ha, ht]; ring
  have h1 : 0 ≤ (xt - xa) + (yt - ya) * β := by rw [← hD]; linarith
  have h2 : (xt - xa) + (yt - ya) * β0 ≤ 0 := by rw [← hD]; linarith
  have h3 : 0 < (xt - xa) + (yt - ya) * β ∨ (xt - xa) + (yt - ya) * β0 < 0 := by
    rcases hstrict with h | h
    · left; rw [← hD]; linarith
    · right; rw [← hD]; linarith
  obtain ⟨r1, r2, r3⟩ := Aux_CF_l2.real_part _ _ β β0 hβ hβ0 h1 h2 h3
  refine ⟨?_, r1, ?_, ?_⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hta, htt⟩ := h
    have hva : ∀ γ, val γ a = a.q - a.p := by intro γ; simp only [val, hta]
    have hvt : ∀ γ, val γ t = t.q - t.p := by intro γ; simp only [val, htt]
    rw [hva, hvt] at hle1 hle2
    rcases hstrict with h | h <;> rw [hva, hvt] at h <;> linarith
  · intro hlt
    obtain ⟨k1, k2⟩ := r2 hlt
    refine ⟨fun γ hγ => ?_, ?_⟩
    · have := k1 γ hγ; rw [← hD] at this; linarith
    · rw [← Aux_CF_l2.val_one, ← Aux_CF_l2.val_one]; rw [← hD] at k2; linarith
  · intro hlt
    obtain ⟨k1, k2⟩ := r3 hlt
    refine ⟨fun γ hγ => ?_, ?_⟩
    · have := k1 γ hγ; rw [← hD] at this; linarith
    · rw [← Aux_CF_l2.val_one, ← Aux_CF_l2.val_one]; rw [← hD] at k2; linarith
