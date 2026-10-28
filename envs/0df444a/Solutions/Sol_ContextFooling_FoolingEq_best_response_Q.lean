-- Prove2me | solution 1 for ContextFooling.FoolingEq.best_response_Q
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:39:06.083964+00:00
-- url     : https://prove2.me/submissions/bbda1c5d-eb09-4fbf-91ca-b20bd7d0785b

import Mathlib
import Definitions.Def_ContextFooling_FoolingEq_Model

open ContextFooling.FoolingEq in
theorem solution (P : Params) (hP : P.Standing) (β0 ubar : ℝ)
    (hβ0 : β0 ∈ Set.Ioo 1 P.β) (hubar : 0 ≤ ubar) :
    (∀ a t : Product, a.θ = Ctx.Q → t.θ = Ctx.Q → Fools P.β β0 a t → P.qlow ≤ a.q →
        P.qlow ≤ t.q → ubar ≤ u a →
        t.p - P.c t.q ≤ P.β * P.qQ - P.c P.qQ - (P.β - 1) * P.qlow - ubar ∧
        (t.p - P.c t.q = P.β * P.qQ - P.c P.qQ - (P.β - 1) * P.qlow - ubar ↔
          t = ⟨P.qQ, P.β * (P.qQ - P.qlow) + P.qlow - ubar, Ctx.Q⟩ ∧
          a = ⟨P.qlow, P.qlow - ubar, Ctx.Q⟩)) ∧
    (Fools P.β β0 ⟨P.qlow, P.qlow - ubar, Ctx.Q⟩
        ⟨P.qQ, P.β * (P.qQ - P.qlow) + P.qlow - ubar, Ctx.Q⟩ ∧
      ubar ≤ u ⟨P.qlow, P.qlow - ubar, Ctx.Q⟩ ∧
      (P.β * (P.qQ - P.qlow) + P.qlow - ubar) - P.c P.qQ =
        P.β * P.qQ - P.c P.qQ - (P.β - 1) * P.qlow - ubar) := by
  obtain ⟨hβ, hql, -, -, hC2, -, -, -, hc2, -, -, hqQ0, hcQ, hqP0, hcP, hqlP, -, -, -, -⟩ := hP
  have hdc : Continuous (deriv P.c) := hC2.continuous_deriv (by norm_num)
  have hdiff : Differentiable ℝ P.c := hC2.differentiable (by norm_num)
  have hmono : StrictMonoOn (deriv P.c) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hdc.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    exact hc2 x (le_of_lt hx)
  -- β q - c q is uniquely maximized at qQ on [0, ∞)
  have hmax : ∀ q, 0 ≤ q → q ≠ P.qQ → P.β * q - P.c q < P.β * P.qQ - P.c P.qQ := by
    intro q hq hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope P.c hlt hdiff.continuous.continuousOn
        hdiff.differentiableOn
      have hξlt : deriv P.c ξ < P.β := by
        rw [← hcQ]
        exact hmono (le_of_lt (lt_of_le_of_lt hq hξ.1)) hqQ0 hξ.2
      rw [hξeq, div_lt_iff₀ (by linarith)] at hξlt
      linarith
    · obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope P.c hgt hdiff.continuous.continuousOn
        hdiff.differentiableOn
      have hξgt : P.β < deriv P.c ξ := by
        rw [← hcQ]
        exact hmono hqQ0 (le_of_lt (lt_of_le_of_lt hqQ0 hξ.1)) hξ.1
      rw [hξeq, lt_div_iff₀ (by linarith)] at hξgt
      linarith
  have hmaxle : ∀ q, 0 ≤ q → P.β * q - P.c q ≤ P.β * P.qQ - P.c P.qQ := by
    intro q hq
    by_cases h : q = P.qQ
    · rw [h]
    · exact (hmax q hq h).le
  -- qQ > qlow
  have hβinv : 1 / P.β < P.β := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  have hqQP : P.qP < P.qQ := by
    by_contra h
    push_neg at h
    rcases h.eq_or_lt with h' | h'
    · rw [h'] at hcQ; rw [hcQ] at hcP; linarith
    · have := hmono hqQ0 hqP0 h'
      rw [hcQ, hcP] at this; linarith
  have hqQl : P.qlow < P.qQ := lt_of_le_of_lt hqlP hqQP
  refine ⟨?_, ?_⟩
  · intro a t ha ht hF haq htq hua
    obtain ⟨-, hv1, -, -⟩ := hF
    simp only [val, ha, ht] at hv1
    have hu : ubar ≤ a.q - a.p := hua
    have htp : t.p ≤ P.β * t.q - (P.β - 1) * P.qlow - ubar := by
      have : (P.β - 1) * P.qlow ≤ (P.β - 1) * a.q := mul_le_mul_of_nonneg_left haq (by linarith)
      linarith
    have hq0 : 0 ≤ t.q := le_trans hql.le htq
    have hm := hmaxle t.q hq0
    refine ⟨by linarith, ?_, ?_⟩
    · intro heq
      have htq' : t.q = P.qQ := by
        by_contra hne
        have := hmax t.q hq0 hne
        linarith
      have haq' : a.q = P.qlow := by
        by_contra hne
        have hlt : P.qlow < a.q := lt_of_le_of_ne haq (Ne.symm hne)
        have : (P.β - 1) * P.qlow < (P.β - 1) * a.q := mul_lt_mul_of_pos_left hlt (by linarith)
        rw [htq'] at heq hv1
        linarith
      have hap : a.p = P.qlow - ubar := by
        rw [htq'] at heq hv1
        rw [haq'] at hu hv1
        linarith
      have htp' : t.p = P.β * (P.qQ - P.qlow) + P.qlow - ubar := by
        rw [htq'] at heq hv1
        rw [haq', hap] at hv1
        linarith
      constructor
      · cases t; simp only at ht htq' htp' ⊢; rw [ht, htq', htp']
      · cases a; simp only at ha haq' hap ⊢; rw [ha, haq', hap]
    · rintro ⟨rfl, rfl⟩
      simp only
      ring
  · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro h
      have := congrArg Product.q h
      simp only at this
      linarith
    · simp only [val]; ring_nf; rfl
    · simp only [val]
      have : β0 * (P.qQ - P.qlow) ≤ P.β * (P.qQ - P.qlow) :=
        mul_le_mul_of_nonneg_right hβ0.2.le (by linarith)
      nlinarith
    · right
      simp only [val]
      have : β0 * (P.qQ - P.qlow) < P.β * (P.qQ - P.qlow) :=
        mul_lt_mul_of_pos_right hβ0.2 (by linarith)
      nlinarith
    · simp only [u]; linarith
    · ring
