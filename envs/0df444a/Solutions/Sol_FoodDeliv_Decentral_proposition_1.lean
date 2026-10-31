-- Prove2me | solution 1 for FoodDeliv.Decentral.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T05:22:38.003684+00:00
-- url     : https://prove2.me/submissions/beaf52b0-78d5-49ac-9af7-1465037b8718

import Mathlib
import Definitions.Def_FoodDeliv_Decentral_Model
import Theorems.Thm_FoodDeliv_Decentral_prop_C_4
import Theorems.Thm_FoodDeliv_Decentral_cor_C_3
import Theorems.Thm_FoodDeliv_Decentral_cor_C_4
import Theorems.Thm_FoodDeliv_Decentral_cor_C_2
import Theorems.Thm_FoodDeliv_Decentral_lemma_C_8

open Filter Topology
open FoodDeliv.Decentral

namespace FDProp1Aux

noncomputable def sig (P : Params) (p θ : ℝ) : Profile :=
  if P.c / (P.μ - P.Λ1) < P.R - p then
    (if θ ≤ (P.R - p) * (P.c - P.ϕ) / P.c then ⟨P.Λ1, 0, P.μ - P.c / (P.R - p) - P.Λ1⟩
     else ⟨0, 0, P.μ - P.c / (P.R - p)⟩)
  else if P.ϕ / (P.μ - P.Λ1) ≤ P.R - p - θ then ⟨P.Λ1, 0, 0⟩
  else if P.ϕ / P.μ < P.R - p - θ ∧ θ ≤ (P.R - p) * (P.c - P.ϕ) / P.c then
    ⟨P.μ - P.ϕ / (P.R - p - θ), 0, 0⟩
  else if P.c / P.μ < P.R - p then ⟨0, 0, P.μ - P.c / (P.R - p)⟩
  else ⟨0, 0, 0⟩

lemma T1 (P : Params) (hP : P.Standing) (p θ : ℝ) (h1 : P.R - p ≤ P.c / P.μ)
    (h2 : P.R - p - θ ≤ P.ϕ / P.μ) : IsCustEq P p θ ⟨0, 0, 0⟩ := by
  have hμ := hP.μ_pos; have hΛ0 := hP.μ_le_Λ0; have hΛ1 := hP.Λ1_pos
  have ht : (⟨0, 0, 0⟩ : Profile).total = 0 := by simp [Profile.total, Profile.lamW]
  have hW : UW P p 0 ≤ 0 := by unfold UW; simp; linarith
  have hD : UD P p θ 0 ≤ 0 := by unfold UD; simp; linarith
  refine ⟨le_refl _, le_refl _, le_refl _, by simp; linarith, by simp; linarith,
    by rw [ht]; exact hμ, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp at h
  · intro _; rw [ht]; exact hW
  · intro h; simp at h
  · intro h; simp at h
  · intro _; rw [ht]; exact ⟨hD, hW, fun _ => rfl⟩

lemma T4 (P : Params) (hP : P.Standing) (p θ : ℝ) (h1 : P.R - p ≤ P.c / (P.μ - P.Λ1))
    (h2 : P.ϕ / (P.μ - P.Λ1) ≤ P.R - p - θ) : IsCustEq P p θ ⟨P.Λ1, 0, 0⟩ := by
  have hμ := hP.μ_pos; have hΛ0 := hP.μ_le_Λ0; have hΛ1 := hP.Λ1_pos; have hΛ1' := hP.Λ1_lt_μ
  have ht : (⟨P.Λ1, 0, 0⟩ : Profile).total = P.Λ1 := by simp [Profile.total, Profile.lamW]
  have hW : UW P p P.Λ1 ≤ 0 := by unfold UW; linarith
  have hD : 0 ≤ UD P p θ P.Λ1 := by unfold UD; linarith
  refine ⟨hΛ1.le, le_refl _, le_refl _, by simp, by simp; linarith,
    by rw [ht]; exact hΛ1', ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp at h
  · intro _; rw [ht]; exact hW
  · intro _; rw [ht]; exact ⟨hD, by linarith⟩
  · intro h; simp at h
  · intro h; simp at h

lemma T5 (P : Params) (hP : P.Standing) (p θ : ℝ) (h1 : P.ϕ / P.μ < P.R - p - θ)
    (h2 : P.R - p - θ < P.ϕ / (P.μ - P.Λ1)) (h3 : θ ≤ (P.R - p) * (P.c - P.ϕ) / P.c) :
    IsCustEq P p θ ⟨P.μ - P.ϕ / (P.R - p - θ), 0, 0⟩ := by
  have hμ := hP.μ_pos; have hΛ0 := hP.μ_le_Λ0; have hΛ1 := hP.Λ1_pos; have hΛ1' := hP.Λ1_lt_μ
  have hc := hP.c_pos; have hϕ0 := hP.ϕ_nonneg
  have hμΛ : 0 < P.μ - P.Λ1 := by linarith
  have hϕ : 0 < P.ϕ := by
    rcases hϕ0.lt_or_eq with h | h
    · exact h
    · rw [← h] at h1 h2; simp at h1 h2; linarith
  set d := P.R - p - θ with hd
  have hdpos : 0 < d := lt_of_le_of_lt (div_nonneg hϕ0 hμ.le) h1
  have e1 : P.ϕ < P.μ * d := by rwa [div_lt_iff₀ hμ, mul_comm] at h1
  have e2 : d * (P.μ - P.Λ1) < P.ϕ := by rwa [lt_div_iff₀ hμΛ] at h2
  have e3 : θ * P.c ≤ (P.R - p) * (P.c - P.ϕ) := by rwa [le_div_iff₀ hc] at h3
  have ht : (⟨P.μ - P.ϕ / d, 0, 0⟩ : Profile).total = P.μ - P.ϕ / d := by
    simp [Profile.total, Profile.lamW]
  have hsub : P.μ - (P.μ - P.ϕ / d) = P.ϕ / d := by ring
  have hD : UD P p θ (P.μ - P.ϕ / d) = 0 := by
    unfold UD; rw [hsub]; field_simp; linarith
  have hW : UW P p (P.μ - P.ϕ / d) ≤ 0 := by
    unfold UW; rw [hsub, div_div_eq_mul_div]
    have : P.R - p ≤ P.c * d / P.ϕ := by
      rw [le_div_iff₀ hϕ]; nlinarith
    linarith
  have hlpos : 0 < P.μ - P.ϕ / d := by
    have : P.ϕ / d < P.μ := by rw [div_lt_iff₀ hdpos]; linarith
    linarith
  have hlle : P.μ - P.ϕ / d ≤ P.Λ1 := by
    have : P.μ - P.Λ1 ≤ P.ϕ / d := by rw [le_div_iff₀ hdpos]; linarith
    linarith
  refine ⟨hlpos.le, le_refl _, le_refl _, by simpa using hlle, by simp; linarith,
    by rw [ht]; linarith [div_pos hϕ hdpos], ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp at h
  · intro _; rw [ht]; exact hW
  · intro _; rw [ht, hD]; exact ⟨le_refl _, hW⟩
  · intro h; simp at h
  · intro _; rw [ht, hD]; exact ⟨le_refl _, hW, fun _ => rfl⟩

lemma T3 (P : Params) (hP : P.Standing) (p θ : ℝ) (h1 : P.c / (P.μ - P.Λ1) < P.R - p)
    (h3 : θ ≤ (P.R - p) * (P.c - P.ϕ) / P.c) :
    IsCustEq P p θ ⟨P.Λ1, 0, P.μ - P.c / (P.R - p) - P.Λ1⟩ := by
  have hμ := hP.μ_pos; have hΛ0 := hP.μ_le_Λ0; have hΛ1 := hP.Λ1_pos; have hΛ1' := hP.Λ1_lt_μ
  have hc := hP.c_pos; have hϕ0 := hP.ϕ_nonneg
  have hμΛ : 0 < P.μ - P.Λ1 := by linarith
  set a := P.R - p with ha
  have hapos : 0 < a := lt_trans (div_pos hc hμΛ) h1
  have e1 : P.c < a * (P.μ - P.Λ1) := by rwa [div_lt_iff₀ hμΛ] at h1
  have e3 : θ * P.c ≤ a * (P.c - P.ϕ) := by rwa [le_div_iff₀ hc] at h3
  have ht : (⟨P.Λ1, 0, P.μ - P.c / a - P.Λ1⟩ : Profile).total = P.μ - P.c / a := by
    simp [Profile.total, Profile.lamW]
  have hsub : P.μ - (P.μ - P.c / a) = P.c / a := by ring
  have hW : UW P p (P.μ - P.c / a) = 0 := by
    unfold UW; rw [hsub]; field_simp; ring
  have hD : 0 ≤ UD P p θ (P.μ - P.c / a) := by
    unfold UD; rw [hsub, div_div_eq_mul_div]
    have : P.ϕ * a / P.c ≤ a - θ := by rw [div_le_iff₀ hc]; nlinarith
    linarith
  have hca : P.c / a < P.μ - P.Λ1 := by rw [div_lt_iff₀ hapos]; linarith
  refine ⟨hΛ1.le, le_refl _, by linarith, by simp, ?_,
    by rw [ht]; linarith [div_pos hc hapos], ?_, ?_, ?_, ?_, ?_⟩
  · show P.μ - P.c / a - P.Λ1 ≤ P.Λ0; linarith [div_pos hc hapos]
  · intro _; rw [ht, hW]
  · intro _; rw [ht, hW]
  · intro _; rw [ht, hW]; exact ⟨hD, hD⟩
  · intro h; simp at h
  · intro h; simp at h

lemma T2 (P : Params) (hP : P.Standing) (p θ : ℝ) (h1 : P.c / P.μ < P.R - p)
    (h3 : (P.R - p) * (P.c - P.ϕ) / P.c < θ) :
    IsCustEq P p θ ⟨0, 0, P.μ - P.c / (P.R - p)⟩ := by
  have hμ := hP.μ_pos; have hΛ0 := hP.μ_le_Λ0; have hΛ1 := hP.Λ1_pos; have hΛ1' := hP.Λ1_lt_μ
  have hc := hP.c_pos; have hϕ0 := hP.ϕ_nonneg
  set a := P.R - p with ha
  have hapos : 0 < a := lt_trans (div_pos hc hμ) h1
  have e1 : P.c < a * P.μ := by rwa [div_lt_iff₀ hμ] at h1
  have e3 : a * (P.c - P.ϕ) < θ * P.c := by rwa [div_lt_iff₀ hc] at h3
  have ht : (⟨0, 0, P.μ - P.c / a⟩ : Profile).total = P.μ - P.c / a := by
    simp [Profile.total, Profile.lamW]
  have hsub : P.μ - (P.μ - P.c / a) = P.c / a := by ring
  have hW : UW P p (P.μ - P.c / a) = 0 := by
    unfold UW; rw [hsub]; field_simp; ring
  have hD : UD P p θ (P.μ - P.c / a) < 0 := by
    unfold UD; rw [hsub, div_div_eq_mul_div]
    have : a - θ < P.ϕ * a / P.c := by rw [lt_div_iff₀ hc]; nlinarith
    linarith
  have hca : P.c / a < P.μ := by rw [div_lt_iff₀ hapos]; linarith
  refine ⟨le_refl _, le_refl _, by linarith, by simp; linarith, ?_,
    by rw [ht]; linarith [div_pos hc hapos], ?_, ?_, ?_, ?_, ?_⟩
  · show P.μ - P.c / a ≤ P.Λ0; linarith [div_pos hc hapos]
  · intro _; rw [ht, hW]
  · intro _; rw [ht, hW]
  · intro h; simp at h
  · intro h; simp at h
  · intro _; rw [ht, hW]
    exact ⟨hD.le, le_refl _, fun h => absurd h.1 (ne_of_lt hD)⟩

lemma sig_cust (P : Params) (hP : P.Standing) (p θ : ℝ) : IsCustEq P p θ (sig P p θ) := by
  have hμ := hP.μ_pos; have hΛ1 := hP.Λ1_pos; have hΛ1' := hP.Λ1_lt_μ
  have hc := hP.c_pos; have hϕ0 := hP.ϕ_nonneg
  have hμΛ : 0 < P.μ - P.Λ1 := by linarith
  unfold sig
  split_ifs with h1 h3 h2 h3' h4
  · exact T3 P hP p θ h1 h3
  · have : P.c / P.μ < P.R - p :=
      lt_trans (div_lt_div_of_pos_left hc hμΛ (by linarith)) h1
    exact T2 P hP p θ this (lt_of_not_ge h3)
  · exact T4 P hP p θ (le_of_not_gt h1) h2
  · exact T5 P hP p θ h3'.1 (lt_of_not_ge h2) h3'.2
  · refine T2 P hP p θ h4 ?_
    by_contra hθ
    push Not at hθ
    have hθ' : P.R - p - θ ≤ P.ϕ / P.μ := by
      by_contra hh; exact h3' ⟨lt_of_not_ge hh, hθ⟩
    have e1 : P.c < (P.R - p) * P.μ := by rwa [div_lt_iff₀ hμ] at h4
    have e3 : θ * P.c ≤ (P.R - p) * (P.c - P.ϕ) := by rwa [le_div_iff₀ hc] at hθ
    have e4 : (P.R - p - θ) * P.μ ≤ P.ϕ := by rwa [le_div_iff₀ hμ] at hθ'
    have e5 : P.R - p - θ < P.ϕ / (P.μ - P.Λ1) := lt_of_not_ge h2
    rcases hϕ0.lt_or_eq with hϕ | hϕ
    · nlinarith
    · rw [← hϕ] at e5 e3; simp at e5; nlinarith
  · refine T1 P hP p θ (le_of_not_gt h4) ?_
    by_contra hh
    push Not at hh
    have hθ : (P.R - p) * (P.c - P.ϕ) / P.c < θ := by
      by_contra hθ; exact h3' ⟨hh, le_of_not_gt hθ⟩
    have e1 : (P.R - p) * P.μ ≤ P.c := by
      have := le_of_not_gt h4; rwa [le_div_iff₀ hμ] at this
    have e3 : (P.R - p) * (P.c - P.ϕ) < θ * P.c := by rwa [div_lt_iff₀ hc] at hθ
    have e4 : P.ϕ < (P.R - p - θ) * P.μ := by rwa [div_lt_iff₀ hμ] at hh
    nlinarith


lemma lamD_case1 (P : Params) (p θ : ℝ) (h1 : P.c / (P.μ - P.Λ1) < P.R - p) :
    (sig P p θ).lamD = if θ ≤ (P.R - p) * (P.c - P.ϕ) / P.c then P.Λ1 else 0 := by
  unfold sig; rw [if_pos h1]; split_ifs <;> rfl

lemma lamD_K (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) (p θ : ℝ)
    (h1 : ¬ P.c / (P.μ - P.Λ1) < P.R - p)
    (hθ1 : θ ≤ (P.R - p) * (P.c - P.ϕ) / P.c) (hθ2 : θ ≤ P.R - p - P.ϕ / P.μ) :
    (sig P p θ).lamD = min P.Λ1 (P.μ - P.ϕ / (P.R - p - θ)) := by
  have hμ := hP.μ_pos; have hΛ1' := hP.Λ1_lt_μ
  have hμΛ : 0 < P.μ - P.Λ1 := by linarith
  have hd : P.ϕ / P.μ ≤ P.R - p - θ := by linarith
  have hdpos : 0 < P.R - p - θ := lt_of_lt_of_le (div_pos hϕ hμ) hd
  unfold sig; rw [if_neg h1]
  split_ifs with h2 h3 h4
  · symm; apply min_eq_left
    have : P.ϕ / (P.R - p - θ) ≤ P.μ - P.Λ1 := by
      rw [div_le_iff₀ hdpos]; rw [div_le_iff₀ hμΛ] at h2; linarith
    linarith
  · symm; apply min_eq_right
    have : P.μ - P.Λ1 ≤ P.ϕ / (P.R - p - θ) := by
      rw [le_div_iff₀ hdpos]; have := lt_of_not_ge h2; rw [lt_div_iff₀ hμΛ] at this; linarith
    linarith
  all_goals
    have heq : P.R - p - θ = P.ϕ / P.μ := le_antisymm (by
      by_contra hh; exact h3 ⟨lt_of_not_ge hh, hθ1⟩) hd
    show (0:ℝ) = _
    have hh : P.ϕ / (P.ϕ / P.μ) = P.μ := by field_simp
    rw [heq, hh, sub_self, min_eq_right hP.Λ1_pos.le]

lemma lamD_out (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) (p θ : ℝ)
    (h1 : ¬ P.c / (P.μ - P.Λ1) < P.R - p)
    (hθ : (P.R - p) * (P.c - P.ϕ) / P.c < θ ∨ P.R - p - P.ϕ / P.μ < θ) :
    (sig P p θ).lamD = 0 := by
  have hμ := hP.μ_pos; have hΛ1' := hP.Λ1_lt_μ; have hc := hP.c_pos
  have hμΛ : 0 < P.μ - P.Λ1 := by linarith
  have hlt : P.ϕ / P.μ < P.ϕ / (P.μ - P.Λ1) :=
    div_lt_div_of_pos_left hϕ hμΛ (by linarith [hP.Λ1_pos])
  have n2 : ¬ P.ϕ / (P.μ - P.Λ1) ≤ P.R - p - θ := by
    intro h2
    rcases hθ with hθ | hθ
    · have e1 : P.R - p ≤ P.c / (P.μ - P.Λ1) := le_of_not_gt h1
      rw [le_div_iff₀ hμΛ] at e1
      rw [div_le_iff₀ hμΛ] at h2
      rw [div_lt_iff₀ hc] at hθ
      nlinarith
    · linarith
  have n3 : ¬ (P.ϕ / P.μ < P.R - p - θ ∧ θ ≤ (P.R - p) * (P.c - P.ϕ) / P.c) := by
    rintro ⟨ha, hb⟩
    rcases hθ with hθ | hθ <;> linarith
  unfold sig; rw [if_neg h1, if_neg n2, if_neg n3]
  split_ifs <;> rfl

lemma fee_exists (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) (p : ℝ) :
    ∃ θ, IsFeeBR (sig P) p θ := by
  have hμ := hP.μ_pos; have hΛ1 := hP.Λ1_pos; have hΛ1' := hP.Λ1_lt_μ; have hc := hP.c_pos
  have hϕc := hP.ϕ_lt_c
  have hμΛ : 0 < P.μ - P.Λ1 := by linarith
  by_cases h1 : P.c / (P.μ - P.Λ1) < P.R - p
  · have hapos : 0 < P.R - p := lt_trans (div_pos hc hμΛ) h1
    have h0 : 0 ≤ (P.R - p) * (P.c - P.ϕ) / P.c :=
      div_nonneg (mul_nonneg hapos.le (by linarith)) hc.le
    refine ⟨(P.R - p) * (P.c - P.ϕ) / P.c, h0, fun θ' hθ' => ?_⟩
    unfold platProfit
    rw [lamD_case1 P p _ h1, lamD_case1 P p _ h1, if_pos (le_refl _)]
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right h hΛ1.le
    · simp; exact mul_nonneg h0 hΛ1.le
  · set θ2 := min ((P.R - p) * (P.c - P.ϕ) / P.c) (P.R - p - P.ϕ / P.μ) with hθ2
    by_cases hneg : θ2 < 0
    · refine ⟨0, le_refl _, fun θ' hθ' => ?_⟩
      unfold platProfit
      have : (sig P p θ').lamD = 0 := by
        apply lamD_out P hP hϕ p θ' h1
        rcases min_lt_iff.mp (lt_of_lt_of_le hneg hθ') with h | h
        · exact Or.inl h
        · exact Or.inr h
      rw [this]; simp
    · push Not at hneg
      let g : ℝ → ℝ := fun θ => θ * min P.Λ1 (P.μ - P.ϕ / (P.R - p - θ))
      have hcont : ContinuousOn g (Set.Icc 0 θ2) := by
        apply ContinuousOn.mul continuousOn_id
        refine ContinuousOn.inf continuousOn_const ?_
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.div continuousOn_const (by fun_prop)
        intro x hx
        have : x ≤ P.R - p - P.ϕ / P.μ := le_trans hx.2 (min_le_right _ _)
        have := div_pos hϕ hμ
        intro h; linarith
      obtain ⟨θs, hθs, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_refl _, hneg⟩ hcont
      have hgK : ∀ θ ∈ Set.Icc 0 θ2, platProfit (sig P) p θ = g θ := by
        intro θ hθ
        unfold platProfit
        rw [lamD_K P hP hϕ p θ h1 (le_trans hθ.2 (min_le_left _ _))
          (le_trans hθ.2 (min_le_right _ _))]
      refine ⟨θs, hθs.1, fun θ' hθ' => ?_⟩
      rw [hgK θs hθs]
      by_cases hin : θ' ≤ θ2
      · rw [hgK θ' ⟨hθ', hin⟩]; exact hmax ⟨hθ', hin⟩
      · have : (sig P p θ').lamD = 0 := by
          apply lamD_out P hP hϕ p θ' h1
          rcases min_lt_iff.mp (lt_of_not_ge hin) with h | h
          · exact Or.inl h
          · exact Or.inr h
        unfold platProfit; rw [this, mul_zero]
        have := hmax (show (0:ℝ) ∈ Set.Icc 0 θ2 from ⟨le_refl _, hneg⟩)
        simpa [g] using this


/-- The body of Proposition 1 after choosing `ϕ1` and `ϕ`. -/
def Body (R μ c Λ0 ϕ1 ϕ : ℝ) : Prop :=
    ∃ l1 : ℝ, 0 < l1 ∧ l1 < μ ∧
    ∃ E : ℝ → Strategy,
      (∀ Λ1 ∈ Set.Ioo 0 μ, IsSPE ⟨R, μ, c, ϕ, Λ0, Λ1⟩ (E Λ1)) ∧
      let I : Set ℝ := if ϕ1 < ϕ then Set.Ioo 0 μ else Set.Ioc 0 l1
      ((∀ a ∈ I, ∀ b ∈ I, (E a).pStar = (E b).pStar) ∧
        (∀ a ∈ I, ∀ b ∈ I,
          (E a).lamDStar + (E a).lamWStar = (E b).lamDStar + (E b).lamWStar) ∧
        MonotoneOn (fun Λ1 => (E Λ1).platProfitStar) I ∧
        MonotoneOn (fun Λ1 => (E Λ1).welfareStar ⟨R, μ, c, ϕ, Λ0, Λ1⟩) I ∧
        MonotoneOn (fun Λ1 => (E Λ1).lamDStar) I ∧
        MonotoneOn (fun Λ1 => -(E Λ1).lamWStar) I) ∧
      (ϕ ≤ ϕ1 →
        (∀ a ∈ Set.Ioc 0 l1, ∀ b ∈ Set.Ioo l1 μ, (E a).pStar < (E b).pStar) ∧
        (∃ L : ℝ, Tendsto (fun Λ1 => (E Λ1).platProfitStar) (𝓝[>] l1) (𝓝 L) ∧
          L < (E l1).platProfitStar) ∧
        (∃ L : ℝ, Tendsto (fun Λ1 => (E Λ1).welfareStar ⟨R, μ, c, ϕ, Λ0, Λ1⟩) (𝓝[>] l1) (𝓝 L) ∧
          L < (E l1).welfareStar ⟨R, μ, c, ϕ, Λ0, l1⟩)) ∧
      (ϕ < c / (2 * Real.sqrt (R * μ / c) - 1) →
        c / (2 * Real.sqrt (R * μ / c) - 1) ≤ ϕ1 ∧
        ∃ L : ℝ, Tendsto (fun Λ1 => (E Λ1).lamDStar + (E Λ1).lamWStar) (𝓝[<] μ) (𝓝 L) ∧
          ∀ a ∈ Set.Ioc 0 l1, (E a).lamDStar + (E a).lamWStar < L)

lemma sqfacts (R μ c : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ) :
    ∃ s t : ℝ, 0 < t ∧ t < s ∧ s ^ 2 = R * μ ∧ t ^ 2 = c ∧
      Real.sqrt (c / μ * R) = t * s / μ ∧ Real.sqrt (c * μ / R) = t * μ / s ∧
      Real.sqrt (R * μ) = s ∧ Real.sqrt c = t := by
  have hRμ : 0 < R * μ := lt_trans hc hcR
  have hR : 0 < R := pos_of_mul_pos_left hRμ hμ.le
  have hs2 : Real.sqrt (R * μ) ^ 2 = R * μ := Real.sq_sqrt hRμ.le
  have ht2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hs := Real.sqrt_pos.2 hRμ
  have ht := Real.sqrt_pos.2 hc
  refine ⟨Real.sqrt (R * μ), Real.sqrt c, ht,
    Real.sqrt_lt_sqrt hc.le hcR, hs2, ht2, ?_, ?_, rfl, rfl⟩
  · have : c / μ * R = (Real.sqrt c * Real.sqrt (R * μ) / μ) ^ 2 := by
      rw [div_pow, mul_pow, hs2, ht2]; field_simp
    rw [this, Real.sqrt_sq (by positivity)]
  · have : c * μ / R = (Real.sqrt c * μ / Real.sqrt (R * μ)) ^ 2 := by
      rw [div_pow, mul_pow, hs2, ht2]; field_simp
    rw [this, Real.sqrt_sq (by positivity)]

lemma standing_of (R μ c ϕ Λ0 Λ1 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ0 : 0 ≤ ϕ) (hϕc : ϕ < c) (hΛ0 : μ ≤ Λ0) (hΛ1 : Λ1 ∈ Set.Ioo 0 μ) :
    Params.Standing ⟨R, μ, c, ϕ, Λ0, Λ1⟩ :=
  ⟨hμ, hc, hcR, hϕ0, hϕc, hΛ0, hΛ1.1, hΛ1.2⟩

lemma lamD0 (P : Params) (hP : P.Standing) (hϕ : P.ϕ = 0) (p θ : ℝ) :
    (sig P p θ).lamD = if θ ≤ P.R - p then P.Λ1 else 0 := by
  have hc := hP.c_pos
  have e : (P.R - p) * (P.c - P.ϕ) / P.c = P.R - p := by rw [hϕ]; field_simp; ring
  have e2 : P.ϕ / (P.μ - P.Λ1) = 0 := by rw [hϕ, zero_div]
  have e3 : P.ϕ / P.μ = 0 := by rw [hϕ, zero_div]
  unfold sig; rw [e, e2, e3]
  split_ifs <;> first | rfl | (exfalso; linarith)

lemma fee0_br (P : Params) (hP : P.Standing) (hϕ : P.ϕ = 0) (p : ℝ) :
    IsFeeBR (sig P) p (max (P.R - p) 0) := by
  refine ⟨le_max_right _ _, fun θ' hθ' => ?_⟩
  unfold platProfit
  rw [lamD0 P hP hϕ, lamD0 P hP hϕ]
  have hΛ1 := hP.Λ1_pos
  by_cases ha : 0 ≤ P.R - p
  · rw [max_eq_left ha, if_pos (le_refl _)]
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right h hΛ1.le
    · simp; exact mul_nonneg ha hΛ1.le
  · push Not at ha
    rw [max_eq_right ha.le, zero_mul, if_neg (by linarith), mul_zero]

lemma total0 (P : Params) (hP : P.Standing) (hϕ : P.ϕ = 0) (p : ℝ) :
    p * (sig P p (max (P.R - p) 0)).total ≤
      max ((Real.sqrt (P.R * P.μ) - Real.sqrt P.c) ^ 2) (P.R * P.Λ1) := by
  have hμ := hP.μ_pos; have hΛ1 := hP.Λ1_pos; have hΛ1' := hP.Λ1_lt_μ; have hc := hP.c_pos
  have hμΛ : 0 < P.μ - P.Λ1 := by linarith
  have e : (P.R - p) * (P.c - P.ϕ) / P.c = P.R - p := by rw [hϕ]; field_simp; ring
  obtain ⟨s, t, ht, hts, hs2, ht2, -, -, hs, htt⟩ := sqfacts P.R P.μ P.c hμ hc hP.c_lt_Rμ
  rw [hs, htt]
  by_cases h1 : P.c / (P.μ - P.Λ1) < P.R - p
  · have hapos : 0 < P.R - p := lt_trans (div_pos hc hμΛ) h1
    unfold sig
    rw [if_pos h1, max_eq_left hapos.le, e, if_pos (le_refl _)]
    simp only [Profile.total, Profile.lamW]
    apply le_trans _ (le_max_left _ _)
    have key : p * (P.μ - P.c / (P.R - p)) ≤ (s - t) ^ 2 := by
      set a := P.R - p with ha
      have hp : p = P.R - a := by ring
      rw [hp]
      rw [← sub_nonneg]
      have : (s - t) ^ 2 - (P.R - a) * (P.μ - P.c / a) = (s * t - a * P.μ) ^ 2 / (a * P.μ) := by
        field_simp
        rw [← ht2]
        have hR : P.R = s ^ 2 / P.μ := by field_simp; linarith
        rw [hR]; field_simp; ring
      rw [this]; positivity
    linarith
  · by_cases ha : 0 ≤ P.R - p
    · unfold sig
      rw [if_neg h1, max_eq_left ha, if_pos (by rw [hϕ, zero_div]; linarith)]
      simp only [Profile.total, Profile.lamW]
      apply le_trans _ (le_max_right _ _)
      nlinarith
    · have : (sig P p (max (P.R - p) 0)).total = 0 := by
        unfold sig
        push Not at ha
        rw [if_neg h1, max_eq_right ha.le, hϕ]
        have : ¬ P.c / P.μ < P.R - p := by
          have := div_pos hc hμ; linarith
        simp only [zero_div, sub_zero]
        rw [if_neg (by linarith), if_neg (by intro h; linarith [h.1]), if_neg this]
        simp [Profile.total, Profile.lamW]
      rw [this, mul_zero]
      exact le_trans (sq_nonneg _) (le_max_left _ _)


lemma case_zero (R μ c Λ0 ϕ1 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hΛ0 : μ ≤ Λ0) (hconst : c / (2 * Real.sqrt (R * μ / c) - 1) ≤ ϕ1)
    (hconstpos : 0 < c / (2 * Real.sqrt (R * μ / c) - 1)) :
    Body R μ c Λ0 ϕ1 0 := by
  obtain ⟨s, t, ht, hts, hs2, ht2, hsq1, hsq2, hs, htt⟩ := sqfacts R μ c hμ hc hcR
  have hR : 0 < R := pos_of_mul_pos_left (lt_trans hc hcR) hμ.le
  have hspos : 0 < s := lt_trans ht hts
  have hRe : R = s ^ 2 / μ := by field_simp; linarith
  set l1 := (s - t) ^ 2 / R with hl1
  set T0 := μ - t * μ / s with hT0
  set p0 := R - t * s / μ with hp0
  have hl1pos : 0 < l1 := by have : 0 < s - t := by linarith
                             positivity
  have hl1T0 : l1 < T0 := by
    rw [hl1, hT0, hRe, div_div_eq_mul_div, div_lt_iff₀ (by positivity)]
    have : 0 < s - t := by linarith
    field_simp
    nlinarith [mul_pos this ht, mul_pos (mul_pos this ht) hspos]
  have hT0μ : T0 < μ := by have : 0 < t * μ / s := by positivity
                           linarith
  have hl1μ : l1 < μ := lt_trans hl1T0 hT0μ
  have hp0pos : 0 < p0 := by
    rw [hp0, hRe, ← sub_div]; apply div_pos _ hμ; nlinarith
  have hap0 : R - p0 = t * s / μ := by rw [hp0]; ring
  have hcap : c / (t * s / μ) = t * μ / s := by rw [← ht2]; field_simp
  let P : ℝ → Params := fun Λ1 => ⟨R, μ, c, 0, Λ0, Λ1⟩
  let E : ℝ → Strategy := fun Λ1 =>
    ⟨sig (P Λ1), fun p => max (R - p) 0, if Λ1 ≤ l1 then p0 else R⟩
  have hSt : ∀ Λ1 ∈ Set.Ioo 0 μ, (P Λ1).Standing := fun Λ1 h =>
    standing_of R μ c 0 Λ0 Λ1 hμ hc hcR le_rfl hc hΛ0 h
  -- values on `(0, l1]`
  have valA : ∀ Λ1 ∈ Set.Ioc 0 l1,
      (E Λ1).pStar = p0 ∧ (E Λ1).lamDStar = Λ1 ∧ (E Λ1).lamWStar = T0 - Λ1 ∧
      (E Λ1).platProfitStar = t * s / μ * Λ1 ∧
      (E Λ1).welfareStar (P Λ1) = (s - t) ^ 2 + t * s / μ * Λ1 ∧
      restProfit (E Λ1).σ (E Λ1).fee (E Λ1).price = (s - t) ^ 2 := by
    intro Λ1 hΛ
    have hpr : (E Λ1).price = p0 := if_pos hΛ.2
    have hfee : (E Λ1).fee p0 = t * s / μ := by
      show max (R - p0) 0 = _; rw [hap0, max_eq_left (by positivity)]
    have hΛT : Λ1 < T0 := lt_of_le_of_lt hΛ.2 hl1T0
    have hμΛ : 0 < μ - Λ1 := by linarith
    have h1 : c / (μ - Λ1) < R - p0 := by
      rw [hap0, div_lt_iff₀ hμΛ, ← ht2]
      have : t * μ / s < μ - Λ1 := by linarith
      rw [div_lt_iff₀ hspos] at this
      field_simp; nlinarith
    have hsig : (E Λ1).σ p0 (t * s / μ) = ⟨Λ1, 0, μ - c / (R - p0) - Λ1⟩ := by
      show sig (P Λ1) p0 (t * s / μ) = _
      unfold sig
      rw [if_pos h1, if_pos]
      show t * s / μ ≤ (R - p0) * (c - 0) / c
      rw [hap0, sub_zero, mul_div_cancel_right₀ _ hc.ne']
    have hstar : (E Λ1).σ (E Λ1).price ((E Λ1).fee (E Λ1).price) = ⟨Λ1, 0, T0 - Λ1⟩ := by
      rw [hpr, hfee, hsig, hap0, hcap]
    have hrest : restProfit (E Λ1).σ (E Λ1).fee (E Λ1).price = (s - t) ^ 2 := by
      unfold restProfit
      rw [hstar]; simp only [Profile.total, Profile.lamW]; rw [hpr, hp0, hT0, hRe]
      field_simp; ring
    refine ⟨hpr, by unfold Strategy.lamDStar; rw [hstar], ?_, ?_, ?_, hrest⟩
    · unfold Strategy.lamWStar; rw [hstar]; simp [Profile.lamW]
    · unfold Strategy.platProfitStar platProfit; rw [hstar, show (E Λ1).fee (E Λ1).price = t * s / μ by rw [hpr, hfee]]
    · unfold Strategy.welfareStar welfare
      rw [hrest]
      unfold platProfit
      rw [hstar, show (E Λ1).fee (E Λ1).price = t * s / μ by rw [hpr, hfee], hpr]
      simp only [Profile.total, Profile.lamW, UD, UW]
      have e1 : μ - (Λ1 + (T0 - Λ1 + 0)) = t * μ / s := by rw [hT0]; ring
      rw [e1]
      have e2 : R - p0 - c / (t * μ / s) = 0 := by
        rw [hap0, ← ht2]; field_simp; ring
      have e3 : R - p0 - t * s / μ - 0 / (t * μ / s) = 0 := by rw [hap0]; ring
      show (s - t) ^ 2 + t * s / μ * Λ1 + Λ1 * (R - p0 - t * s / μ - 0 / (t * μ / s))
        + (T0 - Λ1 + 0) * (R - p0 - c / (t * μ / s)) = _
      rw [e2, e3]; ring
  -- values on `(l1, μ)`
  have valB : ∀ Λ1 ∈ Set.Ioo l1 μ,
      (E Λ1).pStar = R ∧ (E Λ1).lamDStar = Λ1 ∧ (E Λ1).lamWStar = 0 ∧
      (E Λ1).platProfitStar = 0 ∧ (E Λ1).welfareStar (P Λ1) = R * Λ1 ∧
      restProfit (E Λ1).σ (E Λ1).fee (E Λ1).price = R * Λ1 := by
    intro Λ1 hΛ
    have hpr : (E Λ1).price = R := if_neg (not_le.mpr hΛ.1)
    have hfee : (E Λ1).fee R = 0 := by show max (R - R) 0 = 0; simp
    have hμΛ : 0 < μ - Λ1 := by linarith [hΛ.2]
    have hstar : (E Λ1).σ (E Λ1).price ((E Λ1).fee (E Λ1).price) = ⟨Λ1, 0, 0⟩ := by
      rw [hpr, hfee]
      show sig (P Λ1) R 0 = _
      unfold sig
      rw [if_neg (by show ¬ c / (μ - Λ1) < R - R; rw [sub_self]; exact not_lt.mpr (div_pos hc hμΛ).le),
        if_pos (by show (0:ℝ) / (μ - Λ1) ≤ R - R - 0; simp)]
    have hrest : restProfit (E Λ1).σ (E Λ1).fee (E Λ1).price = R * Λ1 := by
      unfold restProfit; rw [hstar, hpr]; simp [Profile.total, Profile.lamW]
    refine ⟨hpr, by unfold Strategy.lamDStar; rw [hstar], by unfold Strategy.lamWStar; rw [hstar]; simp [Profile.lamW], ?_, ?_, hrest⟩
    · unfold Strategy.platProfitStar platProfit; rw [hstar, hpr, hfee, zero_mul]
    · unfold Strategy.welfareStar welfare
      rw [hrest]; unfold platProfit; rw [hstar, hpr, hfee]
      simp [Profile.total, Profile.lamW, UD, UW, P]
  have hSPE : ∀ Λ1 ∈ Set.Ioo 0 μ, IsSPE ⟨R, μ, c, 0, Λ0, Λ1⟩ (E Λ1) := by
    intro Λ1 hΛ
    have hP := hSt Λ1 hΛ
    refine ⟨fun p θ _ _ => sig_cust _ hP p θ, fun p _ => fee0_br _ hP rfl p, ?_, ?_⟩
    · show 0 ≤ (E Λ1).price
      by_cases h : Λ1 ≤ l1
      · rw [show (E Λ1).price = p0 from if_pos h]; exact hp0pos.le
      · rw [show (E Λ1).price = R from if_neg h]; exact hR.le
    · intro p' _
      have hb := total0 (P Λ1) hP rfl p'
      have hb' : restProfit (E Λ1).σ (E Λ1).fee p' ≤ max ((s - t) ^ 2) (R * Λ1) := by
        rw [← hs, ← htt]; exact hb
      refine le_trans hb' ?_
      by_cases h : Λ1 ≤ l1
      · rw [(valA Λ1 ⟨hΛ.1, h⟩).2.2.2.2.2]
        apply max_le le_rfl
        rw [hl1, le_div_iff₀ hR] at h; linarith
      · rw [(valB Λ1 ⟨lt_of_not_ge h, hΛ.2⟩).2.2.2.2.2]
        apply max_le _ le_rfl
        have := lt_of_not_ge h
        rw [hl1, div_lt_iff₀ hR] at this; linarith
  refine ⟨l1, hl1pos, hl1μ, E, hSPE, ?_⟩
  simp only [if_neg (show ¬ (ϕ1 < 0) by linarith)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ => ⟨?_, ?_, ?_⟩, fun _ => ⟨hconst, ?_⟩⟩
  · intro a ha b hb; rw [(valA a ha).1, (valA b hb).1]
  · intro a ha b hb
    rw [(valA a ha).2.1, (valA a ha).2.2.1, (valA b hb).2.1, (valA b hb).2.2.1]; ring
  · intro a ha b hb hab
    simp only; rw [(valA a ha).2.2.2.1, (valA b hb).2.2.2.1]
    exact mul_le_mul_of_nonneg_left hab (by positivity)
  · intro a ha b hb hab
    simp only; rw [(valA a ha).2.2.2.2.1, (valA b hb).2.2.2.2.1]
    have := mul_le_mul_of_nonneg_left hab (show 0 ≤ t * s / μ by positivity)
    linarith
  · intro a ha b hb hab
    simp only; rw [(valA a ha).2.1, (valA b hb).2.1]; exact hab
  · intro a ha b hb hab
    simp only; rw [(valA a ha).2.2.1, (valA b hb).2.2.1]; linarith
  · intro a ha b hb
    rw [(valA a ha).1, (valB b hb).1, hp0]
    have : 0 < t * s / μ := by positivity
    linarith
  · refine ⟨0, ?_, ?_⟩
    · apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT hl1μ] with x hx
      rw [(valB x hx).2.2.2.1]
    · rw [(valA l1 ⟨hl1pos, le_rfl⟩).2.2.2.1]; positivity
  · refine ⟨R * l1, ?_, ?_⟩
    · have : Tendsto (fun x : ℝ => R * x) (𝓝[>] l1) (𝓝 (R * l1)) :=
        ((continuous_const.mul continuous_id).tendsto l1).mono_left nhdsWithin_le_nhds
      apply this.congr'
      filter_upwards [Ioo_mem_nhdsGT hl1μ] with x hx
      rw [(valB x hx).2.2.2.2.1]
    · have := (valA l1 ⟨hl1pos, le_rfl⟩).2.2.2.2.1
      rw [this]
      have e : R * l1 = (s - t) ^ 2 := by rw [hl1]; field_simp
      rw [e]
      have : 0 < t * s / μ * l1 := by positivity
      linarith
  · refine ⟨μ, ?_, ?_⟩
    · have : Tendsto (fun x : ℝ => x) (𝓝[<] μ) (𝓝 μ) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      apply this.congr'
      filter_upwards [Ioo_mem_nhdsLT hl1μ] with x hx
      rw [(valB x hx).2.1, (valB x hx).2.2.1, add_zero]
    · intro a ha
      rw [(valA a ha).2.1, (valA a ha).2.2.1]; linarith


noncomputable def pTf (R μ c ϕ Λ1 : ℝ) : ℝ :=
  if ϕ ≤ phi1 R μ c then
    (if Λ1 ≤ lam1 R μ c ϕ then R - Real.sqrt (c / μ * R)
      else if Λ1 ≤ lam2 R μ ϕ then R - μ * ϕ / (μ - Λ1) ^ 2
      else 2 * R * (μ - chi R μ ϕ) / (2 * μ - chi R μ ϕ))
  else R - Real.sqrt (c / μ * R)

noncomputable def VTf (R μ c ϕ Λ1 : ℝ) : ℝ :=
  if ϕ ≤ phi1 R μ c then
    (if Λ1 ≤ lam1 R μ c ϕ then (Real.sqrt (R * μ) - Real.sqrt c) ^ 2
      else if Λ1 ≤ lam2 R μ ϕ then Λ1 * (R - μ * ϕ / (μ - Λ1) ^ 2)
      else 2 * R * (μ - chi R μ ϕ) ^ 2 / (2 * μ - chi R μ ϕ))
  else (Real.sqrt (R * μ) - Real.sqrt c) ^ 2

noncomputable def TTf (R μ c ϕ Λ1 : ℝ) : ℝ :=
  if ϕ ≤ phi1 R μ c then
    (if Λ1 ≤ lam1 R μ c ϕ then μ - Real.sqrt (c * μ / R)
      else if Λ1 ≤ lam2 R μ ϕ then Λ1
      else μ - chi R μ ϕ)
  else μ - Real.sqrt (c * μ / R)

noncomputable def θTf (R μ c ϕ Λ1 : ℝ) : ℝ :=
  if ϕ ≤ phi1 R μ c then
    (if Λ1 ≤ lam1 R μ c ϕ then (c - ϕ) * Real.sqrt (R / (μ * c))
      else if Λ1 ≤ lam2 R μ ϕ then ϕ * Λ1 / (μ - Λ1) ^ 2
      else R * chi R μ ϕ * (μ - chi R μ ϕ) / (μ * (2 * μ - chi R μ ϕ)))
  else
    (if Λ1 ≤ μ - Real.sqrt (c * μ / R) then (c - ϕ) * Real.sqrt (R / (c * μ))
      else (c - ϕ) * Real.sqrt (R / (c * μ)))

noncomputable def πTf (R μ c ϕ Λ1 : ℝ) : ℝ :=
  if ϕ ≤ phi1 R μ c then
    (if Λ1 ≤ lam1 R μ c ϕ then Λ1 * (c - ϕ) * Real.sqrt (R / (c * μ))
      else if Λ1 ≤ lam2 R μ ϕ then ϕ * Λ1 ^ 2 / (μ - Λ1) ^ 2
      else R * chi R μ ϕ * (μ - chi R μ ϕ) ^ 2 / (μ * (2 * μ - chi R μ ϕ)))
  else
    (if Λ1 ≤ μ - Real.sqrt (c * μ / R) then Λ1 * (c - ϕ) * Real.sqrt (R / (c * μ))
      else (c - ϕ) * (Real.sqrt (R * μ / c) - 1))

noncomputable def DTf (R μ c ϕ Λ1 : ℝ) : ℝ :=
  if ϕ ≤ phi1 R μ c then
    (if Λ1 ≤ lam1 R μ c ϕ then Λ1 else if Λ1 ≤ lam2 R μ ϕ then Λ1 else μ - chi R μ ϕ)
  else
    (if Λ1 ≤ μ - Real.sqrt (c * μ / R) then Λ1 else μ - Real.sqrt (c * μ / R))

noncomputable def WTf (R μ c ϕ Λ1 : ℝ) : ℝ :=
  if ϕ ≤ phi1 R μ c then
    (if Λ1 ≤ lam1 R μ c ϕ then μ - Real.sqrt (c * μ / R) - Λ1 else if Λ1 ≤ lam2 R μ ϕ then 0 else 0)
  else
    (if Λ1 ≤ μ - Real.sqrt (c * μ / R) then μ - Real.sqrt (c * μ / R) - Λ1 else 0)

noncomputable def STf (R μ c ϕ Λ1 : ℝ) : ℝ :=
  if ϕ ≤ phi1 R μ c then
    (if Λ1 ≤ lam1 R μ c ϕ then (Real.sqrt (R * μ) - Real.sqrt c) ^ 2 + Λ1 * (c - ϕ) * Real.sqrt (R / (c * μ))
      else if Λ1 ≤ lam2 R μ ϕ then R * Λ1 - ϕ * Λ1 / (μ - Λ1)
      else R * (2 * μ + chi R μ ϕ) * (μ - chi R μ ϕ) ^ 2 / (μ * (2 * μ - chi R μ ϕ)))
  else
    (if Λ1 ≤ μ - Real.sqrt (c * μ / R) then
        (Real.sqrt (R * μ) - Real.sqrt c) ^ 2 + Λ1 * (c - ϕ) * Real.sqrt (R / (c * μ))
      else ϕ + R * μ - (c + ϕ) * Real.sqrt (R * μ / c))

lemma C4' (R μ c ϕ Λ0 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) (hΛ0 : μ ≤ Λ0) :
    (∀ Λ1 ∈ Set.Ioo 0 μ, ∀ (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ),
      (∀ p θ : ℝ, 0 ≤ p → 0 ≤ θ → IsCustEq ⟨R, μ, c, ϕ, Λ0, Λ1⟩ p θ (σ p θ)) →
      (∀ p : ℝ, 0 ≤ p → IsFeeBR σ p (fee p)) →
      IsOptPrice σ fee (pTf R μ c ϕ Λ1) ∧ restProfit σ fee (pTf R μ c ϕ Λ1) = VTf R μ c ϕ Λ1 ∧
        (σ (pTf R μ c ϕ Λ1) (fee (pTf R μ c ϕ Λ1))).total = TTf R μ c ϕ Λ1) ∧
    (ϕ ≤ phi1 R μ c → ∀ a ∈ Set.Ioc 0 (lam1 R μ c ϕ), ∀ b ∈ Set.Ioo (lam1 R μ c ϕ) μ,
      pTf R μ c ϕ a < pTf R μ c ϕ b) ∧
    MonotoneOn (VTf R μ c ϕ) (Set.Ioo 0 μ) ∧
    (ϕ < c / (2 * Real.sqrt (R * μ / c) - 1) →
      c / (2 * Real.sqrt (R * μ / c) - 1) ≤ phi1 R μ c ∧
        μ - Real.sqrt (c * μ / R) < lam2 R μ ϕ) :=
  prop_C_4 R μ c ϕ Λ0 hμ hc hcR hϕ hϕc hΛ0

lemma C3' (R μ c ϕ Λ0 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) (hΛ0 : μ ≤ Λ0) :
    (∀ Λ1 ∈ Set.Ioo 0 μ, ∀ (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ),
      (∀ p θ : ℝ, 0 ≤ p → 0 ≤ θ → IsCustEq ⟨R, μ, c, ϕ, Λ0, Λ1⟩ p θ (σ p θ)) →
      (∀ p : ℝ, 0 ≤ p → IsFeeBR σ p (fee p)) →
      fee (pTf R μ c ϕ Λ1) = θTf R μ c ϕ Λ1 ∧
        platProfit σ (pTf R μ c ϕ Λ1) (fee (pTf R μ c ϕ Λ1)) = πTf R μ c ϕ Λ1 ∧
        (σ (pTf R μ c ϕ Λ1) (fee (pTf R μ c ϕ Λ1))).lamD = DTf R μ c ϕ Λ1 ∧
        (σ (pTf R μ c ϕ Λ1) (fee (pTf R μ c ϕ Λ1))).lamW = WTf R μ c ϕ Λ1) ∧
    (ϕ ≤ phi1 R μ c → ∃ L : ℝ, Tendsto (πTf R μ c ϕ) (𝓝[>] (lam1 R μ c ϕ)) (𝓝 L) ∧
      L < πTf R μ c ϕ (lam1 R μ c ϕ)) ∧
    (phi1 R μ c < ϕ → MonotoneOn (πTf R μ c ϕ) (Set.Ioo 0 μ)) :=
  cor_C_3 R μ c ϕ Λ0 hμ hc hcR hϕ hϕc hΛ0

lemma C4w' (R μ c ϕ Λ0 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) (hΛ0 : μ ≤ Λ0) :
    (∀ Λ1 ∈ Set.Ioo 0 μ, ∀ (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ),
      (∀ p θ : ℝ, 0 ≤ p → 0 ≤ θ → IsCustEq ⟨R, μ, c, ϕ, Λ0, Λ1⟩ p θ (σ p θ)) →
      (∀ p : ℝ, 0 ≤ p → IsFeeBR σ p (fee p)) →
      welfare ⟨R, μ, c, ϕ, Λ0, Λ1⟩ σ fee (pTf R μ c ϕ Λ1) = STf R μ c ϕ Λ1) ∧
    (ϕ ≤ phi1 R μ c → ∃ L : ℝ, Tendsto (STf R μ c ϕ) (𝓝[>] (lam1 R μ c ϕ)) (𝓝 L) ∧
      L < STf R μ c ϕ (lam1 R μ c ϕ)) ∧
    (phi1 R μ c < ϕ → MonotoneOn (STf R μ c ϕ) (Set.Ioo 0 μ)) :=
  cor_C_4 R μ c ϕ Λ0 hμ hc hcR hϕ hϕc hΛ0


lemma case_pos (R μ c Λ0 ϕ : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hΛ0 : μ ≤ Λ0) (hϕ : 0 < ϕ) (hϕc : ϕ < c) :
    Body R μ c Λ0 (phi1 R μ c) ϕ := by
  obtain ⟨s, t, ht, hts, hs2, ht2, hsq1, hsq2, hs, htt⟩ := sqfacts R μ c hμ hc hcR
  have hR : 0 < R := pos_of_mul_pos_left (lt_trans hc hcR) hμ.le
  have hspos : 0 < s := lt_trans ht hts
  have hRe : R = s ^ 2 / μ := by field_simp; linarith
  let P : ℝ → Params := fun Λ1 => ⟨R, μ, c, ϕ, Λ0, Λ1⟩
  have hSt : ∀ Λ1 ∈ Set.Ioo 0 μ, (P Λ1).Standing := fun Λ1 h =>
    standing_of R μ c ϕ Λ0 Λ1 hμ hc hcR hϕ.le hϕc hΛ0 h
  let feeF : ℝ → ℝ → ℝ := fun Λ1 p => Classical.epsilon (fun θ => IsFeeBR (sig (P Λ1)) p θ)
  have hfee : ∀ Λ1 ∈ Set.Ioo 0 μ, ∀ p, IsFeeBR (sig (P Λ1)) p (feeF Λ1 p) :=
    fun Λ1 h p => Classical.epsilon_spec (fee_exists (P Λ1) (hSt Λ1 h) hϕ p)
  have hcu : ∀ Λ1 ∈ Set.Ioo 0 μ, ∀ p θ : ℝ, 0 ≤ p → 0 ≤ θ →
      IsCustEq ⟨R, μ, c, ϕ, Λ0, Λ1⟩ p θ (sig (P Λ1) p θ) :=
    fun Λ1 h p θ _ _ => sig_cust (P Λ1) (hSt Λ1 h) p θ
  have hfe : ∀ Λ1 ∈ Set.Ioo 0 μ, ∀ p : ℝ, 0 ≤ p → IsFeeBR (sig (P Λ1)) p (feeF Λ1 p) :=
    fun Λ1 h p _ => hfee Λ1 h p
  let E : ℝ → Strategy := fun Λ1 => ⟨sig (P Λ1), feeF Λ1, pTf R μ c ϕ Λ1⟩
  obtain ⟨C4t, C4i, -, C4iii⟩ := C4' R μ c ϕ Λ0 hμ hc hcR hϕ hϕc hΛ0
  obtain ⟨C3t, C3i, C3ii⟩ := C3' R μ c ϕ Λ0 hμ hc hcR hϕ hϕc hΛ0
  obtain ⟨Swt, Swi, Swii⟩ := C4w' R μ c ϕ Λ0 hμ hc hcR hϕ hϕc hΛ0
  have hSPE : ∀ Λ1 ∈ Set.Ioo 0 μ, IsSPE ⟨R, μ, c, ϕ, Λ0, Λ1⟩ (E Λ1) := fun Λ1 h =>
    ⟨hcu Λ1 h, hfe Λ1 h, (C4t Λ1 h _ _ (hcu Λ1 h) (hfe Λ1 h)).1⟩
  have vP : ∀ Λ1, (E Λ1).pStar = pTf R μ c ϕ Λ1 := fun _ => rfl
  have vT : ∀ Λ1 ∈ Set.Ioo 0 μ, (E Λ1).lamDStar + (E Λ1).lamWStar = TTf R μ c ϕ Λ1 :=
    fun Λ1 h => (C4t Λ1 h _ _ (hcu Λ1 h) (hfe Λ1 h)).2.2
  have vπ : ∀ Λ1 ∈ Set.Ioo 0 μ, (E Λ1).platProfitStar = πTf R μ c ϕ Λ1 :=
    fun Λ1 h => (C3t Λ1 h _ _ (hcu Λ1 h) (hfe Λ1 h)).2.1
  have vD : ∀ Λ1 ∈ Set.Ioo 0 μ, (E Λ1).lamDStar = DTf R μ c ϕ Λ1 :=
    fun Λ1 h => (C3t Λ1 h _ _ (hcu Λ1 h) (hfe Λ1 h)).2.2.1
  have vW : ∀ Λ1 ∈ Set.Ioo 0 μ, (E Λ1).lamWStar = WTf R μ c ϕ Λ1 :=
    fun Λ1 h => (C3t Λ1 h _ _ (hcu Λ1 h) (hfe Λ1 h)).2.2.2
  have vS : ∀ Λ1 ∈ Set.Ioo 0 μ, (E Λ1).welfareStar ⟨R, μ, c, ϕ, Λ0, Λ1⟩ = STf R μ c ϕ Λ1 :=
    fun Λ1 h => Swt Λ1 h _ _ (hcu Λ1 h) (hfe Λ1 h)
  have hl2 : lam2 R μ ϕ ∈ Set.Ioo 0 μ := (lemma_C_8 R μ c ϕ hμ hc hcR hϕ hϕc).2.2.1.1
  set T0 := μ - Real.sqrt (c * μ / R) with hT0
  have hK : 0 ≤ Real.sqrt (R / (c * μ)) := Real.sqrt_nonneg _
  have hcϕ : 0 ≤ c - ϕ := by linarith
  by_cases hA : phi1 R μ c < ϕ
  · have nB : ¬ ϕ ≤ phi1 R μ c := not_le.mpr hA
    refine ⟨μ / 2, by linarith, by linarith, E, hSPE, ?_⟩
    simp only [if_pos hA]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun h => absurd h nB, fun h => ?_⟩
    · intro a _ b _; rw [vP, vP]; simp only [pTf, if_neg nB]
    · intro a ha b hb; rw [vT a ha, vT b hb]; simp only [TTf, if_neg nB]
    · intro a ha b hb hab; simp only; rw [vπ a ha, vπ b hb]; exact C3ii hA ha hb hab
    · intro a ha b hb hab; simp only; rw [vS a ha, vS b hb]; exact Swii hA ha hb hab
    · intro a ha b hb hab; simp only; rw [vD a ha, vD b hb]; simp only [DTf, if_neg nB, ← hT0]
      split_ifs <;> linarith
    · intro a ha b hb hab; simp only; rw [vW a ha, vW b hb]; simp only [WTf, if_neg nB, ← hT0]
      split_ifs <;> linarith
    · exfalso; have := (C4iii h).1; linarith
  · have hB : ϕ ≤ phi1 R μ c := le_of_not_gt hA
    -- bounds on `λ1`
    have hl1 : 0 < lam1 R μ c ϕ ∧ lam1 R μ c ϕ < μ := by
      set S := {l : ℝ | l ∈ Set.Ioo 0 μ ∧
        deliveryCurve R μ ϕ l = (Real.sqrt (R * μ) - Real.sqrt c) ^ 2} with hS
      have hlam : lam1 R μ c ϕ = sInf S := rfl
      by_cases hne : S.Nonempty
      · have lb : ∀ l ∈ S, (s - t) ^ 2 / R ≤ l := by
          intro l hl
          obtain ⟨⟨hl0, hlμ⟩, hdc⟩ := hl
          rw [hs, htt] at hdc
          unfold deliveryCurve at hdc
          rw [div_le_iff₀ hR, ← hdc]
          have : 0 ≤ μ * ϕ / (μ - l) ^ 2 := by
            have : 0 < μ - l := by linarith
            positivity
          nlinarith
        obtain ⟨l0, hl0⟩ := hne
        have hpos : 0 < (s - t) ^ 2 / R := by
          have : 0 < s - t := by linarith
          positivity
        refine ⟨lt_of_lt_of_le hpos ?_, ?_⟩
        · rw [hlam]; exact le_csInf ⟨l0, hl0⟩ lb
        · rw [hlam]
          exact lt_of_le_of_lt (csInf_le ⟨0, fun l hl => hl.1.1.le⟩ hl0) hl0.1.2
      · exfalso
        have hS0 : lam1 R μ c ϕ = 0 := by
          rw [hlam, Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]
        have hT0pos : 0 < T0 := by
          rw [hT0, hsq2]
          have : t * μ / s < μ := by rw [div_lt_iff₀ hspos]; nlinarith
          linarith
        have hcμ : 0 < (c - ϕ) / c * μ := by
          have : 0 < c - ϕ := by linarith
          positivity
        have hst : 0 < (s - t) ^ 2 / R := by
          have : 0 < s - t := by linarith
          positivity
        obtain ⟨Λ1, hΛ1⟩ : ∃ x : ℝ,
            x = min (min T0 ((c - ϕ) / c * μ)) (min (lam2 R μ ϕ) ((s - t) ^ 2 / R)) / 2 :=
          ⟨_, rfl⟩
        have hm : 0 < min (min T0 ((c - ϕ) / c * μ)) (min (lam2 R μ ϕ) ((s - t) ^ 2 / R)) :=
          lt_min (lt_min hT0pos hcμ) (lt_min hl2.1 hst)
        have hΛpos : 0 < Λ1 := by rw [hΛ1]; linarith
        have hle1 : Λ1 < T0 := by
          have := min_le_left (min T0 ((c - ϕ) / c * μ)) (min (lam2 R μ ϕ) ((s - t) ^ 2 / R))
          have := min_le_left T0 ((c - ϕ) / c * μ); rw [hΛ1]; linarith
        have hle2 : Λ1 ≤ (c - ϕ) / c * μ := by
          have := min_le_left (min T0 ((c - ϕ) / c * μ)) (min (lam2 R μ ϕ) ((s - t) ^ 2 / R))
          have := min_le_right T0 ((c - ϕ) / c * μ); rw [hΛ1]; linarith
        have hle3 : Λ1 ≤ lam2 R μ ϕ := by
          have := min_le_right (min T0 ((c - ϕ) / c * μ)) (min (lam2 R μ ϕ) ((s - t) ^ 2 / R))
          have := min_le_left (lam2 R μ ϕ) ((s - t) ^ 2 / R); rw [hΛ1]; linarith
        have hle4 : Λ1 < (s - t) ^ 2 / R := by
          have := min_le_right (min T0 ((c - ϕ) / c * μ)) (min (lam2 R μ ϕ) ((s - t) ^ 2 / R))
          have := min_le_right (lam2 R μ ϕ) ((s - t) ^ 2 / R); rw [hΛ1]; linarith
        have hΛ : Λ1 ∈ Set.Ioo 0 μ := ⟨hΛpos, lt_of_le_of_lt hle3 hl2.2⟩
        obtain ⟨hopt, hval, -⟩ := C4t Λ1 hΛ _ _ (hcu Λ1 hΛ) (hfe Λ1 hΛ)
        have hV : VTf R μ c ϕ Λ1 = Λ1 * (R - μ * ϕ / (μ - Λ1) ^ 2) := by
          simp only [VTf, if_pos hB, hS0, if_neg (not_le.mpr hΛpos), if_pos hle3]
        set p0 := R - Real.sqrt (c / μ * R) with hp0
        have hap0 : R - p0 = t * s / μ := by rw [hp0, hsq1]; ring
        have hp0pos : 0 < p0 := by
          rw [hp0, hsq1, hRe, ← sub_div]; apply div_pos _ hμ; nlinarith
        have hμΛ : 0 < μ - Λ1 := by linarith [hΛ.2]
        have hp0le : p0 ≤ R - c / (μ - Λ1) := by
          have : c / (μ - Λ1) ≤ t * s / μ := by
            rw [div_le_div_iff₀ hμΛ hμ, ← ht2]
            rw [hT0, hsq2] at hle1
            have : t * μ / s < μ - Λ1 := by linarith
            rw [div_lt_iff₀ hspos] at this
            nlinarith
          linarith
        have hC2 : restProfit (sig (P Λ1)) (feeF Λ1) p0 = p0 * (μ - c / (R - p0)) :=
          ((cor_C_2 (P Λ1) (hSt Λ1 hΛ) hϕ (sig (P Λ1)) (feeF Λ1) (hcu Λ1 hΛ)
            (hfe Λ1 hΛ)).1 hle2 p0 hp0pos.le).1 hp0le
        have hval0 : p0 * (μ - c / (R - p0)) = (s - t) ^ 2 := by
          rw [hap0, hp0, hsq1, hRe, ← ht2]; field_simp
        have h1 := hopt.2 p0 hp0pos.le
        rw [hC2, hval0, hval, hV] at h1
        have : Λ1 * (R - μ * ϕ / (μ - Λ1) ^ 2) ≤ Λ1 * R :=
          mul_le_mul_of_nonneg_left (sub_le_self _ (div_nonneg (mul_nonneg hμ.le hϕ.le)
            (sq_nonneg _))) hΛpos.le
        rw [lt_div_iff₀ hR] at hle4
        linarith
    have hsub : ∀ a ∈ Set.Ioc 0 (lam1 R μ c ϕ), a ∈ Set.Ioo 0 μ := fun a ha => ⟨ha.1, lt_of_le_of_lt ha.2 hl1.2⟩
    refine ⟨(lam1 R μ c ϕ), hl1.1, hl1.2, E, hSPE, ?_⟩
    simp only [if_neg hA]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ => ⟨?_, ?_, ?_⟩, fun h => ?_⟩
    · intro a ha b hb; rw [vP, vP]; simp only [pTf, if_pos hB, if_pos ha.2, if_pos hb.2]
    · intro a ha b hb; rw [vT a (hsub a ha), vT b (hsub b hb)]
      simp only [TTf, if_pos hB, if_pos ha.2, if_pos hb.2]
    · intro a ha b hb hab; simp only; rw [vπ a (hsub a ha), vπ b (hsub b hb)]
      simp only [πTf, if_pos hB, if_pos ha.2, if_pos hb.2]
      linarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab hcϕ) hK]
    · intro a ha b hb hab; simp only; rw [vS a (hsub a ha), vS b (hsub b hb)]
      simp only [STf, if_pos hB, if_pos ha.2, if_pos hb.2]
      linarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab hcϕ) hK]
    · intro a ha b hb hab; simp only; rw [vD a (hsub a ha), vD b (hsub b hb)]
      simp only [DTf, if_pos hB, if_pos ha.2, if_pos hb.2]; exact hab
    · intro a ha b hb hab; simp only; rw [vW a (hsub a ha), vW b (hsub b hb)]
      simp only [WTf, if_pos hB, if_pos ha.2, if_pos hb.2]; linarith
    · intro a ha b hb; rw [vP, vP]; exact C4i hB a ha b hb
    · obtain ⟨L, hL, hLlt⟩ := C3i hB
      refine ⟨L, ?_, ?_⟩
      · apply hL.congr'
        filter_upwards [Ioo_mem_nhdsGT hl1.2] with x hx
        rw [vπ x ⟨lt_trans hl1.1 hx.1, hx.2⟩]
      · rw [vπ (lam1 R μ c ϕ) ⟨hl1.1, hl1.2⟩]; exact hLlt
    · obtain ⟨L, hL, hLlt⟩ := Swi hB
      refine ⟨L, ?_, ?_⟩
      · apply hL.congr'
        filter_upwards [Ioo_mem_nhdsGT hl1.2] with x hx
        rw [vS x ⟨lt_trans hl1.1 hx.1, hx.2⟩]
      · rw [vS (lam1 R μ c ϕ) ⟨hl1.1, hl1.2⟩]; exact hLlt
    · obtain ⟨hc1, hTl⟩ := C4iii h
      refine ⟨hc1, lam2 R μ ϕ, ?_, ?_⟩
      · apply tendsto_const_nhds.congr'
        have hmax : max (lam1 R μ c ϕ) (lam2 R μ ϕ) < μ := max_lt hl1.2 hl2.2
        filter_upwards [Ioo_mem_nhdsLT hmax] with x hx
        have hx1 : (lam1 R μ c ϕ) < x := lt_of_le_of_lt (le_max_left _ _) hx.1
        have hx2 : lam2 R μ ϕ < x := lt_of_le_of_lt (le_max_right _ _) hx.1
        rw [vT x ⟨lt_trans hl1.1 hx1, hx.2⟩]
        simp only [TTf, if_pos hB, if_neg (not_le.mpr hx1), if_neg (not_le.mpr hx2)]
        rfl
      · intro a ha
        rw [vT a (hsub a ha)]
        simp only [TTf, if_pos hB, if_pos ha.2]
        exact hTl

end FDProp1Aux

open FDProp1Aux in
theorem solution (R μ c Λ0 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hΛ0 : μ ≤ Λ0) :
    ∃ ϕ1 : ℝ, ∀ ϕ : ℝ, 0 ≤ ϕ → ϕ < c →
    ∃ l1 : ℝ, 0 < l1 ∧ l1 < μ ∧
    ∃ E : ℝ → Strategy,
      (∀ Λ1 ∈ Set.Ioo 0 μ, IsSPE ⟨R, μ, c, ϕ, Λ0, Λ1⟩ (E Λ1)) ∧
      let I : Set ℝ := if ϕ1 < ϕ then Set.Ioo 0 μ else Set.Ioc 0 l1
      -- (i) / (ii)
      ((∀ a ∈ I, ∀ b ∈ I, (E a).pStar = (E b).pStar) ∧
        (∀ a ∈ I, ∀ b ∈ I,
          (E a).lamDStar + (E a).lamWStar = (E b).lamDStar + (E b).lamWStar) ∧
        MonotoneOn (fun Λ1 => (E Λ1).platProfitStar) I ∧
        MonotoneOn (fun Λ1 => (E Λ1).welfareStar ⟨R, μ, c, ϕ, Λ0, Λ1⟩) I ∧
        MonotoneOn (fun Λ1 => (E Λ1).lamDStar) I ∧
        MonotoneOn (fun Λ1 => -(E Λ1).lamWStar) I) ∧
      -- otherwise
      (ϕ ≤ ϕ1 →
        (∀ a ∈ Set.Ioc 0 l1, ∀ b ∈ Set.Ioo l1 μ, (E a).pStar < (E b).pStar) ∧
        (∃ L : ℝ, Tendsto (fun Λ1 => (E Λ1).platProfitStar) (𝓝[>] l1) (𝓝 L) ∧
          L < (E l1).platProfitStar) ∧
        (∃ L : ℝ, Tendsto (fun Λ1 => (E Λ1).welfareStar ⟨R, μ, c, ϕ, Λ0, Λ1⟩) (𝓝[>] l1) (𝓝 L) ∧
          L < (E l1).welfareStar ⟨R, μ, c, ϕ, Λ0, l1⟩)) ∧
      -- furthermore
      (ϕ < c / (2 * Real.sqrt (R * μ / c) - 1) →
        c / (2 * Real.sqrt (R * μ / c) - 1) ≤ ϕ1 ∧
        ∃ L : ℝ, Tendsto (fun Λ1 => (E Λ1).lamDStar + (E Λ1).lamWStar) (𝓝[<] μ) (𝓝 L) ∧
          ∀ a ∈ Set.Ioc 0 l1, (E a).lamDStar + (E a).lamWStar < L) := by
  have hk : 1 < Real.sqrt (R * μ / c) := by
    rw [Real.lt_sqrt zero_le_one, one_pow, one_lt_div hc]; exact hcR
  have hden : 1 < 2 * Real.sqrt (R * μ / c) - 1 := by linarith
  have hconstpos : 0 < c / (2 * Real.sqrt (R * μ / c) - 1) := div_pos hc (by linarith)
  have hconstlt : c / (2 * Real.sqrt (R * μ / c) - 1) < c := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  have hconst : c / (2 * Real.sqrt (R * μ / c) - 1) ≤ phi1 R μ c :=
    ((C4' R μ c (c / (2 * Real.sqrt (R * μ / c) - 1) / 2) Λ0 hμ hc hcR (by linarith)
      (by linarith) hΛ0).2.2.2 (by linarith)).1
  refine ⟨phi1 R μ c, fun ϕ hϕ0 hϕc => ?_⟩
  rcases hϕ0.lt_or_eq with hϕ | hϕ
  · exact case_pos R μ c Λ0 ϕ hμ hc hcR hΛ0 hϕ hϕc
  · subst hϕ
    exact case_zero R μ c Λ0 (phi1 R μ c) hμ hc hcR hΛ0 hconst hconstpos
