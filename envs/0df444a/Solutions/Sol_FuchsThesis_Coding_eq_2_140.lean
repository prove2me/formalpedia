-- Prove2me | solution 1 for FuchsThesis.Coding.eq_2_140
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:47:46.469343+00:00
-- url     : https://prove2.me/submissions/990f0224-9f1d-44a5-ace1-34107006498b

import Mathlib
import Definitions.Def_FuchsThesis_Coding_IsInstantaneous
import Definitions.Def_FuchsThesis_Coding_expLength
import Definitions.Def_BBPSSW_Distill_shannonBits

namespace Aux_Fuchs_2140
open FuchsThesis.Coding

theorem ud {ι : Type*} (c : ι → List Bool) (hc : IsInstantaneous c) (hne : ∀ x, c x ≠ []) :
    InformationTheory.UniquelyDecodable (Set.range c) := by
  intro L₁
  induction L₁ with
  | nil =>
    intro L₂ _ h₂ heq
    rcases L₂ with _ | ⟨w, L₂⟩
    · rfl
    · exfalso
      simp only [List.flatten_nil, List.flatten_cons] at heq
      obtain ⟨x, hx⟩ := h₂ w List.mem_cons_self
      have : w = [] := (List.append_eq_nil_iff.mp heq.symm).1
      exact hne x (hx.trans this)
  | cons w L ih =>
    intro L₂ h₁ h₂ heq
    obtain ⟨x, hx⟩ := h₁ w List.mem_cons_self
    rcases L₂ with _ | ⟨w', L₂⟩
    · exfalso
      simp only [List.flatten_nil, List.flatten_cons] at heq
      have : w = [] := (List.append_eq_nil_iff.mp heq).1
      exact hne x (hx.trans this)
    · simp only [List.flatten_cons] at heq
      obtain ⟨y, hy⟩ := h₂ w' List.mem_cons_self
      have hww : w = w' := by
        by_contra hneq
        have hxy : x ≠ y := fun h => hneq (by rw [← hx, ← hy, h])
        have p1 : w <+: w ++ L.flatten := List.prefix_append _ _
        have p2 : w' <+: w ++ L.flatten := heq ▸ List.prefix_append _ _
        rcases List.prefix_or_prefix_of_prefix p1 p2 with h | h
        · exact hc x y hxy (by rw [hx, hy]; exact h)
        · exact hc y x (Ne.symm hxy) (by rw [hx, hy]; exact h)
      subst hww
      have := List.append_cancel_left heq
      rw [ih L₂ (fun v hv => h₁ v (List.mem_cons_of_mem _ hv))
        (fun v hv => h₂ v (List.mem_cons_of_mem _ hv)) this]

theorem term (p : ℝ) (hp : 0 ≤ p) (ℓ : ℕ) :
    p - (1 / 2 : ℝ) ^ ℓ ≤ (p * (ℓ : ℝ) + p * Real.logb 2 p) * Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 < (1 / 2 : ℝ) ^ ℓ := by positivity
  have e : (p * (ℓ : ℝ) + p * Real.logb 2 p) * Real.log 2 = p * ℓ * Real.log 2 + p * Real.log p := by
    unfold Real.logb; field_simp
  rw [e]
  rcases hp.eq_or_lt with h | h
  · rw [← h]; nlinarith [hq]
  · have hlq : Real.log ((1 / 2 : ℝ) ^ ℓ) = -(ℓ * Real.log 2) := by
      rw [Real.log_pow, one_div, Real.log_inv]; ring
    have := Real.log_le_sub_one_of_pos (div_pos hq h)
    rw [Real.log_div hq.ne' h.ne', hlq] at this
    have h2 := mul_le_mul_of_nonneg_left this h.le
    have h3 : p * ((1 / 2 : ℝ) ^ ℓ / p - 1) = (1 / 2 : ℝ) ^ ℓ - p := by field_simp
    rw [h3] at h2
    nlinarith

end Aux_Fuchs_2140

open FuchsThesis.Coding Aux_Fuchs_2140 in
theorem solution {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (c : ι → List Bool) (hc : IsInstantaneous c) :
    expLength p c - BBPSSW.Distill.shannonBits p ≥ 0 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hE : ∃ x, c x = []
  · obtain ⟨x, hx⟩ := hE
    have hall : ∀ y, y = x := by
      intro y; by_contra h
      exact hc x y (Ne.symm h) (by rw [hx]; exact List.nil_prefix)
    have hsum : ∀ f : ι → ℝ, ∑ i, f i = f x := fun f =>
      Fintype.sum_eq_single x (fun y hy => absurd (hall y) hy)
    have hpx : p x = 1 := by rw [← hsum p, hp1]
    unfold expLength BBPSSW.Distill.shannonBits
    rw [hsum, hsum, hx, hpx]
    simp
  · push_neg at hE
    have hinj : Function.Injective c := by
      intro x y h
      by_contra hxy
      exact hc x y hxy (by rw [h])
    have hK := InformationTheory.kraft_mcmillan_inequality (S := Finset.univ.image c) (α := Bool) (by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact ud c hc hE)
    rw [Finset.sum_image (fun x _ y _ h => hinj h)] at hK
    simp only [Fintype.card_bool, Nat.cast_ofNat] at hK
    have hterm : ∀ i, (p i - (1 / 2 : ℝ) ^ (c i).length) / Real.log 2 ≤
        p i * ((c i).length : ℝ) + p i * Real.logb 2 (p i) := by
      intro i
      rw [div_le_iff₀ hl2]
      exact term (p i) (hp0 i) _
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hp1, Finset.sum_add_distrib] at hs
    have : 0 ≤ (1 - ∑ i, (1 / 2 : ℝ) ^ (c i).length) / Real.log 2 :=
      div_nonneg (by linarith) hl2.le
    unfold expLength BBPSSW.Distill.shannonBits
    linarith
