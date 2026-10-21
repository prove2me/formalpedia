-- Prove2me | solution 1 for DynOpaque.TwoPeriod.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T02:04:07.151357+00:00
-- url     : https://prove2.me/submissions/fafb3bbe-2305-42ec-84f6-7c852f295c82

import Mathlib
import Definitions.Def_DynOpaque_TwoPeriod_Model
import Theorems.Thm_DynOpaque_TwoPeriod_objectives_3_to_6
import Theorems.Thm_DynOpaque_TwoPeriod_benchmark_transparent
import Theorems.Thm_DynOpaque_TwoPeriod_case_vHL_vL_dominated
import Theorems.Thm_DynOpaque_TwoPeriod_lemma_4_corrected
import Theorems.Thm_DynOpaque_TwoPeriod_lemma_2_corners_dominated

namespace DynOpaqueProp1Aux
open DynOpaque.TwoPeriod

noncomputable def f (α c d x y : ℝ) : ℝ := x * (d - c * x) + (α * x + (1 - α) * y) * (d - c * y)

theorem boundI (α c d x y : ℝ) (hD : 0 < 4 - 4 * α - α ^ 2) :
    (4 - 4 * α - α ^ 2) * c * f α c d x y ≤ 2 * (1 - α) * d ^ 2 := by
  have key : (4 - 4 * α - α ^ 2) * (2 * (1 - α) * d ^ 2 - (4 - 4 * α - α ^ 2) * c * f α c d x y) =
      ((4 - 4 * α - α ^ 2) * c * x - (2 - α - α ^ 2) * d +
          α * ((4 - 4 * α - α ^ 2) * c * y - (2 - 3 * α - α ^ 2) * d) / 2) ^ 2 +
        (4 - 4 * α - α ^ 2) * ((4 - 4 * α - α ^ 2) * c * y - (2 - 3 * α - α ^ 2) * d) ^ 2 / 4 := by
    unfold f; ring
  have hr : 0 ≤ (4 - 4 * α - α ^ 2) * (2 * (1 - α) * d ^ 2 - (4 - 4 * α - α ^ 2) * c * f α c d x y) := by
    rw [key]; positivity
  have := (mul_nonneg_iff_of_pos_left hD).1 hr
  linarith

theorem boundII (α c d x y : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (hk : 0 ≤ α ^ 2 + 3 * α - 2)
    (hc : 0 < c) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    4 * c * f α c d x y ≤ (1 + α) ^ 2 * d ^ 2 := by
  have key : (1 + α) ^ 2 * ((1 + α) ^ 2 * d ^ 2 - 4 * c * f α c d x y) =
      ((1 + α) * ((1 + α) * d - 2 * c * x) - 2 * c * (1 - α) * y) ^ 2 +
        4 * c ^ 2 * (1 - α) * (α ^ 2 + 3 * α) * y ^ 2 +
        4 * c ^ 2 * (1 + α) * (α ^ 2 + 3 * α - 2) * x * y := by
    unfold f; ring
  have h1a : 0 ≤ 1 - α := by linarith
  have hr : 0 ≤ (1 + α) ^ 2 * ((1 + α) ^ 2 * d ^ 2 - 4 * c * f α c d x y) := by
    rw [key]
    have : 0 ≤ 4 * c ^ 2 * (1 - α) * (α ^ 2 + 3 * α) * y ^ 2 := by positivity
    have : 0 ≤ 4 * c ^ 2 * (1 + α) * (α ^ 2 + 3 * α - 2) * x * y := by positivity
    positivity
  have hp : 0 < (1 + α) ^ 2 := by positivity
  have := (mul_nonneg_iff_of_pos_left hp).1 hr
  linarith

theorem sqrt17_lt (α : ℝ) (h0 : 0 ≤ α) (h : α < (Real.sqrt 17 - 3) / 2) : α ^ 2 + 3 * α < 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  have hs0 := Real.sqrt_nonneg 17
  nlinarith

theorem sqrt17_ge (α : ℝ) (h0 : 0 ≤ α) (h : (Real.sqrt 17 - 3) / 2 ≤ α) : 0 ≤ α ^ 2 + 3 * α - 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  have hs0 := Real.sqrt_nonneg 17
  nlinarith

theorem obj3_eq (vH vL cH cL α x y : ℝ) :
    obj3 vH vL cH cL α x y = f α (cH - cL) (vHL vH vL - cL) x y := by
  unfold obj3 f; ring

theorem profI (α c d : ℝ) (hD : 4 - 4 * α - α ^ 2 ≠ 0) (hc : c ≠ 0) :
    (2 - α - α ^ 2) * d / ((4 - 4 * α - α ^ 2) * c) * (d - c * ((2 - α - α ^ 2) * d / ((4 - 4 * α - α ^ 2) * c))) +
     (α * ((2 - α - α ^ 2) * d / ((4 - 4 * α - α ^ 2) * c)) + (1 - α) * ((2 - 3 * α - α ^ 2) * d / ((4 - 4 * α - α ^ 2) * c))) *
      (d - c * ((2 - 3 * α - α ^ 2) * d / ((4 - 4 * α - α ^ 2) * c))) =
    2 * (1 - α) * d ^ 2 / ((4 - 4 * α - α ^ 2) * c) := by
  generalize hDD : 4 - 4 * α - α ^ 2 = D at *
  field_simp
  linear_combination (-2 * d ^ 2 * (1 - α)) * hDD

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

/-- Every feasible policy earns at most `B` once `B` bounds objective (3) on the box and
dominates the transparent benchmark. -/
theorem all_le (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) (B : ℝ)
    (h3 : ∀ x ∈ box, obj3 vH vL cH cL α x.1 x.2 ≤ B)
    (hM : 2 * max (vH - cH) (vL - cL) ≤ B) :
    ∀ Q : Policy, Feasible vH vL Q → profit vH vL cH cL α Q ≤ B := by
  have hS' := hS
  obtain ⟨hv, hc, h0, h1, hl⟩ := hS'
  have h4 : ∀ x ∈ box, obj4 vH vL cH cL x.1 x.2 ≤ B := by
    intro x hx
    obtain ⟨y, hy, hle⟩ := case_vHL_vL_dominated vH vL cH cL α hS x hx
    exact le_trans hle (max_le (h3 y hy) hM)
  have h5 : ∀ x ∈ box, obj5 vH vL cH cL α x.1 x.2 ≤ B := by
    intro x hx
    obtain ⟨hi, hii, hiii⟩ := lemma_4_corrected vH vL cH cL α hS
    obtain ⟨y, hy, hy01, hle⟩ := hi x hx
    have hy2 : y.2 ∈ Set.Icc (0 : ℝ) 1 := hy.2
    rcases hy01 with h | h
    · obtain ⟨z, hz, hle2⟩ := hiii y.2 hy2
      rw [h] at hle
      exact le_trans hle (le_trans hle2 (h4 z hz))
    · rw [h] at hle
      have hb : ((1 : ℝ), y.2) ∈ box := ⟨⟨by norm_num, by norm_num⟩, hy2⟩
      exact le_trans hle (le_trans (hii y.2 hy2) (h3 _ hb))
  have h6 : ∀ x ∈ box, obj6 vL cH cL x.1 x.2 ≤ B := by
    rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
    have := le_max_right (vH - cH) (vL - cL)
    simp only [obj6]
    nlinarith
  intro Q hQ
  cases Q with
  | transparent m q₁ q₂ =>
    exact le_trans ((benchmark_transparent vH vL cH cL α hS).1 m q₁ q₂) hM
  | «opaque» p₁ p₂ ξ₁ ξ₂ =>
    obtain ⟨hp1, hp2, ⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := hQ
    have hbox : (ξ₁, ξ₂) ∈ box := ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
    have hh : 0 ≤ α * ξ₁ + (1 - α) * ξ₂ := by
      have : 0 ≤ 1 - α := by linarith
      positivity
    obtain ⟨e3, e4, e5, e6⟩ := objectives_3_to_6 vH vL cH cL α hS ξ₁ ξ₂
    have b3 := h3 _ hbox
    have b4 := h4 _ hbox
    have b5 := h5 _ hbox
    have b6 := h6 _ hbox
    simp only at b3 b4 b5 b6
    simp only [profit, opaqueProfit] at e3 e4 e5 e6 ⊢
    rcases term_le vH vL cH cL ξ₁ ξ₁ p₁ hv hp1 hx0 with t1 | t1 <;>
    rcases term_le vH vL cH cL (α * ξ₁ + (1 - α) * ξ₂) ξ₂ p₂ hv hp2 hh with t2 | t2 <;>
    linarith

end DynOpaqueProp1Aux

open DynOpaque.TwoPeriod DynOpaqueProp1Aux

theorem solution (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) :
    ((0 ≤ α ∧ α < alphaBar ∧
        (vHL vH vL - cL) / (cH - cL) < (4 - 4 * α - α ^ 2) / (2 - α - α ^ 2) ∧
        (1 - α) * (vHL vH vL - cL) ^ 2 / ((4 - 4 * α - α ^ 2) * (cH - cL)) >
          max (vH - cH) (vL - cL)) →
      IsOptimal vH vL cH cL α
          (Policy.opaque (vHL vH vL) (vHL vH vL)
            ((2 - α - α ^ 2) * (vHL vH vL - cL) / ((4 - 4 * α - α ^ 2) * (cH - cL)))
            ((2 - 3 * α - α ^ 2) * (vHL vH vL - cL) / ((4 - 4 * α - α ^ 2) * (cH - cL)))) ∧
        profit vH vL cH cL α
            (Policy.opaque (vHL vH vL) (vHL vH vL)
              ((2 - α - α ^ 2) * (vHL vH vL - cL) / ((4 - 4 * α - α ^ 2) * (cH - cL)))
              ((2 - 3 * α - α ^ 2) * (vHL vH vL - cL) / ((4 - 4 * α - α ^ 2) * (cH - cL)))) =
          2 * (1 - α) * (vHL vH vL - cL) ^ 2 / ((4 - 4 * α - α ^ 2) * (cH - cL))) ∧
    ((alphaBar ≤ α ∧ α ≤ 1 ∧
        (vHL vH vL - cL) / (cH - cL) < 2 / (1 + α) ∧
        (1 + α) ^ 2 * (vHL vH vL - cL) ^ 2 / (8 * (cH - cL)) > max (vH - cH) (vL - cL)) →
      IsOptimal vH vL cH cL α
          (Policy.opaque (vHL vH vL) (vHL vH vL)
            ((1 + α) * (vHL vH vL - cL) / (2 * (cH - cL))) 0) ∧
        profit vH vL cH cL α
            (Policy.opaque (vHL vH vL) (vHL vH vL)
              ((1 + α) * (vHL vH vL - cL) / (2 * (cH - cL))) 0) =
          (1 + α) ^ 2 * (vHL vH vL - cL) ^ 2 / (4 * (cH - cL))) ∧
    (¬ (0 ≤ α ∧ α < alphaBar ∧
        (vHL vH vL - cL) / (cH - cL) < (4 - 4 * α - α ^ 2) / (2 - α - α ^ 2) ∧
        (1 - α) * (vHL vH vL - cL) ^ 2 / ((4 - 4 * α - α ^ 2) * (cH - cL)) >
          max (vH - cH) (vL - cL)) →
      ¬ (alphaBar ≤ α ∧ α ≤ 1 ∧
        (vHL vH vL - cL) / (cH - cL) < 2 / (1 + α) ∧
        (1 + α) ^ 2 * (vHL vH vL - cL) ^ 2 / (8 * (cH - cL)) > max (vH - cH) (vL - cL)) →
      (vH - cH ≥ vL - cL →
          IsOptimal vH vL cH cL α (Policy.transparent Version.H vH vH) ∧
            profit vH vL cH cL α (Policy.transparent Version.H vH vH) = 2 * (vH - cH)) ∧
        (vL - cL ≥ vH - cH →
          IsOptimal vH vL cH cL α (Policy.transparent Version.L vL vL) ∧
            profit vH vL cH cL α (Policy.transparent Version.L vL vL) = 2 * (vL - cL))) := by
  have hS' := hS
  obtain ⟨hv, hc, h0, h1, hl⟩ := hS'
  have hc0 : 0 < cH - cL := by linarith
  have hd0 : 0 < vHL vH vL - cL := by unfold vHL; linarith
  have hTr := benchmark_transparent vH vL cH cL α hS
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨-, ha, hx, hval⟩
    have hk := sqrt17_lt α h0 (by unfold alphaBar at ha; exact ha)
    have hq : 0 < 2 - α - α ^ 2 := by nlinarith
    have hD : 0 < 4 - 4 * α - α ^ 2 := by nlinarith
    have hr : 0 < 2 - 3 * α - α ^ 2 := by linarith
    rw [div_lt_div_iff₀ hc0 hq] at hx
    have hprof : profit vH vL cH cL α
        (Policy.opaque (vHL vH vL) (vHL vH vL)
          ((2 - α - α ^ 2) * (vHL vH vL - cL) / ((4 - 4 * α - α ^ 2) * (cH - cL)))
          ((2 - 3 * α - α ^ 2) * (vHL vH vL - cL) / ((4 - 4 * α - α ^ 2) * (cH - cL)))) =
        2 * (1 - α) * (vHL vH vL - cL) ^ 2 / ((4 - 4 * α - α ^ 2) * (cH - cL)) := by
      simp only [profit]
      rw [(objectives_3_to_6 vH vL cH cL α hS _ _).1, obj3_eq]
      unfold f
      have hDne : (4 - 4 * α - α ^ 2) ≠ 0 := ne_of_gt (by nlinarith)
      have hcne : cH - cL ≠ 0 := ne_of_gt hc0
      exact profI α _ _ hDne hcne
    refine ⟨⟨?_, fun Q hQ => ?_⟩, hprof⟩
    · refine ⟨le_rfl, le_rfl, ⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩⟩
      · rw [div_le_one (by positivity)]; linarith
      · rw [div_le_one (by positivity)]; nlinarith
    · rw [hprof]
      apply all_le vH vL cH cL α hS _ _ _ Q hQ
      · rintro ⟨x, y⟩ _
        rw [obj3_eq, le_div_iff₀ (by positivity)]
        have := boundI α (cH - cL) (vHL vH vL - cL) x y hD
        linarith
      · have : 2 * (1 - α) * (vHL vH vL - cL) ^ 2 / ((4 - 4 * α - α ^ 2) * (cH - cL)) =
            2 * ((1 - α) * (vHL vH vL - cL) ^ 2 / ((4 - 4 * α - α ^ 2) * (cH - cL))) := by ring
        linarith
  · rintro ⟨ha, ha1, hx, hval⟩
    have hk := sqrt17_ge α h0 (by unfold alphaBar at ha; exact ha)
    have hp : 0 < 1 + α := by linarith
    rw [div_lt_div_iff₀ hc0 hp] at hx
    have hprof : profit vH vL cH cL α
        (Policy.opaque (vHL vH vL) (vHL vH vL)
          ((1 + α) * (vHL vH vL - cL) / (2 * (cH - cL))) 0) =
        (1 + α) ^ 2 * (vHL vH vL - cL) ^ 2 / (4 * (cH - cL)) := by
      simp only [profit]
      rw [(objectives_3_to_6 vH vL cH cL α hS _ _).1, obj3_eq]
      unfold f
      field_simp
      ring
    refine ⟨⟨?_, fun Q hQ => ?_⟩, hprof⟩
    · refine ⟨le_rfl, le_rfl, ⟨by positivity, ?_⟩, ⟨le_rfl, zero_le_one⟩⟩
      rw [div_le_one (by positivity)]; linarith
    · rw [hprof]
      apply all_le vH vL cH cL α hS _ _ _ Q hQ
      · rintro ⟨x, y⟩ ⟨⟨hx0, _⟩, ⟨hy0, _⟩⟩
        rw [obj3_eq, le_div_iff₀ (by positivity)]
        have := boundII α (cH - cL) (vHL vH vL - cL) x y h0 ha1 hk hc0 hx0 hy0
        linarith
      · have : (1 + α) ^ 2 * (vHL vH vL - cL) ^ 2 / (4 * (cH - cL)) =
            2 * ((1 + α) ^ 2 * (vHL vH vL - cL) ^ 2 / (8 * (cH - cL))) := by
          field_simp; ring
        linarith
  · intro hni hnii
    have h3 : ∀ x ∈ box, obj3 vH vL cH cL α x.1 x.2 ≤ 2 * max (vH - cH) (vL - cL) := by
      rintro ⟨x, y⟩ hxy
      have hxy' := hxy
      obtain ⟨⟨hx0, _⟩, ⟨hy0, _⟩⟩ := hxy'
      by_cases ha : α < alphaBar
      · by_cases hx' : (vHL vH vL - cL) / (cH - cL) < (4 - 4 * α - α ^ 2) / (2 - α - α ^ 2)
        · have hval : ¬ ((1 - α) * (vHL vH vL - cL) ^ 2 / ((4 - 4 * α - α ^ 2) * (cH - cL)) >
              max (vH - cH) (vL - cL)) := fun hv => hni ⟨h0, ha, hx', hv⟩
          push_neg at hval
          have hk := sqrt17_lt α h0 (by unfold alphaBar at ha; exact ha)
          have hD : 0 < 4 - 4 * α - α ^ 2 := by nlinarith
          have hb : obj3 vH vL cH cL α x y ≤
              2 * ((1 - α) * (vHL vH vL - cL) ^ 2 / ((4 - 4 * α - α ^ 2) * (cH - cL))) := by
            rw [obj3_eq]
            have e : 2 * ((1 - α) * (vHL vH vL - cL) ^ 2 / ((4 - 4 * α - α ^ 2) * (cH - cL))) =
                2 * (1 - α) * (vHL vH vL - cL) ^ 2 / ((4 - 4 * α - α ^ 2) * (cH - cL)) := by ring
            rw [e, le_div_iff₀ (by positivity)]
            have := boundI α (cH - cL) (vHL vH vL - cL) x y hD
            linarith
          simp only
          linarith
        · exact lemma_2_corners_dominated vH vL cH cL α hS (Or.inl ⟨ha, le_of_not_gt hx'⟩) _ hxy
      · push_neg at ha
        by_cases hx' : (vHL vH vL - cL) / (cH - cL) < 2 / (1 + α)
        · have hval : ¬ ((1 + α) ^ 2 * (vHL vH vL - cL) ^ 2 / (8 * (cH - cL)) >
              max (vH - cH) (vL - cL)) := fun hv => hnii ⟨ha, h1, hx', hv⟩
          push_neg at hval
          have hk := sqrt17_ge α h0 (by unfold alphaBar at ha; exact ha)
          have hb : obj3 vH vL cH cL α x y ≤
              2 * ((1 + α) ^ 2 * (vHL vH vL - cL) ^ 2 / (8 * (cH - cL))) := by
            rw [obj3_eq]
            have e : 2 * ((1 + α) ^ 2 * (vHL vH vL - cL) ^ 2 / (8 * (cH - cL))) =
                (1 + α) ^ 2 * (vHL vH vL - cL) ^ 2 / (4 * (cH - cL)) := by
              field_simp; ring
            rw [e, le_div_iff₀ (by positivity)]
            have := boundII α (cH - cL) (vHL vH vL - cL) x y h0 h1 hk hc0 hx0 hy0
            linarith
          simp only
          linarith
        · exact lemma_2_corners_dominated vH vL cH cL α hS
            (Or.inr ⟨ha, h1, le_of_not_gt hx'⟩) _ hxy
    have key := all_le vH vL cH cL α hS _ h3 le_rfl
    refine ⟨fun hge => ⟨⟨trivial, fun Q hQ => ?_⟩, hTr.2.1⟩,
      fun hge => ⟨⟨trivial, fun Q hQ => ?_⟩, hTr.2.2⟩⟩
    · rw [show profit vH vL cH cL α (Policy.transparent Version.H vH vH) = 2 * (vH - cH) from hTr.2.1]
      have := key Q hQ
      rw [max_eq_left hge] at this
      exact this
    · rw [show profit vH vL cH cL α (Policy.transparent Version.L vL vL) = 2 * (vL - cL) from hTr.2.2]
      have := key Q hQ
      rw [max_eq_right hge] at this
      exact this
