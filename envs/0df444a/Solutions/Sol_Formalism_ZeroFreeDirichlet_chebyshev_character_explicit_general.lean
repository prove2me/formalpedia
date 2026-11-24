-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.chebyshev_character_explicit_general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:00:23.869612+00:00
-- url     : https://prove2.me/submissions/29dd210e-9800-48bc-8f31-418e4cc1f677

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExistsContourAvoidingRealZero
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ChebyshevCharacterExplicitGeneral
import Theorems.Thm_Formalism_ZF_norm_integral_compl_le
import Theorems.Thm_Formalism_ZeroFreeDirichlet_exists_contour_avoiding_real_zero
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_analytic_conductor_mono
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_conductor_pos_real
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_sum_le_of_card_le_one
import Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_contour_decomposition
import Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_horizontal_segment_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_left_line_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_right_line_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_real_zero_residue_term_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
set_option maxHeartbeats 1000000
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (hP : PerronChi) (hRS : RectShiftChi) (c₁ C C₀ : ℝ) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1 / 20) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset ℝ) (hχ : χ ≠ 1)
    (hE : ExcZeros c₁ χ B)
    (hD : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
        ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2)
    (hR : ∀ s : ℂ, 1 < s.re → ‖negLD χ s‖ ≤ 1 / (s.re - 1) + C₀)
    (y T L : ℝ) (hy : 2 ≤ y) (hT : 1 ≤ T) (hL : Real.log ((q : ℝ) * (T + 2)) = L) :
    ∃ σ₁ : ℝ, σ₁ ≤ 1 - c₁ / (4 * L) ∧
      ‖Schi χ y - negLD χ 1 * y + ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤
        2 * Real.pi * ((Real.log y + C₀) * (Real.exp 1 * y)) / T
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 24 * L / c₁) * y ^ σ₁ * (8 * L / c₁) * (2 * T)
        + y ^ σ₁ * (8 * L / c₁) := by
  obtain ⟨hBc, hBz, hBall⟩ := hE
  have hy0 : (0:ℝ) < y := by linarith
  have hy1 : (1:ℝ) ≤ y := by linarith
  have hy1' : (1:ℝ) < y := by linarith
  have hlog2 : (1:ℝ) / 2 < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h
    linarith
  have hlogy2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hly : (1:ℝ) / 2 < Real.log y := by linarith
  have hlogy : 0 < Real.log y := by linarith
  have hlogyne : Real.log y ≠ 0 := hlogy.ne'
  have hT0 : (0:ℝ) < T := by linarith
  have hTabs : |T| = T := abs_of_pos hT0
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    exact_mod_cast hq
  have hL2 : Real.log 2 ≤ L := by
    rw [← hL]
    exact Real.log_le_log (by norm_num) (by nlinarith)
  have hLh : (1:ℝ) / 2 < L := by linarith
  have hL0 : 0 < L := by linarith
  have hLne : L ≠ 0 := hL0.ne'
  have hc₁ne : c₁ ≠ 0 := hc₁.ne'
  have ha : 0 < c₁ / L := div_pos hc₁ hL0
  have haL : c₁ / L * L = c₁ := by field_simp
  have ha' : c₁ / L ≤ 1 / 10 := by nlinarith
  have e3 : c₁ / (3 * L) = c₁ / L / 3 := by rw [mul_comm 3 L, ← div_div]
  have e4 : c₁ / (4 * L) = c₁ / L / 4 := by rw [mul_comm 4 L, ← div_div]
  have e2 : c₁ / 2 / L = c₁ / L / 2 := div_right_comm c₁ 2 L
  have h2ε : 2 / (c₁ / (4 * L)) = 8 * L / c₁ := by rw [div_div_eq_mul_div]; ring
  have h1δ : 1 / (c₁ / (24 * L)) = 24 * L / c₁ := one_div_div _ _
  obtain ⟨σ₁, hσ₁c, hσ₁B⟩ := exists_contour_avoiding_real_zero B hBc L c₁ hL0 hc₁
  rw [e3, e4] at hσ₁c
  have hσ₁b : 1 - c₁ / L / 3 ≤ σ₁ ∧ σ₁ ≤ 1 - c₁ / L / 4 := by
    rcases hσ₁c with h | h <;> rw [h] <;> constructor <;> linarith
  obtain ⟨hσ₁lo, hσ₁up⟩ := hσ₁b
  refine ⟨σ₁, by rw [e4]; exact hσ₁up, ?_⟩
  have hσ₁lt1 : σ₁ < 1 := by linarith
  have hσ₁pos : 0 < σ₁ := by linarith
  have hhalf : 1 / 2 ≤ σ₁ := by linarith
  have hgap : c₁ / (4 * L) ≤ 1 - σ₁ := by rw [e4]; linarith
  have hσ₁reg : 1 - c₁ / 2 / Real.log ((q : ℝ) * (T + 2)) ≤ σ₁ := by
    rw [hL, e2]; linarith

  obtain ⟨σ₀, hσ₀e⟩ : ∃ σ₀ : ℝ, σ₀ = 1 + 1 / Real.log y := ⟨_, rfl⟩
  have hinv : 1 / Real.log y * Real.log y = 1 := by field_simp
  have hinvpos : 0 < 1 / Real.log y := div_pos one_pos hlogy
  have hinv2 : 1 / Real.log y < 2 := by nlinarith
  have hσ₀gt : 1 < σ₀ := by rw [hσ₀e]; linarith
  have hσσ : σ₁ ≤ σ₀ := by linarith
  have hσdiff : |σ₀ - σ₁| ≤ 3 := by
    rw [abs_of_nonneg (by linarith), hσ₀e]; linarith
  have hyσ₀ : y ^ σ₀ = Real.exp 1 * y := by
    rw [hσ₀e, Real.rpow_add hy0, Real.rpow_one, Real.rpow_def_of_pos hy0,
      mul_one_div_cancel hlogyne, mul_comm]

  have hB₁ : ∀ β ∈ B.filter (fun β => σ₁ < β),
      σ₁ < β ∧ β < σ₀ ∧ deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0 := by
    intro β hβ
    rw [Finset.mem_filter] at hβ
    obtain ⟨-, -, hz, hd⟩ := hBz β hβ.1
    refine ⟨hβ.2, ?_, hd⟩
    have hβ1 : β < 1 := by
      by_contra hc
      push_neg at hc
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using hc) hz
    linarith
  have hB₁z : ∀ β ∈ B.filter (fun β => σ₁ < β), DirichletCharacter.LFunction χ (β : ℂ) = 0 := by
    intro β hβ
    rw [Finset.mem_filter] at hβ
    exact (hBz β hβ.1).2.2.1
  have hzer : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T →
      DirichletCharacter.LFunction χ w = 0 → ∃ β ∈ B.filter (fun β => σ₁ < β), w = (β : ℂ) := by
    intro w h1 _ h3 h4
    have hreg : InRegion c₁ q w := by
      unfold InRegion
      have hm := log_analytic_conductor_mono q w.im T h3
      rw [hL] at hm
      have hpos := log_conductor_pos_real q w.im
      have key : c₁ / L ≤ c₁ / Real.log ((q : ℝ) * (|w.im| + 2)) := by
        rw [div_eq_mul_one_div c₁ L, div_eq_mul_one_div c₁ (Real.log ((q : ℝ) * (|w.im| + 2)))]
        exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hpos hm) hc₁.le
      linarith
    obtain ⟨β, hβB, hwβ⟩ := hBall w hreg ⟨Or.inl hχ, h4⟩
    refine ⟨β, Finset.mem_filter.mpr ⟨hβB, ?_⟩, hwβ⟩
    have h1' : σ₁ ≤ β := by rw [hwβ] at h1; simpa using h1
    have hne := hσ₁B β hβB
    rcases lt_or_eq_of_le h1' with h | h
    · exact h
    · exfalso
      rw [h, sub_self, abs_zero] at hne
      have hp : 0 < c₁ / (24 * L) := div_pos hc₁ (by linarith)
      linarith
  have hrect := hRS q χ hχ y hy0 σ₁ σ₀ T (B.filter (fun β => σ₁ < β)) hσ₁pos hσ₁lt1 hσ₀gt hT0
    hB₁ hzer hB₁z
  have hdec := perron_contour_decomposition hP χ y σ₁ σ₀ T _ hy1 hσ₀gt hT0.le hrect

  have hAnn : 0 ≤ (Real.log y + C₀) * (Real.exp 1 * y) :=
    mul_nonneg (by linarith) (mul_pos (Real.exp_pos 1) hy0).le
  have hI1 : ‖∫ t in (Set.Ioc (-T) T)ᶜ, Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤
      2 * Real.pi * ((Real.log y + C₀) * (Real.exp 1 * y)) / T := by
    refine Formalism.ZF.norm_integral_compl_le (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + t * I)) _ T hAnn hT0 (fun t ht => ?_)
    show ‖Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤ _
    rw [hσ₀e]
    exact perron_right_line_bound χ C₀ hR y T t hy1' hT0 ht

  have hHnn : 0 ≤ (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 := by
    have hCL : 0 ≤ C * L ^ 2 + 1 := by
      have := mul_nonneg hC (sq_nonneg L)
      linarith
    exact div_nonneg (mul_nonneg hCL (mul_pos (Real.exp_pos 1) hy0).le) (sq_nonneg T)
  have hH : ∀ v : ℝ, |v| = T → ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + (v : ℂ) * I)‖ ≤
      (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3 := by
    intro v hv
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := σ₁) (b := σ₀) (f := fun x : ℝ => Fchi χ y ((x : ℂ) + (v : ℂ) * I))
      (C := (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2) (fun x hx => by
        rw [Set.uIoc_of_le hσσ] at hx
        have hx' := perron_horizontal_segment_bound χ c₁ C B hBc hD y T x v σ₀ σ₁ hy1 hT hv hσ₁reg
          hx.1.le hx.2
        rw [hL, hyσ₀] at hx'
        exact hx')
    exact hb.trans (mul_le_mul_of_nonneg_left hσdiff hHnn)

  have hV : ‖∫ u in (-T)..T, Fchi χ y ((σ₁ : ℂ) + u * I)‖ ≤
      (C * L ^ 2 + 24 * L / c₁) * y ^ σ₁ * (8 * L / c₁) * (2 * T) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -T) (b := T) (f := fun u : ℝ => Fchi χ y ((σ₁ : ℂ) + u * I))
      (C := (C * L ^ 2 + 24 * L / c₁) * y ^ σ₁ * (8 * L / c₁)) (fun u hu => by
        rw [Set.uIoc_of_le (by linarith)] at hu
        have hu' : |u| ≤ T := abs_le.mpr ⟨hu.1.le, hu.2⟩
        have hb' := perron_left_line_bound χ c₁ C hc₁.le hC B hBc hD y T u σ₁ (c₁ / (24 * L))
          (c₁ / (4 * L)) hy0 hu' hσ₁reg hhalf (div_pos hc₁ (by linarith)) hgap
          (div_pos hc₁ (by linarith)) hσ₁B
        rw [hL, h1δ, h2ε] at hb'
        exact hb')
    have h2T : |T - -T| = 2 * T := by
      rw [sub_neg_eq_add, abs_of_pos (by linarith)]; ring
    rw [h2T] at hb
    exact hb

  have hO : ‖∑ β ∈ B \ B.filter (fun β => σ₁ < β),
      (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤ y ^ σ₁ * (8 * L / c₁) := by
    refine norm_sum_le_of_card_le_one _ ((Finset.card_le_card Finset.sdiff_subset).trans hBc)
      (fun β : ℝ => (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))) _
      (mul_nonneg (Real.rpow_nonneg hy0.le _) (div_pos (by linarith) hc₁).le) (fun β hβ => ?_)
    rw [Finset.mem_sdiff] at hβ
    have hβσ : β ≤ σ₁ := by
      by_contra hc
      push_neg at hc
      exact hβ.2 (Finset.mem_filter.mpr ⟨hβ.1, hc⟩)
    have hreg := (hBz β hβ.1).2.1
    unfold InRegion at hreg
    simp only [Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add] at hreg
    have hl2 : Real.log 2 ≤ Real.log ((q : ℝ) * 2) := Real.log_le_log (by norm_num) (by nlinarith)
    have hlq : (1:ℝ) / 2 < Real.log ((q : ℝ) * 2) := by linarith
    have hlqne : Real.log ((q : ℝ) * 2) ≠ 0 := by linarith
    have hr : c₁ / Real.log ((q : ℝ) * 2) * Real.log ((q : ℝ) * 2) = c₁ := by field_simp
    have hrpos : 0 ≤ c₁ / Real.log ((q : ℝ) * 2) := div_nonneg hc₁.le (by linarith)
    have hrh : c₁ / Real.log ((q : ℝ) * 2) ≤ 1 / 2 := by nlinarith
    have hβhalf : 1 / 2 ≤ β := by linarith
    have hom := real_zero_residue_term_bound y β σ₁ (c₁ / (4 * L)) hy1 hβhalf hβσ (div_pos hc₁ (by linarith)) hgap
    rw [h2ε] at hom
    exact hom

  have hmain : ‖Schi χ y - (negLD χ 1 * y - ∑ β ∈ B.filter (fun β => σ₁ < β),
      (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)))‖ ≤
      2 * Real.pi * ((Real.log y + C₀) * (Real.exp 1 * y)) / T
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 24 * L / c₁) * y ^ σ₁ * (8 * L / c₁) * (2 * T) := by
    have hX := norm_nonneg (Schi χ y - (negLD χ 1 * y - ∑ β ∈ B.filter (fun β => σ₁ < β),
      (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))))
    have h2pi : (1:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hXX := mul_le_mul_of_nonneg_right h2pi hX
    have hbot := hH (-T) (by rw [abs_neg]; exact hTabs)
    have htop := hH T hTabs
    linarith
  rw [← Finset.sum_sdiff (Finset.filter_subset (fun β => σ₁ < β) B)]
  calc ‖Schi χ y - negLD χ 1 * y + (∑ β ∈ B \ B.filter (fun β => σ₁ < β),
          (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)) + ∑ β ∈ B.filter (fun β => σ₁ < β),
          (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)))‖
        = ‖(Schi χ y - (negLD χ 1 * y - ∑ β ∈ B.filter (fun β => σ₁ < β),
          (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)))) + ∑ β ∈ B \ B.filter (fun β => σ₁ < β),
          (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add hmain hO
end Formalism.ZeroFreeDirichlet
