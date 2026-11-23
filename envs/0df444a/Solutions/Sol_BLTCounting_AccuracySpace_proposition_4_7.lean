-- Prove2me | solution 1 for BLTCounting.AccuracySpace.proposition_4_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:26:47.645392+00:00
-- url     : https://prove2.me/submissions/8e79dd33-4383-4190-a57d-1751f1c90b07
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel
import Theorems.Thm_BLTCounting_AccuracySpace_equation_19
import Theorems.Thm_BLTCounting_AccuracySpace_lemma_3_7
import Theorems.Thm_BLTCounting_AccuracySpace_equation_20

open Complex BLTCounting.AccuracySpace

namespace AuxProp47

lemma continuous_c0Hat_re : Continuous (fun ω : ℝ => (c0Hat ω).re) := by
  have heq : (fun ω : ℝ => (c0Hat ω).re) =
      fun ω : ℝ => ‖Complex.Gamma (1 / 4 + I * (ω : ℂ))‖ ^ 2 / Real.pi := by
    ext ω
    rw [equation_19 ω]
    exact Complex.ofReal_re _
  rw [heq]
  have hcont_gamma : Continuous (fun ω : ℝ => Complex.Gamma (1 / 4 + I * (ω : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro ω
    have hd : DifferentiableAt ℂ Complex.Gamma (1 / 4 + I * (ω : ℂ)) := by
      refine Complex.differentiableAt_Gamma _ fun m hm => ?_
      have hre := congrArg Complex.re hm
      simp at hre
      have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    exact ContinuousAt.comp (g := Complex.Gamma) (f := fun x : ℝ => (1 / 4 : ℂ) + I * (x : ℂ))
      hd.continuousAt
      (by continuity : Continuous (fun x : ℝ => (1 / 4 : ℂ) + I * (x : ℂ))).continuousAt
  exact ((hcont_gamma.norm.pow 2).div_const Real.pi)

lemma c0Hat_pos (ω : ℝ) : 0 < (c0Hat ω).re := by
  rw [equation_19 ω, Complex.ofReal_re]
  have hne : Complex.Gamma (1 / 4 + I * (ω : ℂ)) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp)
  have hnorm : 0 < ‖Complex.Gamma (1 / 4 + I * (ω : ℂ))‖ := norm_pos_iff.mpr hne
  positivity

lemma sandwich_of_large {C₂₀ W₂₀ : ℝ}
    (h20 : ∀ ω : ℝ, W₂₀ ≤ ω →
      ‖c0Hat ω - ((2 * ω ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * ω)) : ℝ) : ℂ)‖ ≤
        (C₂₀ / ω) * (2 * ω ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * ω))))
    {ω : ℝ} (hW : W₂₀ ≤ ω) (h1 : 1 ≤ ω) (hC : 2 * C₂₀ ≤ ω) :
    ω ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * ω)) ≤ (c0Hat ω).re ∧
      (c0Hat ω).re ≤ 3 * (ω ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * ω))) := by
  have hω_pos : 0 < ω := by linarith
  have hmain := h20 ω hW
  let M : ℝ := 2 * ω ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * ω))
  have hM_pos : 0 < M := by
    dsimp [M]
    positivity
  have habs : |(c0Hat ω).re - M| ≤ (C₂₀ / ω) * M := by
    have hre : ((c0Hat ω - ((M : ℝ) : ℂ)).re) = (c0Hat ω).re - M := by simp
    calc
      |(c0Hat ω).re - M| = |(c0Hat ω - ((M : ℝ) : ℂ)).re| := by rw [hre]
      _ ≤ ‖c0Hat ω - ((M : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
      _ ≤ (C₂₀ / ω) * M := hmain
  have hfrac : C₂₀ / ω ≤ 1 / 2 := by
    rw [div_le_iff₀ hω_pos]
    linarith
  have herr : (C₂₀ / ω) * M ≤ (1 / 2) * M :=
    mul_le_mul_of_nonneg_right hfrac hM_pos.le
  have hbounds := abs_sub_le_iff.mp (le_trans habs herr)
  have hM_eq : (1 / 2 : ℝ) * M = ω ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * ω)) := by
    dsimp [M]; ring
  have hM_eq3 : (3 / 2 : ℝ) * M = 3 * (ω ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * ω))) := by
    dsimp [M]; ring
  constructor <;> linarith

end AuxProp47

theorem solution :
    ∃ a : ℝ, 0 < a ∧
      (∀ η : ℝ, 0 < η → a ≤ Real.log (1 / η) →
        ∃! ω : ℝ, 0 < ω ∧ c0Hat ω = ((8 * η : ℝ) : ℂ)) ∧
      ∃ C A₀ : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → A₀ ≤ Real.log (1 / η) →
        ∀ ω : ℝ, 0 < ω → c0Hat ω = ((8 * η : ℝ) : ℂ) →
          |ω - (1 / Real.pi) * (Real.log (1 / η) - (1 / 2) * Real.log (Real.log (1 / η)))| ≤ C := by
  rcases equation_20 with ⟨C₂₀, W₂₀, hC₂₀, hW₂₀, h20⟩
  have h37 := lemma_3_7
  let g : ℝ → ℝ := fun ω => (c0Hat ω).re
  have hg0_pos : 0 < g 0 := AuxProp47.c0Hat_pos 0
  let a : ℝ := max 1 (Real.log (16 / g 0))
  have ha_pos : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let W₁ : ℝ := max (max W₂₀ 1) (2 * C₂₀)
  have hW₁_ge1 : 1 ≤ W₁ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hW₁_geW : W₂₀ ≤ W₁ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hW₁_geC : 2 * C₂₀ ≤ W₁ := le_max_right _ _
  have hgW₁_pos : 0 < g W₁ := AuxProp47.c0Hat_pos W₁
  let A₀ : ℝ := max (max a 16) (Real.log (16 / g W₁))
  refine ⟨a, ha_pos, ?_, 1, A₀, zero_lt_one, ?_⟩
  · intro η hη haA
    have h8η_lt_g0 : 8 * η < g 0 := by
      have hlog : Real.log (16 / g 0) ≤ Real.log (1 / η) :=
        le_trans (le_max_right _ _) haA
      have hle : 16 / g 0 ≤ 1 / η :=
        (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog
      have h1 : 16 * η ≤ g 0 := by
        have hmul := mul_le_mul_of_nonneg_right hle (mul_nonneg hg0_pos.le hη.le)
        field_simp [ne_of_gt hg0_pos, ne_of_gt hη] at hmul
        linarith
      linarith
    let Ω : ℝ := max W₁ (|Real.log (8 * η / 6)| / Real.pi + 1)
    have hΩ_geW₁ : W₁ ≤ Ω := le_max_left _ _
    have hΩ_ge1 : 1 ≤ Ω := le_trans hW₁_ge1 hΩ_geW₁
    have hΩ_pos : 0 < Ω := by linarith
    have hgΩ_lt : g Ω < 8 * η := by
      have hsand := (AuxProp47.sandwich_of_large h20
        (le_trans hW₁_geW hΩ_geW₁) hΩ_ge1 (le_trans hW₁_geC hΩ_geW₁)).2
      have hrpow_le1 : Ω ^ (-(1 / 2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hΩ_ge1 (by norm_num)
      have hexp_lt : Real.exp (-(Real.pi * Ω)) < 8 * η / 3 := by
        have hΩ_bound : |Real.log (8 * η / 6)| / Real.pi + 1 ≤ Ω := le_max_right _ _
        have hpiΩ : -Real.log (8 * η / 6) < Real.pi * Ω := by
          have h1 : -Real.log (8 * η / 6) ≤ |Real.log (8 * η / 6)| := neg_le_abs _
          have h2 : |Real.log (8 * η / 6)| < Real.pi * Ω := by
            have hmul := mul_le_mul_of_nonneg_left hΩ_bound Real.pi_pos.le
            have hdiv : Real.pi * (|Real.log (8 * η / 6)| / Real.pi) = |Real.log (8 * η / 6)| :=
              mul_div_cancel₀ _ (ne_of_gt Real.pi_pos)
            linarith [Real.pi_pos]
          linarith
        have hneg : -(Real.pi * Ω) < Real.log (8 * η / 6) := by linarith
        calc
          Real.exp (-(Real.pi * Ω)) < Real.exp (Real.log (8 * η / 6)) :=
            Real.exp_lt_exp.mpr hneg
          _ = 8 * η / 6 := Real.exp_log (by positivity)
          _ < 8 * η / 3 := by linarith
      have h1 : 3 * (Ω ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * Ω))) ≤
          3 * (1 * Real.exp (-(Real.pi * Ω))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_right hrpow_le1 (Real.exp_pos _).le
      dsimp [g]
      linarith
    have hivt : 8 * η ∈ g '' Set.Icc 0 Ω :=
      intermediate_value_Icc' hΩ_pos.le AuxProp47.continuous_c0Hat_re.continuousOn
        ⟨hgΩ_lt.le, h8η_lt_g0.le⟩
    rcases hivt with ⟨ω, ⟨hω0, hωΩ⟩, hω_eq⟩
    have hω_pos : 0 < ω := by
      rcases eq_or_lt_of_le hω0 with rfl | hpos
      · linarith
      · exact hpos
    have hω_c : c0Hat ω = ((8 * η : ℝ) : ℂ) := by
      apply Complex.ext
      · simpa [g] using hω_eq
      · simp [(h37.1 ω).1]
    refine ⟨ω, ⟨hω_pos, hω_c⟩, fun ω' ⟨hω'_pos, hω'_c⟩ => ?_⟩
    have hgω' : g ω' = 8 * η := by
      have hre := congrArg Complex.re hω'_c
      simpa [g] using hre
    exact h37.2.injOn (Set.mem_Ici.mpr hω'_pos.le) (Set.mem_Ici.mpr hω_pos.le)
      (hgω'.trans hω_eq.symm)
  · intro η hη hA₀ ω hω_pos hω_c
    let A : ℝ := Real.log (1 / η)
    have hA_ge16 : 16 ≤ A := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hA₀
    have hA_pos : 0 < A := by linarith
    have hgω : g ω = 8 * η := by
      have hre := congrArg Complex.re hω_c
      simpa [g] using hre
    have h8η_lt_gW₁ : 8 * η < g W₁ := by
      have hlog : Real.log (16 / g W₁) ≤ A := le_trans (le_max_right _ _) hA₀
      have hle : 16 / g W₁ ≤ 1 / η :=
        (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog
      have h1 : 16 * η ≤ g W₁ := by
        have hmul := mul_le_mul_of_nonneg_right hle (mul_nonneg hgW₁_pos.le hη.le)
        field_simp [ne_of_gt hgW₁_pos, ne_of_gt hη] at hmul
        linarith
      linarith
    have hW₁_lt_ω : W₁ < ω := by
      by_contra hnot
      have hle : ω ≤ W₁ := not_lt.mp hnot
      rcases eq_or_lt_of_le hle with rfl | hlt
      · linarith
      · have hgt := h37.2 (Set.mem_Ici.mpr hω_pos.le)
          (Set.mem_Ici.mpr (le_trans zero_le_one hW₁_ge1)) hlt
        dsimp [g] at hgω h8η_lt_gW₁
        linarith
    have hW₁_le_ω : W₁ ≤ ω := hW₁_lt_ω.le
    have hω_ge1 : 1 ≤ ω := le_trans hW₁_ge1 hW₁_le_ω
    have hsand := AuxProp47.sandwich_of_large h20
      (le_trans hW₁_geW hW₁_le_ω) hω_ge1 (le_trans hW₁_geC hW₁_le_ω)
    rw [show (c0Hat ω).re = 8 * η from hgω] at hsand
    have hη_exp : η = Real.exp (-A) := by
      dsimp [A]
      rw [one_div, Real.log_inv, neg_neg, Real.exp_log hη]
    have hlog_lhs : -(1 / 2 : ℝ) * Real.log ω - Real.pi * ω ≤ Real.log 8 - A := by
      have h1 := Real.log_le_log (by positivity) hsand.1
      rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hω_pos,
        Real.log_exp, hη_exp, Real.log_mul (by norm_num) (by positivity), Real.log_exp] at h1
      linarith
    have hlog_rhs : Real.log 8 - A ≤ Real.log 3 - (1 / 2 : ℝ) * Real.log ω - Real.pi * ω := by
      have h1 := Real.log_le_log (by positivity) hsand.2
      rw [hη_exp, Real.log_mul (by norm_num) (by positivity), Real.log_exp,
        Real.log_mul (by norm_num) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_rpow hω_pos, Real.log_exp] at h1
      linarith
    have hlog3_lt_log8 : Real.log 3 < Real.log 8 :=
      Real.log_lt_log (by norm_num) (by norm_num)
    have hlog8_lt3 : Real.log 8 < 3 := by
      have h8_lt : (8 : ℝ) < Real.exp 3 := by
        have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have he3 : Real.exp 3 = Real.exp 1 ^ 3 := by
          rw [← Real.exp_nat_mul]
          norm_num
        have hpow : (2.7 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
          pow_lt_pow_left₀ he (by norm_num) (by omega)
        rw [he3]
        linarith [show (8 : ℝ) < (2.7 : ℝ) ^ 3 by norm_num]
      exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr h8_lt
    have hlogω_nn : 0 ≤ Real.log ω := Real.log_nonneg hω_ge1
    have hω_le_A : ω ≤ A := by
      have hpiω : Real.pi * ω ≤ A := by linarith
      have hpi3 : 3 < Real.pi := Real.pi_gt_three
      nlinarith
    have hω_ge_A8 : A / 8 ≤ ω := by
      have hlogω_le : Real.log ω ≤ ω - 1 := Real.log_le_sub_one_of_pos hω_pos
      have hpi4 : Real.pi < 4 := Real.pi_lt_four
      nlinarith
    have hlogω_upper : Real.log ω ≤ Real.log A := Real.log_le_log hω_pos hω_le_A
    have hlogω_lower : Real.log A - Real.log 8 ≤ Real.log ω := by
      have h1 := Real.log_le_log (by positivity) hω_ge_A8
      rw [Real.log_div (ne_of_gt hA_pos) (by norm_num)] at h1
      exact h1
    have hdiff_upper : Real.pi * ω - (A - (1 / 2) * Real.log A) ≤ (1 / 2) * Real.log 8 := by
      linarith
    have hdiff_lower : -Real.log 8 ≤ Real.pi * ω - (A - (1 / 2) * Real.log A) := by
      linarith
    have hpi3 : 3 < Real.pi := Real.pi_gt_three
    rw [abs_le]
    constructor
    · rw [le_sub_iff_add_le, ← mul_le_mul_iff_of_pos_left Real.pi_pos]
      have hrew : Real.pi * (-1 + 1 / Real.pi * (A - 1 / 2 * Real.log A)) =
          -Real.pi + (A - 1 / 2 * Real.log A) := by
        field_simp [ne_of_gt Real.pi_pos]
      rw [hrew]
      linarith
    · rw [sub_le_iff_le_add, ← mul_le_mul_iff_of_pos_left Real.pi_pos]
      have hrew : Real.pi * (1 + 1 / Real.pi * (A - 1 / 2 * Real.log A)) =
          Real.pi + (A - 1 / 2 * Real.log A) := by
        field_simp [ne_of_gt Real.pi_pos]
      rw [hrew]
      linarith
