-- Prove2me | solution 1 for BanditAlgorithm.bandit_high_probability_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-21T02:41:45.159976+00:00
-- url     : https://prove2.me/submissions/91ae667f-9649-44c9-8141-9ee6f283620a

import Theorems.Thm_BanditAlgorithm_bandit_high_probability_lower_bound_at_gap
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory

open BanditAlgorithm

private theorem threshold_algebra {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n)
    {B δ : ℝ} (hB : 0 < B) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    let Δ := min (1 / 2 : ℝ)
      ((1 / (2 * B)) * Real.sqrt (((k : ℝ) - 1) / n) * Real.log (1 / (4 * δ)))
    (1 / 4 : ℝ) * min (n : ℝ)
          (Real.sqrt (((k : ℝ) - 1) * n) * Real.log (1 / (4 * δ)) / B) ≤
      Δ * n / 2 := by
  dsimp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hkreal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hsqrt_mul : Real.sqrt ((((k : ℝ) - 1) / n)) * n =
      Real.sqrt (((k : ℝ) - 1) * n) := by
    have hdiv : 0 ≤ ((k : ℝ) - 1) / n := by positivity
    have hmul : 0 ≤ ((k : ℝ) - 1) * n := by positivity
    have hsq : (Real.sqrt (((k : ℝ) - 1) / n) * n) ^ 2 =
        (Real.sqrt (((k : ℝ) - 1) * n)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hdiv, Real.sq_sqrt hmul]
      field_simp
    exact (sq_eq_sq₀ (by positivity) (by positivity)).mp hsq
  rw [mul_min_of_nonneg (n : ℝ)
    (Real.sqrt (((k : ℝ) - 1) * n) * Real.log (1 / (4 * δ)) / B)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hrhs : min (1 / 2 : ℝ)
        (1 / (2 * B) * Real.sqrt (((k : ℝ) - 1) / n) * Real.log (1 / (4 * δ))) * n / 2 =
      min (1 / 2 : ℝ)
        (1 / (2 * B) * Real.sqrt (((k : ℝ) - 1) / n) * Real.log (1 / (4 * δ))) * (n / 2) := by
    ring
  rw [hrhs, min_mul_of_nonneg _ _ (by positivity : 0 ≤ (n : ℝ) / 2)]
  apply min_le_min
  · ring_nf
    exact le_rfl
  · rw [← hsqrt_mul]
    field_simp [ne_of_gt hB]
    ring
    exact le_rfl

private theorem tuned_gap_pos_and_test {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n)
    {B δ : ℝ} (hB : 0 < B) (hδpos : 0 < δ) (hδsmall : δ < 1 / 4) :
    let Δ := min (1 / 2 : ℝ)
      ((1 / (2 * B)) * Real.sqrt (((k : ℝ) - 1) / n) * Real.log (1 / (4 * δ)))
    0 < Δ ∧ Δ ≤ 1 / 2 ∧
      2 * δ ≤ (1 / 2 : ℝ) *
        Real.exp (-2 * B * Δ * Real.sqrt ((n : ℝ) / ((k : ℝ) - 1))) := by
  dsimp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hkreal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hfour : 0 < 4 * δ := by positivity
  have hratio : 1 < 1 / (4 * δ) := by
    rw [lt_div_iff₀ hfour]
    linarith
  have hlog : 0 < Real.log (1 / (4 * δ)) := Real.log_pos hratio
  have hroot_left : 0 < Real.sqrt (((k : ℝ) - 1) / n) :=
    Real.sqrt_pos.2 (by positivity)
  have hroot_right : 0 < Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)) :=
    Real.sqrt_pos.2 (by positivity)
  have hprod : Real.sqrt (((k : ℝ) - 1) / n) *
      Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)) = 1 := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ ((k : ℝ) - 1) / n)]
    have hfrac : (((k : ℝ) - 1) / n) * (n / ((k : ℝ) - 1)) = 1 := by
      field_simp
    rw [hfrac, Real.sqrt_one]
  have hgap_right : 0 < (1 / (2 * B)) * Real.sqrt (((k : ℝ) - 1) / n) *
      Real.log (1 / (4 * δ)) := by positivity
  refine ⟨lt_min (by norm_num) hgap_right, min_le_left _ _, ?_⟩
  have hΔle := min_le_right (1 / 2 : ℝ)
    ((1 / (2 * B)) * Real.sqrt (((k : ℝ) - 1) / n) * Real.log (1 / (4 * δ)))
  have hexponent : -Real.log (1 / (4 * δ)) ≤
      -2 * B * min (1 / 2 : ℝ)
          ((1 / (2 * B)) * Real.sqrt (((k : ℝ) - 1) / n) *
            Real.log (1 / (4 * δ))) *
        Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)) := by
    calc
      -Real.log (1 / (4 * δ)) =
          -(Real.log (1 / (4 * δ)) *
            (Real.sqrt (((k : ℝ) - 1) / n) *
              Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)))) := by rw [hprod]; ring
      _ =
          -2 * B * ((1 / (2 * B)) * Real.sqrt (((k : ℝ) - 1) / n) *
            Real.log (1 / (4 * δ))) *
            Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)) := by
              field_simp [ne_of_gt hB]
      _ ≤ _ := by
        rw [show -2 * B *
            ((1 / (2 * B)) * Real.sqrt (((k : ℝ) - 1) / n) *
              Real.log (1 / (4 * δ))) *
              Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)) =
            (-2 * B * Real.sqrt ((n : ℝ) / ((k : ℝ) - 1))) *
              ((1 / (2 * B)) * Real.sqrt (((k : ℝ) - 1) / n) *
                Real.log (1 / (4 * δ))) by ring]
        rw [show -2 * B * min (1 / 2 : ℝ)
            ((1 / (2 * B)) * Real.sqrt (((k : ℝ) - 1) / n) *
              Real.log (1 / (4 * δ))) *
              Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)) =
            (-2 * B * Real.sqrt ((n : ℝ) / ((k : ℝ) - 1))) *
              min (1 / 2 : ℝ)
                ((1 / (2 * B)) * Real.sqrt (((k : ℝ) - 1) / n) *
                  Real.log (1 / (4 * δ))) by ring]
        exact mul_le_mul_of_nonpos_left hΔle
          (mul_nonpos_of_nonpos_of_nonneg (by nlinarith [hB]) hroot_right.le)
  have hexp : 4 * δ ≤ Real.exp
      (-2 * B * min (1 / 2 : ℝ)
          ((1 / (2 * B)) * Real.sqrt (((k : ℝ) - 1) / n) *
            Real.log (1 / (4 * δ))) *
        Real.sqrt ((n : ℝ) / ((k : ℝ) - 1))) := by
    calc
      4 * δ = Real.exp (-Real.log (1 / (4 * δ))) := by
        rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 1 / (4 * δ))]
        field_simp
      _ ≤ _ := Real.exp_le_exp.mpr hexponent
  nlinarith

theorem solution {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n)
    {B : ℝ} (hB : 0 < B) (π : BanditPolicy k)
    (hbound : ∀ μvec : Fin k → ℝ, (∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) →
      banditRegret (gaussianBandit μvec) π n ≤ B * Real.sqrt (((k : ℝ) - 1) * n))
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ μvec : Fin k → ℝ, (∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) ∧
      δ ≤ (banditMeasure (gaussianBandit μvec) π n).real
        {h | (1 / 4 : ℝ) * min (n : ℝ)
              (Real.sqrt (((k : ℝ) - 1) * n) * Real.log (1 / (4 * δ)) / B) ≤
            ∑ i, (armPullCount i h : ℝ) * banditGap (gaussianBandit μvec) i} := by
  by_cases hsmall : δ < 1 / 4
  · let Δ := min (1 / 2 : ℝ)
      ((1 / (2 * B)) * Real.sqrt (((k : ℝ) - 1) / n) * Real.log (1 / (4 * δ)))
    have hprops := tuned_gap_pos_and_test hk hn hB hδ.1 hsmall
    change 0 < Δ ∧ Δ ≤ 1 / 2 ∧
      2 * δ ≤ (1 / 2 : ℝ) *
        Real.exp (-2 * B * Δ * Real.sqrt ((n : ℝ) / ((k : ℝ) - 1))) at hprops
    obtain ⟨hΔpos, hΔle, htest⟩ := hprops
    obtain ⟨μvec, hμbox, hprob⟩ :=
      bandit_high_probability_lower_bound_at_gap hk hn hB π hbound hδ Δ
        hΔpos hΔle htest
    refine ⟨μvec, hμbox, hprob.trans ?_⟩
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro h hh
    exact (threshold_algebra hk hn hB hδ).trans hh
  · have hquarter : 1 / 4 ≤ δ := le_of_not_gt hsmall
    have hfour : 0 < 4 * δ := by positivity
    have hratio : 1 / (4 * δ) ≤ 1 := by
      rw [div_le_one hfour]
      linarith
    have hlog : Real.log (1 / (4 * δ)) ≤ 0 := Real.log_nonpos (by positivity) hratio
    have hsecond : Real.sqrt (((k : ℝ) - 1) * n) * Real.log (1 / (4 * δ)) / B ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) hlog) hB.le
    have hthreshold : (1 / 4 : ℝ) * min (n : ℝ)
          (Real.sqrt (((k : ℝ) - 1) * n) * Real.log (1 / (4 * δ)) / B) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by norm_num) ((min_le_right _ _).trans hsecond)
    let μvec : Fin k → ℝ := fun _ ↦ 0
    refine ⟨μvec, ?_, ?_⟩
    · intro i
      exact ⟨by simp [μvec], by simp [μvec]⟩
    have hset : {h : BanditHistory k n | (1 / 4 : ℝ) * min (n : ℝ)
              (Real.sqrt (((k : ℝ) - 1) * n) * Real.log (1 / (4 * δ)) / B) ≤
            ∑ i, (armPullCount i h : ℝ) * banditGap (gaussianBandit μvec) i} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro h
      exact hthreshold.trans (Finset.sum_nonneg fun i _ ↦
        mul_nonneg (by positivity) (by
          rw [banditGap, sub_nonneg]
          exact Finite.le_ciSup (fun j : Fin k ↦ banditArmMean (gaussianBandit μvec) j) i))
    rw [hset]
    simpa using hδ.2.le
