-- Prove2me | solution 1 for FournierGuillin.Moment.shell_tail
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:50:27.657009+00:00
-- url     : https://prove2.me/submissions/6caeb29d-1a5f-4b93-a6e1-2e53bd676c43

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Moment_Setting

open MeasureTheory
open scoped ENNReal

open FournierGuillin.Moment in
theorem solution {d : ℕ} (hd : 1 ≤ d) {q : ℝ} (hq : 0 < q)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (hμ : moment q μ = 1) :
    ∀ n : ℕ, μ (shell n) ≤ ENNReal.ofReal (2 ^ (-(q * ((n : ℝ) - 1)))) := by
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h1 : (1 : ℝ) ≤ 2 ^ (-(q * (((0 : ℕ) : ℝ) - 1))) := by
      apply Real.one_le_rpow (by norm_num)
      push_cast; linarith
    calc μ (shell 0) ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h1
  · set c : ℝ := (2 : ℝ) ^ (q * ((n : ℝ) - 1)) with hc
    have hcpos : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
    have hsub : shell n ⊆ {x : EuclideanSpace ℝ (Fin d) | ENNReal.ofReal c ≤ ENNReal.ofReal (‖x‖ ^ q)} := by
      intro x hx
      unfold shell at hx
      rw [if_neg (Nat.pos_iff_ne_zero.mp hn)] at hx
      obtain ⟨_, hx2⟩ := hx
      unfold box at hx2
      simp only [Set.mem_setOf_eq, not_forall] at hx2
      obtain ⟨i, hi⟩ := hx2
      have hr : (2 : ℝ) ^ (n - 1) ≤ |x i| := by
        by_cases h1 : -(2 : ℝ) ^ (n - 1) < x i
        · have h2 : ¬ x i ≤ (2 : ℝ) ^ (n - 1) := fun h => hi ⟨h1, h⟩
          push_neg at h2
          rw [abs_of_pos (by linarith [pow_pos (show (0:ℝ) < 2 by norm_num) (n - 1)])]
          linarith
        · push_neg at h1
          rw [abs_of_neg (by linarith [pow_pos (show (0:ℝ) < 2 by norm_num) (n - 1)])]
          linarith
      have hnorm : (2 : ℝ) ^ (n - 1) ≤ ‖x‖ := by
        have := PiLp.norm_apply_le x i
        rw [Real.norm_eq_abs] at this
        linarith
      have hcr : c = ((2 : ℝ) ^ (n - 1)) ^ q := by
        rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1
        rw [Nat.cast_sub hn]
        push_cast
        ring
      simp only [Set.mem_setOf_eq]
      apply ENNReal.ofReal_le_ofReal
      rw [hcr]
      exact Real.rpow_le_rpow (by positivity) hnorm hq.le
    have hmeas : AEMeasurable (fun x : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (‖x‖ ^ q)) μ := by
      fun_prop
    have hmk := mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal c)
    have hmom : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ q) ∂μ = 1 := hμ
    rw [hmom] at hmk
    have h1 : μ {x | ENNReal.ofReal c ≤ ENNReal.ofReal (‖x‖ ^ q)} ≤ (ENNReal.ofReal c)⁻¹ := by
      rw [ENNReal.le_inv_iff_mul_le, mul_comm]
      exact hmk
    have h2 : (ENNReal.ofReal c)⁻¹ = ENNReal.ofReal (2 ^ (-(q * ((n : ℝ) - 1)))) := by
      rw [← ENNReal.ofReal_inv_of_pos hcpos, hc, Real.rpow_neg (by norm_num)]
    calc μ (shell n) ≤ μ {x | ENNReal.ofReal c ≤ ENNReal.ofReal (‖x‖ ^ q)} := measure_mono hsub
      _ ≤ _ := h1
      _ = _ := h2
