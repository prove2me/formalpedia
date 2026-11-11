-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_uniform_compoundPoisson_real_mgf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:39:11.890244+00:00
-- url     : https://prove2.me/submissions/172aa8be-7c83-4e20-b0b0-90b3e3f1a50a

import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Theorems.Thm_AvramDividend_Classical_chat06_laplace_random_mark_sum_without_pgf_assumption
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_mark_independent
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_fixed_mark_real_moment
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_exp_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_jumpCount_measurable_public
import Theorems.Thm_levy_foundations_compoundPoissonJumpCountLaw
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_restrict_identities
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_measure_facts
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp (θ *
      LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω) ∂P) =
      Real.exp ((t : ℝ) * (θ + (∫ y in Ioo (-1 : ℝ) 0,
      (Real.exp (θ * y) - 1) ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))))) := by
  let N := fun ω => LevyFoundations.jumpCount
    (fun j => LevyFoundations.arrival τ j ω) (t : ℝ)
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)
  let m := ∫ y, Real.exp (θ * y) ∂ν
  have hN : Measurable N :=
    avram_a06_compound_jumpCount_measurable_public τ
      hd.measurable_interarrival (t : ℝ)
  have hLaw : HasLaw N (poissonMeasure t) P :=
    ⟨hN.aemeasurable, by
      simpa only [one_mul] using
        (levy_foundations_compoundPoissonJumpCountLaw hd (by norm_num) t)⟩
  have hpoint (ω) :
      Real.exp (θ * LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω) =
        Real.exp (θ * (t : ℝ)) *
          Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω) := by
    simp only [LevyFoundations.compoundPoisson, LevyFoundations.piecewisePath]
    rw [← Real.exp_add]
    congr 1
    ring
  have hFint : Integrable
      (fun ω => Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω)) P := by
    have h := (avram_a06_compoundPoisson_exp_integrable hd (t : ℝ) θ hθ).const_mul
      (Real.exp (-(θ * (t : ℝ))))
    convert h using 1
    funext ω
    rw [hpoint ω, ← mul_assoc, ← Real.exp_add]
    simp
  have hMoment :
      (∫ ω, Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω) ∂P) =
        Real.exp ((t : ℝ) * (m - 1)) := by
    exact chat06_laplace_random_mark_sum_without_pgf_assumption
      P N Y hN hd.measurable_mark
      (avram_a06_original_cp_count_mark_independent P τ Y hd t)
      t hLaw θ m hFint
      (fun k => avram_a06_original_cp_fixed_mark_real_moment P τ Y hd k θ hθ)
  have hmass : ν Set.univ = 1 :=
    avram_a06_uniform_negative_mark_measure_facts.2.1
  letI : IsProbabilityMeasure ν := ⟨hmass⟩
  have hExpInt : Integrable (fun y : ℝ => Real.exp (θ * y)) ν := by
    have hm : AEStronglyMeasurable (fun y : ℝ => Real.exp (θ * y)) ν := by
      fun_prop
    refine (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) ν).mono hm ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioo : MeasurableSet (Ioo (-1 : ℝ) 0))]
      with y hy
    have hmul : θ * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθ (le_of_lt hy.2)
    have hexp : Real.exp (θ * y) ≤ 1 := by
      simpa only [Real.exp_zero] using (Real.exp_le_exp).mpr hmul
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hexp
  have hScalar :
      (∫ y in Ioo (-1 : ℝ) 0, (Real.exp (θ * y) - 1) ∂ν) = m - 1 := by
    have hrestr := avram_a06_uniform_negative_mark_restrict_identities.2
    change (∫ y, (Real.exp (θ * y) - 1) ∂ν.restrict (Ioo (-1 : ℝ) 0)) = m - 1
    rw [show ν.restrict (Ioo (-1 : ℝ) 0) = ν from hrestr]
    rw [integral_sub hExpInt (integrable_const (1 : ℝ))]
    simp [m]
  calc
    (∫ ω, Real.exp (θ *
      LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω) ∂P) =
        Real.exp (θ * (t : ℝ)) *
          (∫ ω, Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω) ∂P) := by
            simp_rw [hpoint]
            rw [integral_const_mul]
    _ = Real.exp (θ * (t : ℝ)) * Real.exp ((t : ℝ) * (m - 1)) := by
      rw [hMoment]
    _ = Real.exp ((t : ℝ) * (θ + (∫ y in Ioo (-1 : ℝ) 0,
        (Real.exp (θ * y) - 1) ∂ν))) := by
      rw [← Real.exp_add, hScalar]
      congr 1
      ring