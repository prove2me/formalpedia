-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockContinuum.tendsto_eLpNorm_indicator_compl
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T11:11:06.624638+00:00
-- url     : https://prove2.me/submissions/f8845a29-a2e7-42d2-b4d7-7e035f249890

-- Generated from ChapterNavierStokesFockContinuum.lean — solution of BookProof.NavierStokesFlow.FockContinuum.tendsto_eLpNorm_indicator_compl
import Mathlib
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockContinuum



open MeasureTheory



open FullEsa

variable {X : Type*} [MeasurableSpace X]

variable {X : Type*} [MeasurableSpace X]

set_option maxHeartbeats 1000000 in

theorem solution (μ : Measure X) {g : X → ℝ} (hg : Measurable g)
    (f : Lp ℂ 2 μ) :
    Filter.Tendsto
      (fun n : ℕ => eLpNorm ({x | |g x| ≤ (n : ℝ)}ᶜ.indicator ((f : X → ℂ))) 2 μ)
      Filter.atTop (nhds 0) := by
  have hmeasS : ∀ n : ℕ, MeasurableSet ({x | |g x| ≤ (n : ℝ)}ᶜ) :=
    fun n => (measurableSet_le hg.abs measurable_const).compl
  have hrw : ∀ n : ℕ, eLpNorm ({x | |g x| ≤ (n : ℝ)}ᶜ.indicator (f : X → ℂ)) 2 μ
      = (∫⁻ x, ‖({x | |g x| ≤ (n : ℝ)}ᶜ.indicator (f : X → ℂ)) x‖ₑ ^ (2 : ℝ) ∂μ)
          ^ (1 / (2 : ℝ)) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      show ((2 : ENNReal).toReal) = (2 : ℝ) by norm_num]
  simp_rw [hrw]
  have hlim : Filter.Tendsto
      (fun n : ℕ => ∫⁻ x, ‖({x | |g x| ≤ (n : ℝ)}ᶜ.indicator (f : X → ℂ)) x‖ₑ ^ (2 : ℝ) ∂μ)
      Filter.atTop (nhds 0) := by
    have hdom : ∀ n : ℕ,
        (fun x => ‖({x | |g x| ≤ (n : ℝ)}ᶜ.indicator (f : X → ℂ)) x‖ₑ ^ (2 : ℝ))
          ≤ᵐ[μ] fun x => ‖(f : X → ℂ) x‖ₑ ^ (2 : ℝ) := by
      intro n
      filter_upwards with x
      by_cases h : x ∈ ({x | |g x| ≤ (n : ℝ)}ᶜ)
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h]; simp
    have hbdd : ∫⁻ x, ‖(f : X → ℂ) x‖ₑ ^ (2 : ℝ) ∂μ ≠ ⊤ := by
      intro hcon
      have h := Lp.eLpNorm_ne_top f
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h
      apply h
      rw [show ((2 : ENNReal).toReal) = (2 : ℝ) by norm_num, hcon]
      exact ENNReal.top_rpow_of_pos (by positivity)
    have hae : ∀ᵐ x ∂μ, Filter.Tendsto
        (fun n : ℕ => ‖({x | |g x| ≤ (n : ℝ)}ᶜ.indicator (f : X → ℂ)) x‖ₑ ^ (2 : ℝ))
        Filter.atTop (nhds 0) := by
      filter_upwards with x
      obtain ⟨N, hN⟩ := exists_nat_ge |g x|
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds (f₁ := fun _ : ℕ => (0 : ENNReal))
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hx : x ∈ {x | |g x| ≤ (n : ℝ)} := le_trans hN (by exact_mod_cast hn)
      rw [Set.indicator_of_notMem (by simpa using hx)]
      simp
    have hdct := tendsto_lintegral_of_dominated_convergence' (μ := μ) (f := fun _ => (0 : ENNReal))
      (fun x => ‖(f : X → ℂ) x‖ₑ ^ (2 : ℝ))
      (fun n => (((Lp.aestronglyMeasurable f).indicator (hmeasS n)).enorm).pow_const _)
      hdom hbdd hae
    simpa using hdct
  have h := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hlim
  simp only [one_div] at h
  rw [show (0 : ENNReal) ^ (2 : ℝ)⁻¹ = 0 from ENNReal.zero_rpow_of_pos (by norm_num)] at h
  have hfun : ∀ I : ℕ → ENNReal,
      (fun a : ENNReal => a ^ (2:ℝ)⁻¹) ∘ I = fun n => I n ^ (2:ℝ)⁻¹ := fun I => rfl
  simp only [one_div]
  rw [← hfun]
  exact h
