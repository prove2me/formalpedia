-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB149_time_supported_nested_L2_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:37:51.370213+00:00
-- url     : https://prove2.me/submissions/bd4d288a-3d87-4389-8482-7974b68749d9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB142_three_bounded_joint_measurable_nested_losses_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
noncomputable section

theorem solution
    {β : Type*} [MeasurableSpace β]
    (μ : Measure ℝ) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (I : Set ℝ) (hI : MeasurableSet I) (hsupp : ∀ᵐ t ∂μ, t ∈ I)
    (f g h : ℝ × β → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (Bf Bg Bh : ℝ) (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg) (hBh : 0 ≤ Bh)
    (hfb : ∀ z, |f z| ≤ Bf) (hgb : ∀ z, |g z| ≤ Bg)
    (hhb : ∀ z, z.1 ∈ I → |h z| ≤ Bh) :
    Integrable (fun t => ∫ b, (f (t,b) - g (t,b)) ^ 2 ∂ν) μ ∧
    Integrable (fun t => ∫ b, (f (t,b) - h (t,b)) ^ 2 ∂ν) μ ∧
    Integrable (fun t => ∫ b, (h (t,b) - g (t,b)) ^ 2 ∂ν) μ := by
  classical
  let hc : ℝ × β → ℝ := fun z => if z.1 ∈ I then h z else 0
  have hcm : Measurable hc :=
    Measurable.ite (hI.preimage measurable_fst) hh measurable_const
  have hcb : ∀ z, |hc z| ≤ Bh := by
    intro z
    by_cases hz : z.1 ∈ I
    · simpa only [hc, if_pos hz] using hhb z hz
    · simp [hc, hz, hBh]
  let M : ℝ := max (max Bf Bg) Bh
  have hM : 0 ≤ M := hBf.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hfbM : ∀ z, |f z| ≤ M := by
    intro z
    exact (hfb z).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hgbM : ∀ z, |g z| ≤ M := by
    intro z
    exact (hgb z).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hcbM : ∀ z, |hc z| ≤ M := by
    intro z
    exact (hcb z).trans (le_max_right _ _)
  rcases avram_gbB142_three_bounded_joint_measurable_nested_losses_integrable
    μ ν f g hc hf hg hcm M hM hfbM hgbM hcbM
    with ⟨_, hfg, hfh, hhg⟩
  have hfhEq :
      (fun t => ∫ b, (f (t,b) - hc (t,b)) ^ 2 ∂ν) =ᵐ[μ]
      (fun t => ∫ b, (f (t,b) - h (t,b)) ^ 2 ∂ν) := by
    filter_upwards [hsupp] with t ht
    simp [hc, ht]
  have hhgEq :
      (fun t => ∫ b, (hc (t,b) - g (t,b)) ^ 2 ∂ν) =ᵐ[μ]
      (fun t => ∫ b, (h (t,b) - g (t,b)) ^ 2 ∂ν) := by
    filter_upwards [hsupp] with t ht
    simp [hc, ht]
  exact ⟨hfg, hfh.congr hfhEq, hhg.congr hhgEq⟩
