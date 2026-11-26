-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_generator_convolution_hjb
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:36:03.864953+00:00
-- url     : https://prove2.me/submissions/d51a8b00-9005-42d6-833e-459b90f41728
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_interior_jet_interchange
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_jump_integral_interchange
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_generator_sign_assembly
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w V ρ : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (δ : ℝ) (hδ : 0 < δ)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hVeq : ∀ y : ℝ, ENNReal.ofReal y ≤ C → V y = w y)
    (hVmono : Monotone V) (hVnonneg : ∀ y, 0 ≤ V y)
    (hVzero : ∀ y < 0, V y = 0)
    (hρI : Integrable ρ) (hρnorm : (∫ r, ρ r) = 1)
    (hρpos : 0 ≤ᵐ[volume] ρ)
    (hρsupport : ∀ᵐ r ∂volume, ρ r ≠ 0 →
      r ∈ Icc (δ / 3) (2 * (δ / 3)))
    (hρsmooth : ContDiff ℝ 2 ρ) (hρcompact : HasCompactSupport ρ)
    (hI : ∀ y : ℝ, Integrable (fun r => ρ r * V (y - r)))
    (hg : ContDiff ℝ 2 (fun y => ∫ r, ρ r * V (y - r))) :
    ∀ y : ℝ, δ ≤ y → ENNReal.ofReal y ≤ C →
      X.GeneratorIntegrable (fun t => ∫ r, ρ r * V (t - r)) y ∧
      X.generator (fun t => ∫ r, ρ r * V (t - r)) y -
        q * (∫ r, ρ r * V (y - r)) ≤ 0 := by 
  intro y hy hyC
  obtain ⟨hW, hD1, hD2, hv, hd1, hd2⟩ :=
    avram_locmoll_interior_jet_interchange X q w V ρ C hC δ hδ
      hw_smooth hw_hjb hVeq hVmono hVnonneg hVzero hρI hρnorm
      hρpos hρsupport hρsmooth hρcompact hI hg y hy hyC
  obtain ⟨hi, hJ, hj⟩ :=
    avram_locmoll_jump_integral_interchange X q w V ρ C hC δ hδ
      hw_smooth hw_hjb hVeq hVmono hVnonneg hVzero hρI hρnorm
      hρpos hρsupport hρsmooth hρcompact hI hg y hy hyC hD1 hd1
  refine ⟨hi, ?_⟩
  unfold SpectrallyNegativeLevy.generator
  rw [hd1, hd2, hj, hv]
  apply avram_locmoll_generator_sign_assembly
    (X.σ ^ 2 / 2) X.c q _ _ _ _ hD2 hD1 hJ hW
  filter_upwards [hρpos, hρsupport] with r hp hs
  by_cases hz : ρ r = 0
  · simp [hz]
  · have hr := hs hz
    have hpos : 0 < y - r := by linarith [hr.2]
    have hlt : ENNReal.ofReal (y - r) < C :=
      lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < y)).2
        (by linarith [hr.1])) hyC
    have h := (hw_hjb (y - r) hpos hlt).2
    unfold SpectrallyNegativeLevy.generator at h
    have hm := mul_nonpos_of_nonneg_of_nonpos hp h
    nlinarith only [hm]
