-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_martingale_increment_zero_on_frozen_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:05:30.045455+00:00
-- url     : https://prove2.me/submissions/638d17ed-3151-4bde-9db3-9b0bdf7e8b9c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_lsv_quadratic_martingale_increment_condExp_zero
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
set_option autoImplicit false
noncomputable section

/-
Adapted from dufeteller/lean-lsv, LSV/LocalizedMartingaleFrozenEnergy.lean,
martingale_increment_zero_on_event_of_energy_eq,
commit a5f604de2e1ae431de4cbecde23e5694a12ba719.
Upstream CC BY 4.0, attribution to original source authors.
-/

theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ι (inferInstance : MeasurableSpace Ω))
    (M A : ι → Ω → ℝ) (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω)^2 - A t ω) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (s t : ι) (hst : s ≤ t)
    (E : Set Ω) (hE : MeasurableSet[ℱ s] E)
    (hAe : ∀ᵐ ω ∂μ, ω ∈ E → A t ω = A s ω) :
    ∀ᵐ ω ∂μ, ω ∈ E → M t ω = M s ω := by
  have hAi (u : ι) : Integrable (A u) μ := by
    convert (hM2 u).integrable_sq.sub (hQ.integrable u) using 1
    funext ω
    change A u ω = (M u ω)^2 - ((M u ω)^2 - A u ω)
    ring
  have hV : Integrable (fun ω => (M t ω - M s ω)^2 -
      (A t ω - A s ω)) μ :=
    ((hM2 t).sub (hM2 s)).integrable_sq.sub ((hAi t).sub (hAi s))
  have hz := AvramDividend.Classical.avram_lsv_quadratic_martingale_increment_condExp_zero
    μ ℱ M A hM hQ hM2 s t hst
  have hi0 : (∫ ω in E, (M t ω - M s ω)^2 -
      (A t ω - A s ω) ∂μ) = 0 := by
    rw [← setIntegral_condExp (ℱ.le s) hV hE]
    exact (integral_congr_ae (ae_restrict_of_ae hz)).trans (integral_zero _ _)
  have hsquare : (∫ ω in E, (M t ω - M s ω)^2 ∂μ) = 0 := by
    apply (integral_congr_ae ?_).trans hi0
    filter_upwards [ae_restrict_of_ae hAe,
      ae_restrict_mem (ℱ.le s _ hE)] with ω he hmem
    rw [he hmem, sub_self, sub_zero]
  have hzero := (integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ (fun ω => sq_nonneg _))
    (((hM2 t).sub (hM2 s)).integrable_sq.integrableOn)).mp hsquare
  change ∀ᵐ ω ∂μ.restrict E, (M t ω - M s ω)^2 = 0 at hzero
  rw [ae_restrict_iff' (ℱ.le s _ hE)] at hzero
  exact hzero.mono (fun ω hω hmem =>
    sub_eq_zero.mp (sq_eq_zero_iff.mp (hω hmem)))

