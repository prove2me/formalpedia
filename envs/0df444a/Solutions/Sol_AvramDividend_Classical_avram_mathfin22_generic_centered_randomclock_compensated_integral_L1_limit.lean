-- Prove2me | solution 1 for AvramDividend.Classical.avram_mathfin22_generic_centered_randomclock_compensated_integral_L1_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:52:27.565084+00:00
-- url     : https://prove2.me/submissions/2a3bc4da-2cd0-4702-a45f-5b9f6da3a5c5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_generic_random_clock_signed_compensator_integral_DCT
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

/-- Bounded random-clock signed compensator limits preserve integrability and centring. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (J N ρ : Ω → ℝ)
    (c : ℕ → ℝ) (r M T : ℝ)
    (hT : 0 ≤ T)
    (hFI : ∀ k, Integrable (F k) P)
    (hNI : Integrable N P) (hρI : Integrable ρ P)
    (hρ : ∀ ω, 0 ≤ ρ ω ∧ ρ ω ≤ T)
    (hFBound : ∀ᵐ ω ∂P, ∀ k, ‖F k ω‖ ≤ N ω)
    (hcBound : ∀ k, |c k| ≤ M)
    (hFConv : ∀ᵐ ω ∂P,
      Tendsto (fun k => F k ω) atTop (𝓝 (J ω)))
    (hcConv : Tendsto c atTop (𝓝 r))
    (hCentered : ∀ k,
      (∫ ω, F k ω - ρ ω * c k ∂P) = 0) :
    Integrable (fun ω => J ω - ρ ω * r) P ∧
    (∫ ω, J ω - ρ ω * r ∂P) = 0 := by
  have hJMeas : AEStronglyMeasurable J P :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (hFI k).aestronglyMeasurable) hFConv
  have hJI : Integrable J P := by
    refine hNI.mono hJMeas ?_
    filter_upwards [hFBound, hFConv] with ω hBd hLim
    have hNorm : Tendsto (fun k : ℕ => ‖F k ω‖)
        atTop (𝓝 ‖J ω‖) :=
      (continuous_norm.tendsto (J ω)).comp hLim
    have hBound : ‖J ω‖ ≤ N ω :=
      le_of_tendsto hNorm (Filter.Eventually.of_forall hBd)
    exact hBound.trans (by simpa [Real.norm_eq_abs] using
      (le_abs_self (N ω)))
  have hDCT :=
    avram_mathfin22_generic_random_clock_signed_compensator_integral_DCT
      F J N ρ c r M T hT hFI hNI hρI hρ hFBound
      hcBound hFConv hcConv
  have hZeroLimit :
      Tendsto (fun k => ∫ ω, F k ω - ρ ω * c k ∂P)
        atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_nhds (x := (0 : ℝ))) using 1
    funext k
    exact hCentered k
  exact ⟨hJI.sub (hρI.mul_const r),
    (tendsto_nhds_unique hZeroLimit hDCT).symm⟩
