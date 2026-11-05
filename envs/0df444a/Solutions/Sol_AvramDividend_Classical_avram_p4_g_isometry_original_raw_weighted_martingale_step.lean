-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_raw_weighted_martingale_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:31:26.245341+00:00
-- url     : https://prove2.me/submissions/c9d05ecd-286f-43e5-89d5-2bf8920763d7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_weighted_condExp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Each actual finite-band compensated weighted cell has the original martingale step property. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : X.ν B < ⊤)
    (N : Ω → ℝ≥0∞)
    (hActual : N = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (hMeas : Measurable N)
    (hRect : ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
      (∫⁻ ω in A, N ω ∂P) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P)
    (hCountL2 : MemLp (fun ω => (N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) 2 P)
    (M : Ω → ℝ)
    (hM : StronglyMeasurable[𝓕 s] M)
    (hMInt : Integrable M P)
    : P[(fun ω => M ω + H ω * ((N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) | 𝓕 s]
        =ᵐ[P] M := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hzero := avram_p4_g_isometry_original_raw_weighted_condExp_zero
    X s t hst ε hε B hB hBand hν N hActual hMeas hRect
    H hH hHL2 hCountL2
  have hprod : Integrable (fun ω => H ω * ((N ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) P :=
    hHL2.integrable_mul hCountL2
  have hMcond : P[M | 𝓕 s] = M :=
    condExp_of_stronglyMeasurable (𝓕.le s) hM hMInt
  calc
    P[(fun ω => M ω + H ω * ((N ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) | 𝓕 s] =ᵐ[P]
      (P[M | 𝓕 s] + P[(fun ω => H ω * ((N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) | 𝓕 s]) :=
      condExp_add hMInt hprod (𝓕 s)
    _ =ᵐ[P] M := by
      filter_upwards [hzero] with ω hz
      simpa only [Pi.add_apply, Pi.zero_apply, hMcond, hz, add_zero]
