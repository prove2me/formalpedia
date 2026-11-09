-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_stop_original_F0_zero_under_physical_L1_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:09:37.596406+00:00
-- url     : https://prove2.me/submissions/be2752c5-89d1-40de-bf10-6b9979e770c6

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original initial-history centring persists under a physical L¹ Gaussian mesh limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (F : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hFzero : ∀ n,
      P[F n | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)))
    (hZI : Integrable Z P)
    (hLim : Tendsto
      (fun n => eLpNorm (fun ω => F n ω - Z ω) 1 P)
      atTop (nhds 0)) :
    P[Z | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hBound (n : ℕ) :
      eLpNorm (P[Z | 𝓕.rightCont 0]) 1 P ≤
        eLpNorm (fun ω => F n ω - Z ω) 1 P := by
    have hSub : P[(fun ω => F n ω - Z ω) | 𝓕.rightCont 0] =ᵐ[P]
        (fun ω => -(P[Z | 𝓕.rightCont 0]) ω) := by
      have hFunEq : (fun ω => F n ω - Z ω) = F n - Z := by
        funext ω
        simp only [Pi.sub_apply]
      rw [hFunEq]
      filter_upwards [condExp_sub (hFI n) hZI (𝓕.rightCont 0),
        hFzero n] with ω hEq hZero
      simpa [hEq, hZero]
    calc
      eLpNorm (P[Z | 𝓕.rightCont 0]) 1 P =
          eLpNorm (fun ω => -(P[Z | 𝓕.rightCont 0]) ω) 1 P := by
            apply eLpNorm_congr_enorm_ae
            filter_upwards with ω
            simp only [enorm_neg]
      _ = eLpNorm
          (P[(fun ω => F n ω - Z ω) | 𝓕.rightCont 0]) 1 P :=
            (eLpNorm_congr_ae hSub).symm
      _ ≤ eLpNorm (fun ω => F n ω - Z ω) 1 P :=
        eLpNorm_condExp_le_eLpNorm _ le_rfl
  have hLe : eLpNorm (P[Z | 𝓕.rightCont 0]) 1 P ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hLim
      (Filter.Eventually.of_forall hBound)
  have hZero : eLpNorm (P[Z | 𝓕.rightCont 0]) 1 P = 0 :=
    le_antisymm hLe bot_le
  have hCEint : Integrable (P[Z | 𝓕.rightCont 0]) P :=
    integrable_condExp
  exact (eLpNorm_eq_zero_iff hCEint.aestronglyMeasurable
    (by norm_num : (1 : ℝ≥0∞) ≠ 0)).mp hZero
