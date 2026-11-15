-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a315_eventual_ae_two_error_expected_L1_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:57:42.338123+00:00
-- url     : https://prove2.me/submissions/900135e5-74ec-4f57-bcf0-b1cba232c0c7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F E Q : ℕ → Ω → ℝ) (C D : ℝ)
    (hFI : ∀ m, Integrable (F m) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hQI : ∀ m, Integrable (Q m) P)
    (hFpos : ∀ m, ∀ᵐ ω ∂P, 0 ≤ F m ω)
    (hBound : ∀ᶠ m : ℕ in atTop, ∀ᵐ ω ∂P,
      F m ω ≤ C*E m ω + D*Q m ω)
    (hELim : Tendsto (fun m => ∫ ω, E m ω ∂P) atTop (𝓝 (0:ℝ)))
    (hQLim : Tendsto (fun m => ∫ ω, Q m ω ∂P) atTop (𝓝 (0:ℝ))) :
    Tendsto (fun m => ∫ ω, F m ω ∂P) atTop (𝓝 (0:ℝ)) := by
  have hLo (m : ℕ) : 0 ≤ (∫ ω, F m ω ∂P) :=
    integral_nonneg_of_ae (hFpos m)
  have hHi : ∀ᶠ m : ℕ in atTop,
      (∫ ω, F m ω ∂P) ≤
        C*(∫ ω, E m ω ∂P)+D*(∫ ω, Q m ω ∂P) := by
    filter_upwards [hBound] with m hm
    have hMajor :
        Integrable (fun ω => C*E m ω+D*Q m ω) P :=
      ((hEI m).const_mul C).add ((hQI m).const_mul D)
    calc
      (∫ ω, F m ω ∂P) ≤
        ∫ ω, C*E m ω+D*Q m ω ∂P :=
        integral_mono_ae (hFI m) hMajor hm
      _ = C*(∫ ω, E m ω ∂P)+D*(∫ ω, Q m ω ∂P) := by
        rw [integral_add ((hEI m).const_mul C)
          ((hQI m).const_mul D)]
        simp [integral_const_mul]
  have ht : Tendsto (fun m =>
      C*(∫ ω, E m ω ∂P)+D*(∫ ω, Q m ω ∂P))
      atTop (𝓝 (0:ℝ)) := by
    simpa using (hELim.const_mul C).add (hQLim.const_mul D)
  exact squeeze_zero' (Filter.Eventually.of_forall hLo) hHi ht
