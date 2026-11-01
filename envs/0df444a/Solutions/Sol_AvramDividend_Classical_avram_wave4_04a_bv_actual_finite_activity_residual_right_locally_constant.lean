-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_finite_activity_residual_right_locally_constant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:09:51.367602+00:00
-- url     : https://prove2.me/submissions/fcbe8d6b-1624-426f-b61b-a470ef60f20d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_finite_residual_range_on_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology Finset AvramDividend.Classical
open scoped NNReal ENNReal

/-- For an actual finite-activity BV source, its residual is locally constant
from the right at every point of every fixed finite horizon, almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      ∀ᶠ u in nhdsWithin t (Ici t), u ≤ T →
        (u : ℝ) * X.drift - X.X u ω =
          (t : ℝ) * X.drift - X.X t ω := by
  classical
  filter_upwards
    [avram_wave4_04a_bv_actual_finite_residual_range_on_horizon
      X hBV hFinite T hT] with ω hω
  obtain ⟨S, hS⟩ := hω
  intro t ht
  let Y : ℝ≥0 → ℝ := fun u => (u : ℝ) * X.drift - X.X u ω
  have hc : Continuous (fun v : ℝ≥0 => (v : ℝ) * X.drift) :=
    NNReal.continuous_coe.mul continuous_const
  have hRight : ContinuousWithinAt Y (Ici t) t := by
    exact hc.continuousWithinAt.sub (X.rightCont ω t)
  let R : Finset ℝ := S.erase (Y t)
  have hClosed : IsClosed ((R : Finset ℝ) : Set ℝ) :=
    (Finset.finite_toSet R).isClosed
  have hNot : Y t ∈ (((R : Finset ℝ) : Set ℝ)ᶜ) := by
    simp [R]
  have hEventually : ∀ᶠ u in nhdsWithin t (Ici t),
      Y u ∈ (((R : Finset ℝ) : Set ℝ)ᶜ) :=
    hRight.tendsto.eventually (hClosed.isOpen_compl.mem_nhds hNot)
  filter_upwards [hEventually] with u hu huT
  change Y u = Y t
  by_contra hne
  have hm : Y u ∈ R := by
    simp only [R, Finset.mem_erase]
    exact ⟨hne, hS u huT⟩
  exact hu hm
