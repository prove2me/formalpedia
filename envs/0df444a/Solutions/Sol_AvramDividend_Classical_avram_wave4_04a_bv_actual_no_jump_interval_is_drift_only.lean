-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:47:07.804977+00:00
-- url     : https://prove2.me/submissions/aee2d4e0-808b-4285-8949-6d84bd193fc0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_finite_residual_range_on_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology Finset AvramDividend.Classical
open scoped NNReal ENNReal

/-- A source interval with no actual Lévy jump is a drift-only interval:
the finite-range monotone residual cannot move continuously. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (∀ u : ℝ≥0, u ∈ Ioc s t →
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      (t : ℝ) * X.drift - X.X t ω =
        (s : ℝ) * X.drift - X.X s ω := by
  classical
  filter_upwards
    [avram_wave4_04a_bv_actual_finite_residual_range_on_horizon
      X hBV hFinite T hT] with ω hω
  obtain ⟨S, hS⟩ := hω
  intro s t hst htT hNoJump
  let Y : ℝ≥0 → ℝ := fun u => (u : ℝ) * X.drift - X.X u ω
  have hContinuousX :
      ContinuousOn (fun u : ℝ≥0 => X.X u ω) (Icc s t) := by
    intro u hu
    by_cases hus : u = s
    · subst u
      apply (X.rightCont ω s).mono
      intro v hv
      exact hv.1
    · have hsu : s < u := lt_of_le_of_ne hu.1 (Ne.symm hus)
      have huPos : 0 < u := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ s) hsu
      have hJump : X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 :=
        hNoJump u ⟨hsu, hu.2⟩
      letI : (𝓝[<] u).NeBot :=
        nhdsLT_neBot_of_exists_lt ⟨0, huPos⟩
      obtain ⟨l, hl⟩ := X.leftLim ω u huPos
      have hlValue :
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = l :=
        leftLim_eq_of_tendsto hl
      have hlEq : l = X.X u ω := by
        rw [hlValue] at hJump
        exact (sub_eq_zero.mp hJump).symm
      have hcLeft :
          ContinuousWithinAt (fun v : ℝ≥0 => X.X v ω) (Iio u) u := by
        change Tendsto (fun v : ℝ≥0 => X.X v ω) (𝓝[<] u)
          (𝓝 (X.X u ω))
        simpa only [hlEq] using hl
      have hcBoth :
          ContinuousWithinAt (fun v : ℝ≥0 => X.X v ω)
            (Iio u ∪ Ici u) u :=
        hcLeft.union (X.rightCont ω u)
      have hc : ContinuousAt (fun v : ℝ≥0 => X.X v ω) u := by
        simpa only [Set.Iio_union_Ici, continuousWithinAt_univ] using hcBoth
      exact hc.continuousWithinAt
  have hContinuousDrift :
      Continuous (fun u : ℝ≥0 => (u : ℝ) * X.drift) :=
    NNReal.continuous_coe.mul continuous_const
  have hContinuousY : ContinuousOn Y (Icc s t) := by
    exact hContinuousDrift.continuousOn.sub hContinuousX
  have hMaps : MapsTo Y (Icc s t) ((S : Finset ℝ) : Set ℝ) := by
    intro u hu
    exact hS u (hu.2.trans htT)
  have hConst : Y s = Y t :=
    (isPreconnected_Icc.constant_of_mapsTo
      (Finset.finite_toSet S).isDiscrete hContinuousY hMaps)
      ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩
  change Y t = Y s
  exact hConst.symm
