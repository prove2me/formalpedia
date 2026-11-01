-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_finite_activity_residual_left_locally_constant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:52:53.206253+00:00
-- url     : https://prove2.me/submissions/fe69a54d-7221-4a20-a316-f83911e8cc48

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_finite_residual_range_on_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology Finset AvramDividend.Classical
open scoped NNReal ENNReal

/-- On the original finite-activity BV path, nonjump times are left-locally
constant times for the true drift residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t ≤ T →
      X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t = 0 →
        Filter.Eventually
          (fun u : ℝ≥0 =>
            (u : ℝ) * X.drift - X.X u ω =
              (t : ℝ) * X.drift - X.X t ω)
          (nhdsWithin t (Iio t : Set ℝ≥0)) := by
  classical
  filter_upwards
    [avram_wave4_04a_bv_actual_finite_residual_range_on_horizon
      X hBV hFinite T hT] with ω hω
  obtain ⟨S, hS⟩ := hω
  intro t ht htT hNoJump
  letI : (𝓝[<] t).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  obtain ⟨l, hl⟩ := X.leftLim ω t ht
  have hXLeft :
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) t = l :=
    leftLim_eq_of_tendsto hl
  have hlEq : l = X.X t ω := by
    rw [hXLeft] at hNoJump
    linarith
  let Y : ℝ≥0 → ℝ := fun u => (u : ℝ) * X.drift - X.X u ω
  have hlin :
      Tendsto (fun u : ℝ≥0 => (u : ℝ) * X.drift)
        (𝓝[<] t) (𝓝 ((t : ℝ) * X.drift)) :=
    (NNReal.continuous_coe.mul continuous_const).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hLeft : Tendsto Y (𝓝[<] t) (𝓝 (Y t)) := by
    simpa [Y, hlEq] using hlin.sub hl
  let R : Finset ℝ := S.erase (Y t)
  have hClosed : IsClosed ((R : Finset ℝ) : Set ℝ) :=
    (Finset.finite_toSet R).isClosed
  have hNot : Y t ∈ (((R : Finset ℝ) : Set ℝ)ᶜ) := by
    simp [R]
  have hEventually : ∀ᶠ u in nhdsWithin t (Iio t : Set ℝ≥0),
      Y u ∈ (((R : Finset ℝ) : Set ℝ)ᶜ) :=
    hLeft.eventually (hClosed.isOpen_compl.mem_nhds hNot)
  have hWithin : ∀ᶠ u in nhdsWithin t (Iio t : Set ℝ≥0), u < t := self_mem_nhdsWithin
  filter_upwards [hEventually, hWithin] with u hu huLT
  change Y u = Y t
  by_contra hne
  have hm : Y u ∈ R := by
    simp only [R, Finset.mem_erase]
    exact ⟨hne, hS u ((le_of_lt huLT).trans htT)⟩
  exact hu hm
