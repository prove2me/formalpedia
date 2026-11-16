-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_finite_jump_compensated_residual_left_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:54:58.89613+00:00
-- url     : https://prove2.me/submissions/e4776b4f-72ed-4af1-a128-beb72e6dd80a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva_finite_jumps_eventually_affine_strict_left
import Theorems.Thm_AvramDividend_Classical_avram_bv_leftLim_affine_of_eventuallyEq
import Theorems.Thm_AvramDividend_Classical_finite_marked_step_sum_left_limit
import Theorems.Thm_AvramDividend_Classical_avram_bva_finite_compensated_residual_left_right_exact
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set AvramDividend.Classical
open scoped NNReal Topology
noncomputable section

theorem solution
    (f : ℝ≥0 → ℝ) (drift : ℝ) (T : ℝ≥0)
    (hFinite : Set.Finite {t : ℝ≥0 |
      0 < t ∧ t ≤ T ∧ f t - Function.leftLim f t ≠ 0})
    (hFlat : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (∀ u ∈ Set.Ioc s t,
        f u - Function.leftLim f u = 0) →
      (t : ℝ) * drift - f t = (s : ℝ) * drift - f s) :
    ∀ u ∈ hFinite.toFinset,
      Function.leftLim
        (fun t : ℝ≥0 => (t : ℝ) * drift - f t -
          Finset.sum hFinite.toFinset (fun v => if v ≤ t then
            Function.leftLim f v - f v else 0)) u =
      (u : ℝ) * drift - f u -
        Finset.sum hFinite.toFinset (fun v => if v ≤ u then
          Function.leftLim f v - f v else 0) := by
  intro u hu
  let S : Finset ℝ≥0 := hFinite.toFinset
  have huPos : 0 < u := (hFinite.mem_toFinset.mp hu).1
  haveI : (𝓝[<] u).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, huPos⟩
  obtain ⟨a, ha⟩ := avram_bva_finite_jumps_eventually_affine_strict_left
    f drift T hFinite hFlat u hu
  let hCoord : Tendsto (fun t : ℝ≥0 => (t : ℝ))
      (𝓝[<] u) (𝓝 (u : ℝ)) :=
    (continuous_subtype_val : Continuous (fun t : ℝ≥0 => (t : ℝ))).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  let hAffine : Tendsto (fun t : ℝ≥0 => a + drift * (t : ℝ))
      (𝓝[<] u) (𝓝 (a + drift * (u : ℝ))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hCoord)
  let hFLeft : Function.leftLim f u = a + drift * (u : ℝ) :=
    avram_bv_leftLim_affine_of_eventuallyEq f u a drift ha
  have hF : Tendsto f (𝓝[<] u) (𝓝 (Function.leftLim f u)) := by
    rw [hFLeft]
    exact hAffine.congr' ha.symm
  let hK : Tendsto
      (fun t : ℝ≥0 =>
        Finset.sum S (fun v => if v ≤ t then Function.leftLim f v - f v else 0))
      (𝓝[<] u)
      (𝓝 (Finset.sum S (fun v => if v < u then Function.leftLim f v - f v else 0))) :=
    finite_marked_step_sum_left_limit S (fun v : ℝ≥0 => v)
      (fun v => Function.leftLim f v - f v) u
  let hG : Tendsto
      (fun t : ℝ≥0 => (t : ℝ) * drift - f t -
        Finset.sum S (fun v => if v ≤ t then Function.leftLim f v - f v else 0))
      (𝓝[<] u)
      (𝓝 ((u : ℝ) * drift - Function.leftLim f u -
        Finset.sum S (fun v => if v < u then Function.leftLim f v - f v else 0))) :=
    ((hCoord.mul tendsto_const_nhds).sub hF).sub hK
  let hLeft : Function.leftLim
      (fun t : ℝ≥0 => (t : ℝ) * drift - f t -
        Finset.sum S (fun v => if v ≤ t then Function.leftLim f v - f v else 0)) u =
      (u : ℝ) * drift - Function.leftLim f u -
        Finset.sum S (fun v => if v < u then Function.leftLim f v - f v else 0) :=
    leftLim_eq_of_tendsto hG
  let hCancel := avram_bva_finite_compensated_residual_left_right_exact
    f drift S u hu
  exact hLeft.trans hCancel.symm
