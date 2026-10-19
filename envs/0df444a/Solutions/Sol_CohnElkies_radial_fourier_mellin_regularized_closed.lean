-- Prove2me | solution 1 for CohnElkies.radial_fourier_mellin_regularized_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/4221b8aa-1de3-4e7a-9900-4fbb38fa665f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialProfile_mellin_differentiableAt

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0)
    (hhatZero : (𝓕 f : TestFunction d) (0 : Euclidean d) = 0)
    (s : ℂ) (hs : 0 ≤ s.re) (hsd : s.re ≤ (d : ℝ)) :
    mellin (radialProfile hd (𝓕 f : TestFunction d)) s *
        (Complex.Gamma (s / 2))⁻¹ =
      (Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
        (mellin (radialProfile hd f) ((d : ℂ) - s) *
          (Complex.Gamma (((d : ℂ) - s) / 2))⁻¹) := by
  let U : Set ℂ := Complex.re ⁻¹' Ioo (0 : ℝ) (d : ℝ)
  let T : Set ℂ := Complex.re ⁻¹' Icc (0 : ℝ) (d : ℝ)
  let L : ℂ → ℂ := fun w =>
    mellin (radialProfile hd (𝓕 f : TestFunction d)) w *
      (Complex.Gamma (w / 2))⁻¹
  let G : ℂ → ℂ := fun w =>
    (Real.pi : ℂ) ^ ((d : ℂ) / 2 - w) *
      (mellin (radialProfile hd f) ((d : ℂ) - w) *
        (Complex.Gamma (((d : ℂ) - w) / 2))⁻¹)
  have hinv : Continuous (fun w : ℂ => (Complex.Gamma w)⁻¹) :=
    Complex.differentiable_one_div_Gamma.continuous
  have hhat : ContinuousOn
      (fun w : ℂ =>
        mellin (radialProfile hd (𝓕 f : TestFunction d)) w) T := by
    intro w hw
    change 0 ≤ w.re ∧ w.re ≤ (d : ℝ) at hw
    exact
      (radialProfile_mellin_differentiableAt hd
        (𝓕 f : TestFunction d)
        (gaussianMellin_fourier_radial hf) hhatZero w
        (by linarith [hw.1])).continuousAt.continuousWithinAt
  have hprimal : ContinuousOn
      (fun w : ℂ =>
        mellin (radialProfile hd f) ((d : ℂ) - w)) T := by
    intro w hw
    change 0 ≤ w.re ∧ w.re ≤ (d : ℝ) at hw
    have hinner : ContinuousAt (fun v : ℂ => (d : ℂ) - v) w := by
      fun_prop
    have hre : -2 < (((d : ℂ) - w).re) := by
      norm_num
      linarith [hw.2]
    exact
      ((radialProfile_mellin_differentiableAt hd f hf hzero
        ((d : ℂ) - w) hre).continuousAt.comp
        hinner).continuousWithinAt
  have hL : ContinuousOn L T := by
    try dsimp [L]
    exact hhat.mul
      (hinv.comp (continuous_id.div_const (2 : ℂ))).continuousOn
  have hpi :
      Continuous (fun w : ℂ =>
        (Real.pi : ℂ) ^ ((d : ℂ) / 2 - w)) := by
    exact (continuous_const.sub continuous_id).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hG : ContinuousOn G T := by
    try dsimp [G]
    exact hpi.continuousOn.mul
      (hprimal.mul
        (hinv.comp
          ((continuous_const.sub continuous_id).div_const
            (2 : ℂ))).continuousOn)
  have heq : Set.EqOn L G U := by
    intro w hw
    change 0 < w.re ∧ w.re < (d : ℝ) at hw
    have hg₁ : Complex.Gamma (w / 2) ≠ 0 := by
      apply Complex.Gamma_ne_zero_of_re_pos
      norm_num
      linarith [hw.1]
    have hg₂ : Complex.Gamma (((d : ℂ) - w) / 2) ≠ 0 := by
      apply Complex.Gamma_ne_zero_of_re_pos
      norm_num
      linarith [hw.2]
    try dsimp [L, G]
    rw [radial_fourier_mellin_strip hd f hf w hw.1 hw.2]
    field_simp
  have hUT : U ⊆ T := by
    intro w hw
    exact ⟨hw.1.le, hw.2.le⟩
  have hdreal : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hTU : T ⊆ closure U := by
    try dsimp [T, U]
    rw [Complex.closure_preimage_re,
      closure_Ioo (ne_of_lt hdreal)]
  exact heq.of_subset_closure hL hG hUT hTU ⟨hs, hsd⟩
end CohnElkies
