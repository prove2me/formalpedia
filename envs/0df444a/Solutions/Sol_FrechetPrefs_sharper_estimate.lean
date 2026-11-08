-- Prove2me | solution 1 for FrechetPrefs.sharper_estimate
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:05:22.449743+00:00
-- url     : https://prove2.me/submissions/7ef8509d-015c-477b-b0a4-c7bcc39f2164

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

namespace Aux_Frechet_sharper
open FrechetPrefs Set Filter Topology

theorem reg (u : ℝ → ℝ) (hu : IsInadaUtility u) :
    DifferentiableOn ℝ u (Ioi 0) ∧ DifferentiableOn ℝ (deriv u) (Ioi 0) ∧
      ContinuousOn (deriv (deriv u)) (Ioi 0) := by
  have h1 : ContDiffOn ℝ 1 (deriv u) (Ioi 0) :=
    hu.1.deriv_of_isOpen isOpen_Ioi (one_add_one_eq_two).le
  have h0 : ContDiffOn ℝ 0 (deriv (deriv u)) (Ioi 0) :=
    h1.deriv_of_isOpen isOpen_Ioi (zero_add 1).le
  have hd : DifferentiableOn ℝ u (Ioi 0) := hu.1.differentiableOn (by norm_num)
  have hd' : DifferentiableOn ℝ (deriv u) (Ioi 0) := h1.differentiableOn one_ne_zero
  exact ⟨hd, hd', h0.continuousOn⟩

theorem u2_nonpos (u : ℝ → ℝ) (hu : IsInadaUtility u) : ∀ x ∈ Ioi (0 : ℝ), deriv (deriv u) x ≤ 0 := by
  obtain ⟨_, hd', hc⟩ := reg u hu
  intro x0 hx0
  by_contra hpos
  push_neg at hpos
  have hx0' : (0 : ℝ) < x0 := hx0
  -- |u''| ≥ u''(x0) on (0, x0]
  have hab : ∀ x ∈ Ioc (0 : ℝ) x0, deriv (deriv u) x0 ≤ |deriv (deriv u) x| := by
    intro x hx
    have := hu.2.2.2 (show x ∈ Ioi (0:ℝ) from hx.1) hx0 hx.2
    simp only at this
    rw [abs_of_pos hpos] at this
    exact this
  -- u'' > 0 on (0, x0]
  have hpos' : ∀ x ∈ Ioc (0 : ℝ) x0, 0 < deriv (deriv u) x := by
    intro x hx
    by_contra hneg
    push_neg at hneg
    rcases hneg.lt_or_eq with hlt | heq
    · have hsub : Icc x x0 ⊆ Ioi 0 := fun y hy => lt_of_lt_of_le hx.1 hy.1
      obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc hx.2 (hc.mono hsub)
        (show (0 : ℝ) ∈ Icc (deriv (deriv u) x) (deriv (deriv u) x0) from ⟨hlt.le, hpos.le⟩)
      have := hab c ⟨lt_of_lt_of_le hx.1 hc1.1, hc1.2⟩
      rw [hc2, abs_zero] at this
      linarith
    · have := hab x hx
      rw [heq, abs_zero] at this
      linarith
  -- u' monotone on (0, x0]
  have hmono : MonotoneOn (deriv u) (Ioc 0 x0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 x0)
    · exact (hd'.mono Ioc_subset_Ioi_self).continuousOn
    · exact hd'.mono (interior_subset.trans Ioc_subset_Ioi_self)
    · intro x hx
      rw [interior_Ioc] at hx
      exact (hpos' x ⟨hx.1, hx.2.le⟩).le
  have hT := hu.2.1
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), deriv u x0 + 1 < deriv u x ∧ x ∈ Ioo 0 x0 :=
    (hT.eventually_gt_atTop (deriv u x0 + 1)).and (Ioo_mem_nhdsGT hx0')
  obtain ⟨x, hx1, hx2⟩ := hev.exists
  have := hmono ⟨hx2.1, hx2.2.le⟩ ⟨hx0', le_refl _⟩ hx2.2.le
  linarith

end Aux_Frechet_sharper

open FrechetPrefs Aux_Frechet_sharper in
theorem solution (u : ℝ → ℝ) (hu : IsInadaUtility u) (θ g z : ℝ) (hθ : 0 < θ)
    (hg : 0 < g) (hgz : g ≤ z) (heq : 1 / θ * deriv u g + g = z) :
    g ≤ z - 1 / θ * deriv u z := by
  obtain ⟨_, hd', _⟩ := reg u hu
  have hanti : AntitoneOn (deriv u) (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0) hd'.continuousOn
    · exact hd'.mono interior_subset
    · intro x hx
      rw [interior_Ioi] at hx
      exact u2_nonpos u hu x hx
  have h := hanti (show g ∈ Set.Ioi (0:ℝ) from hg) (show z ∈ Set.Ioi (0:ℝ) from lt_of_lt_of_le hg hgz) hgz
  have hθ' : 0 < 1 / θ := by positivity
  have := mul_le_mul_of_nonneg_left h hθ'.le
  linarith
