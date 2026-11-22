-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_original_physical_separated_simple_mark_rightcont_conditional_increment_zero_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:29:07.573455+00:00
-- url     : https://prove2.me/submissions/be29071c-7998-4f1a-8ecf-3b2c296092f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_finite_simple_mark_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (r : ℕ → ℝ≥0)
    (hsr : ∀ k, s < r k) (hrt : ∀ k, r k ≤ t)
    (hShort : Tendsto (fun k => r k - s) atTop (𝓝 0))
    (hLong : Tendsto (fun k => t - r k) atTop (𝓝 (t - s)))
    (S : Set ℝ) (hS : MeasurableSet S)
    (hν : X.ν S < ⊤)
    (g : SimpleFunc ℝ ℝ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    let F : Ω → ℝ := fun ω =>
      ∑ y ∈ g.range, y *
        ((NX ω (Ioc s t ×ˢ B y)).toReal -
          (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B y)).toReal)
    P[F | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ))  := by
  classical
  intro NX B F
  have hBm : ∀ y ∈ g.range, MeasurableSet (B y) := by
    intro y hy
    exact hS.inter (g.measurable (measurableSet_singleton y))
  have hFinite : ∀ y ∈ g.range, X.ν (B y) ≠ ⊤ := by
    intro y hy
    have hle : X.ν (B y) ≤ X.ν S := measure_mono Set.inter_subset_left
    exact ne_of_lt (lt_of_le_of_lt hle hν)
  let J : ℝ → ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun y a b ω =>
    NX ω (Ioc a b ×ˢ B y)
  have hJ : ∀ y ∈ g.range, ∀ a b ω, J y a b ω =
      NX ω (Ioc a b ×ˢ B y) := by
    intros
    rfl
  have hJm : ∀ y ∈ g.range, Measurable (J y s t) := by
    intro y hy
    have hraw :=
      avram_p2_f_weighted_original_intrinsic_rectangle_measurable
        X s (t - s) (B y) (hBm y hy)
    have ht : s + (t - s) = t := by
      exact add_tsub_cancel_of_le hst
    simpa only [J, NX, ht] using hraw
  have hSource :=
    avram_anoise17_original_finite_simple_mark_condexp_zero
      X s t r hsr hrt hShort hLong g.range B hBm hFinite
      J (by
        intro y hy a b ω
        rfl) hJm (fun y => y)
  simpa only [F, J, NX, B] using hSource
