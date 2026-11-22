-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_original_physical_simple_mark_condExp_all_strict_time_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:38:36.036821+00:00
-- url     : https://prove2.me/submissions/b70a2833-b0e2-4bdb-8f91-c5793b9e3b1e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_finite_simple_mark_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_separated_simple_mark_rightcont_conditional_increment_zero_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_nonnegative_time_short_right_bridge_sequence_20261122
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s < t)
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
  obtain ⟨r, hsr, hrt, hShort, hLong⟩ :=
    avram_oai_nonnegative_time_short_right_bridge_sequence_20261122 s t hst
  exact avram_oai_original_physical_separated_simple_mark_rightcont_conditional_increment_zero_20261122
    X s t hst.le r hsr hrt hShort hLong S hS hν g
