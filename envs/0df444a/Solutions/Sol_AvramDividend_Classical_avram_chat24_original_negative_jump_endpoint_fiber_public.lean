-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_original_negative_jump_endpoint_fiber_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:48:42.049208+00:00
-- url     : https://prove2.me/submissions/025223ec-0ad3-48ca-8d97-57142d34c3e6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (E : ℝ≥0 → Prop) [DecidablePred E] (f : ℝ≥0 × ℝ → ℝ) :
    let z : ℝ≥0 → ℝ := fun u => X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let NX : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ z u ≠ 0}).map (fun u => (u, z u))
    (∫ p, if p.1 = t ∧ E p.1 ∧ p.2 < 0 then f p else 0 ∂NX) =
      if E t ∧ z t < 0 then f (t, z t) else 0 := by
  classical
  intro z NX
  have hz : Measurable z :=
    (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp
      (measurable_id.prodMk measurable_const)
  have hι : MeasurableEmbedding (fun u : ℝ≥0 => (u, z u)) := by
    refine ⟨fun u v huv => congrArg Prod.fst huv, measurable_id.prodMk hz, ?_⟩
    intro s hs
    have heq : (fun u : ℝ≥0 => (u, z u)) '' s =
        {p : ℝ≥0 × ℝ | p.1 ∈ s ∧ p.2 = z p.1} := by
      ext p
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨hu, rfl⟩
      · rintro ⟨hp, hpz⟩
        exact ⟨p.1, hp, Prod.ext rfl hpz.symm⟩
    rw [heq]
    exact (hs.preimage measurable_fst).inter
      (measurableSet_eq_fun measurable_snd (hz.comp measurable_fst))
  let r : ℝ := if E t ∧ z t < 0 then f (t, z t) else 0
  have hfun : (fun u : ℝ≥0 => if u = t ∧ E u ∧ z u < 0 then f (u, z u) else 0) =
      ({t} : Set ℝ≥0).indicator (fun _ => r) := by
    funext u
    by_cases hu : u = t
    · subst u
      simp [Set.indicator, r]
    · simp [Set.indicator, hu]
  dsimp only [NX]
  rw [hι.integral_map]
  change (∫ u, if u = t ∧ E u ∧ z u < 0 then f (u, z u) else 0
    ∂(Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ z u ≠ 0})) = r
  rw [hfun, integral_indicator_const r (measurableSet_singleton t)]
  by_cases hzt : z t = 0
  · simp [r, hzt]
  · simp [Measure.real, Measure.restrict_apply, ht, hzt]
