-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_source_jump_times_have_uniform_positive_separation_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:37:03.653555+00:00
-- url     : https://prove2.me/submissions/fab34f3b-9afd-4ecd-a2ae-fae9db8b2d99

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every finite set of genuine times has a positive uniform pairwise
distance, with no topological or stochastic enlargement. -/
private theorem finite_nnreal_times_separated (S : Finset ℝ≥0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ≥0, u ∈ S → v ∈ S → u ≠ v → δ ≤ dist u v := by
  classical
  let D : Finset (ℝ≥0 × ℝ≥0) :=
    (S.product S).filter (fun p => p.1 ≠ p.2)
  by_cases hD : D.Nonempty
  · let E : Finset ℝ := D.image (fun p => dist p.1 p.2)
    have hE : E.Nonempty := by
      obtain ⟨p, hp⟩ := hD
      exact ⟨dist p.1 p.2, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    refine ⟨E.min' hE, ?_, ?_⟩
    · obtain ⟨p, hp, heq⟩ :=
        Finset.mem_image.mp (Finset.min'_mem E hE)
      have hp_ne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      have hp_pos : 0 < dist p.1 p.2 := dist_pos.mpr hp_ne
      rw [← heq]
      exact hp_pos
    · intro u v hu hv huv
      have hpair : (u, v) ∈ D := by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hu, hv⟩, huv⟩
      have hdist : dist u v ∈ E := by
        exact Finset.mem_image.mpr ⟨(u, v), hpair, rfl⟩
      exact Finset.min'_le E _ hdist
  · refine ⟨1, by positivity, ?_⟩
    intro u v hu hv huv
    have hpair : (u, v) ∈ D := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hu, hv⟩, huv⟩
    exact False.elim (hD ⟨(u, v), hpair⟩)

/-- Actual finite-activity BV Lévy jumps are uniformly separated on each
fixed finite horizon on one P-full event, for the original X path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ≥0,
        (u ≤ T ∧ 0 < u ∧ X.X u ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) u ≠ 0) →
        (v ≤ T ∧ 0 < v ∧ X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0) →
        u ≠ v → δ ≤ dist u v := by
  filter_upwards
    [avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon
      X hBV hFinite T hT] with ω hω
  obtain ⟨δ, hδ, hsep⟩ := finite_nnreal_times_separated hω.toFinset
  refine ⟨δ, hδ, ?_⟩
  intro u v hu hv huv
  apply hsep u v
  · exact (Set.Finite.mem_toFinset hω).mpr hu
  · exact (Set.Finite.mem_toFinset hω).mpr hv
  · exact huv
