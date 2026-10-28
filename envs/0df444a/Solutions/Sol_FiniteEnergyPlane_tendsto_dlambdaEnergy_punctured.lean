-- Prove2me | solution 1 for FiniteEnergyPlane.tendsto_dlambdaEnergy_punctured
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-26T16:44:08.740015+00:00
-- url     : https://prove2.me/submissions/46f58644-34e1-4019-8963-74ff67fd0ae7

import Definitions.Def_FiniteEnergyPlane_Setting



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- `dλ`-energy as a measure. -/
theorem dlambdaEnergy_eq_withDensity_aux {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (s : Set ℂ)
    (hs : MeasurableSet s) :
    dlambdaEnergy H s u =
      (volume.withDensity (fun z => ENNReal.ofReal (dlambdaDensity H u z))) s :=
  (withDensity_apply _ hs).symm

/-- A plane whose `dλ`-energy vanishes on every disc has zero `dλ`-energy. -/
theorem dlambdaEnergy_univ_eq_zero_of_ball_aux {n : ℕ} (H : V n → ℝ) (w : ℂ → V n)
    (h0 : ∀ R : ℝ, dlambdaEnergy H (ball 0 R) w = 0) : dlambdaEnergy H Set.univ w = 0 := by
  set μ := volume.withDensity (fun z => ENNReal.ofReal (dlambdaDensity H w z)) with hμ
  have hmono : Monotone (fun N : ℕ => ball (0 : ℂ) N) :=
    fun i j hij => ball_subset_ball (by exact_mod_cast hij)
  have hU : (⋃ N : ℕ, ball (0 : ℂ) N) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    exact Set.mem_iUnion.2 ⟨N, mem_ball_zero_iff.2 hN⟩
  have h := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hU, ← dlambdaEnergy_eq_withDensity_aux H w _ MeasurableSet.univ] at h
  have hc : (μ ∘ fun N : ℕ => ball (0 : ℂ) N) = fun _ => 0 := by
    funext N
    simp only [Function.comp_apply]
    rw [← dlambdaEnergy_eq_withDensity_aux H w _ measurableSet_ball, h0]
  rw [hc] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The `dλ`-energy of small punctured discs tends to `0`. -/
theorem tendsto_dlambdaEnergy_punctured_aux {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (hD : dlambdaEnergy H {x : ℂ | x ≠ 0 ∧ ‖x‖ < 1} u ≠ ⊤) :
    Tendsto (fun r : ℝ => dlambdaEnergy H {x : ℂ | x ≠ 0 ∧ ‖x‖ < r} u) (𝓝[>] 0) (𝓝 0) := by
  set μ := volume.withDensity (fun z => ENNReal.ofReal (dlambdaDensity H u z)) with hμ
  have hmeas : ∀ r : ℝ, MeasurableSet {x : ℂ | x ≠ 0 ∧ ‖x‖ < r} := fun r =>
    (measurableSet_singleton (0 : ℂ)).compl.inter (measurableSet_lt measurable_norm measurable_const)
  have h := tendsto_measure_biInter_gt (μ := μ) (s := fun r : ℝ => {x : ℂ | x ≠ 0 ∧ ‖x‖ < r})
    (a := 0) (fun r _ => (hmeas r).nullMeasurableSet)
    (fun i j _ hij x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hij⟩)
    ⟨1, one_pos, by rw [← dlambdaEnergy_eq_withDensity_aux H u _ (hmeas 1)]; exact hD⟩
  have hI : (⋂ r > (0 : ℝ), {x : ℂ | x ≠ 0 ∧ ‖x‖ < r}) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hx
    by_cases h0 : x = 0
    · exact (hx 1 one_pos).1 h0
    · exact lt_irrefl _ (hx ‖x‖ (norm_pos_iff.2 h0)).2
  rw [hI, measure_empty] at h
  refine h.congr fun r => ?_
  exact (dlambdaEnergy_eq_withDensity_aux H u _ (hmeas r)).symm

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (hD : dlambdaEnergy H {x : ℂ | x ≠ 0 ∧ ‖x‖ < 1} u ≠ ⊤) :
    Tendsto (fun r : ℝ => dlambdaEnergy H {x : ℂ | x ≠ 0 ∧ ‖x‖ < r} u) (𝓝[>] 0) (𝓝 0) :=
  tendsto_dlambdaEnergy_punctured_aux H u hD
