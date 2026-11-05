-- Prove2me | solution 1 for FeinbergPOMDP.WStar.theorem_5_2
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-04T18:35:00.190614+00:00
-- url     : https://prove2.me/submissions/3b106aeb-7b47-4163-92b7-91a802f87bb2

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergPOMDP.WStar

theorem solution : ¬ (∀ {S₁ S₂ S₃ ι : Type}
    [TopologicalSpace S₁] [TopologicalSpace.MetrizableSpace S₁]
    [TopologicalSpace S₂] [TopologicalSpace.MetrizableSpace S₂] [TopologicalSpace.SeparableSpace S₂]
    [MeasurableSpace S₂] [BorelSpace S₂]
    [TopologicalSpace S₃] [TopologicalSpace.MetrizableSpace S₃]
    (Ψ : S₁ → ProbabilityMeasure S₂) (hΨ : IsWeaklyContinuous Ψ)
    (F : ι → S₂ × S₃ → ℝ) (hFc : ∀ i, Continuous (F i))
    (hFeq : ∀ p : S₂ × S₃, EquicontinuousAt F p)
    (hFb : ∃ M : ℝ, ∀ i p, |F i p| ≤ M)
    (O : Set S₂) (hO : IsOpen O),
    (∀ p : S₁ × S₃, EquicontinuousAt
        (fun i (q : S₁ × S₃) => ∫ s₂ in O, F i (s₂, q.2) ∂(Ψ q.1 : Measure S₂)) p) ∧
    ∃ M : ℝ, ∀ i (q : S₁ × S₃), |∫ s₂ in O, F i (s₂, q.2) ∂(Ψ q.1 : Measure S₂)| ≤ M) := by
  intro h
  have hΨ : IsWeaklyContinuous
      (fun x : ULift.{0} ℝ => diracProba (⟨x.down⟩ : ULift.{0} ℝ)) := by
    intro s ss hss
    exact ((continuous_diracProba.comp (continuous_uliftUp.comp continuous_uliftDown)).tendsto s).comp hss
  have hO : IsOpen {y : ULift.{0} ℝ | 0 < y.down} := isOpen_lt continuous_const continuous_uliftDown
  have hsep : TopologicalSpace.SeparableSpace (ULift.{0} ℝ) :=
    (Homeomorph.ulift.{0} (X := ℝ)).symm.isQuotientMap.surjective.denseRange.separableSpace
      Homeomorph.ulift.symm.continuous
  obtain ⟨h1, -⟩ := @h (ULift.{0} ℝ) (ULift.{0} ℝ) PUnit.{1} PUnit.{1}
    _ _ _ _ hsep _ _ _ _ _ hΨ (fun _ _ => (1 : ℝ)) (fun _ => continuous_const)
    (fun p => equicontinuousAt_finite.2 fun _ => continuousAt_const) ⟨1, fun _ _ => by simp⟩
    _ hO
  have hc := (h1 (⟨0⟩, PUnit.unit)).continuousAt PUnit.unit
  have hval : ∀ x : ULift.{0} ℝ,
      (∫ _s₂ in {y : ULift.{0} ℝ | 0 < y.down}, (1 : ℝ)
        ∂((diracProba (⟨x.down⟩ : ULift.{0} ℝ) : ProbabilityMeasure _) : Measure (ULift.{0} ℝ)))
        = if 0 < x.down then 1 else 0 := by
    intro x
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
      diracProba_toMeasure_apply' _ (hO.measurableSet)]
    by_cases hx : 0 < x.down <;> simp [Set.indicator, hx]
  let qs : ℕ → ULift.{0} ℝ × PUnit.{1} := fun n => (⟨1 / ((n : ℝ) + 1)⟩, PUnit.unit)
  have hqs : Tendsto qs atTop (𝓝 (⟨0⟩, PUnit.unit)) := by
    refine Tendsto.prodMk_nhds ?_ tendsto_const_nhds
    have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact (continuous_uliftUp.tendsto _).comp this
  have hlim := hc.tendsto.comp hqs
  simp only [Function.comp_def, qs, hval] at hlim
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  simp only [hpos, if_true, lt_irrefl, if_false] at hlim
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)
