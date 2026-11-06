-- Prove2me | solution 1 for DROOptimal.Continuous.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T10:19:36.471201+00:00
-- url     : https://prove2.me/submissions/76380bc2-f40f-4266-8cfd-0f42a51a63b6

import Mathlib
import Definitions.Def_DROOptimal_Continuous_Setting

open MeasureTheory Filter Topology
open DROOptimal.Continuous

theorem solution {d n : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin d))} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : IsCompact X) (hΞ : IsCompact Ξ) (γ : ↥X → ↥Ξ → ℝ)
    (hγ : Continuous (fun p : ↥X × ↥Ξ => γ p.1 p.2)) :
    IsPredictor (cost γ) := by
  have : CompactSpace ↥Ξ := isCompact_iff_compactSpace.mp hΞ
  let G : C(↥X × ↥Ξ, ℝ) := ⟨fun p => γ p.1 p.2, hγ⟩
  have hF : Continuous (fun x => G.curry x) := G.curry.continuous
  have hint : ∀ (f : C(↥Ξ, ℝ)) (P : DROOptimal.Continuous.Dist Ξ),
      Integrable (fun ξ => f ξ) (P : Measure ↥Ξ) := fun f P =>
    (BoundedContinuousFunction.mkOfCompact f).integrable _
  have hΦ : Continuous (fun q : C(↥Ξ, ℝ) × DROOptimal.Continuous.Dist Ξ =>
      ∫ ξ, q.1 ξ ∂(q.2 : Measure ↥Ξ)) := by
    rw [continuous_iff_continuousAt]
    rintro ⟨f0, P0⟩
    have h2 : Continuous (fun q : C(↥Ξ, ℝ) × DROOptimal.Continuous.Dist Ξ =>
        ∫ ξ, f0 ξ ∂(q.2 : Measure ↥Ξ)) :=
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
        (BoundedContinuousFunction.mkOfCompact f0)).comp continuous_snd
    have h1 : Tendsto (fun q : C(↥Ξ, ℝ) × DROOptimal.Continuous.Dist Ξ =>
        ∫ ξ, (q.1 - f0) ξ ∂(q.2 : Measure ↥Ξ)) (𝓝 (f0, P0)) (𝓝 0) := by
      apply squeeze_zero_norm (a := fun q => ‖q.1 - f0‖)
      · intro q
        have := norm_integral_le_of_norm_le_const (μ := (q.2 : Measure ↥Ξ))
          (f := fun ξ => (q.1 - f0) ξ) (C := ‖q.1 - f0‖)
          (Eventually.of_forall fun ξ => ContinuousMap.norm_coe_le_norm _ ξ)
        simpa using this
      · have : Continuous (fun q : C(↥Ξ, ℝ) × DROOptimal.Continuous.Dist Ξ => ‖q.1 - f0‖) := by
          fun_prop
        simpa using this.tendsto (f0, P0)
    have hsum := h1.add (h2.tendsto (f0, P0))
    simp only [zero_add] at hsum
    refine hsum.congr fun q => ?_
    rw [← integral_add (hint _ _) (hint _ _)]
    simp
  exact hΦ.comp ((hF.comp continuous_fst).prodMk continuous_snd)
