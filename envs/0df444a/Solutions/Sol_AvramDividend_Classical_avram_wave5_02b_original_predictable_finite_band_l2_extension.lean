-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02b_original_predictable_finite_band_l2_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:01:52.410206+00:00
-- url     : https://prove2.me/submissions/5c356279-a12a-49c6-8639-a21ba738877c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_original_filtration_marked_finite_band_l2_dense
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_dense_elementary_l2_isometry_extension
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_probability_l2_expectation_continuous_original_space

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasurableSpace Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    [mAll : MeasurableSpace ((ℝ≥0 × Ω) × ℝ)]
    (μ : Measure ((ℝ≥0 × Ω) × ℝ)) [IsFiniteMeasure μ]
    (hAll : mAll = (𝓕.predictable).prod
      (inferInstance : MeasurableSpace ℝ))
    (R : Set (Lp ℝ (2 : ℝ≥0∞) μ))
    (hR : R =
      {v | ∃ (t : Set ((ℝ≥0 × Ω) × ℝ)),
        t ∈ insert Set.univ (insert (∅ : Set ((ℝ≥0 × Ω) × ℝ))
          (Set.image2 (· ×ˢ ·)
            {S | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
                        S = ({⊥} ×ˢ A)) ∨
                 (∃ i : ℝ≥0, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
                        S = (Set.Ioi i ×ˢ A))}
            {C : Set ℝ | MeasurableSet C})) ∧
        ∃ (htm : MeasurableSet t) (hμt : μ t ≠ ⊤),
          indicatorConstLp (2 : ℝ≥0∞) htm hμt (1 : ℝ) = v})
    (S : Submodule ℝ (Lp ℝ (2 : ℝ≥0∞) μ))
    (hS : S = Submodule.span ℝ R)
    (I₀ : S →ₗ[ℝ] Lp ℝ (2 : ℝ≥0∞) P)
    (hIsom : ∀ x : S, ‖I₀ x‖ = ‖(x : Lp ℝ (2 : ℝ≥0∞) μ)‖)
    (hZero : ∀ x : S, ∫ ω, I₀ x ω ∂P = 0)
    (clock : Measure ℝ≥0) (ν : Measure ℝ)
    (hSource : ∀ x : S, (I₀ x : Ω → ℝ) =ᵐ[P] fun ω =>
      (∫ p, ((x : Lp ℝ (2 : ℝ≥0∞) μ) : ((ℝ≥0 × Ω) × ℝ) → ℝ)
        ((p.1, ω), p.2) ∂(NX ω)) -
      ∫ t, ∫ z, ((x : Lp ℝ (2 : ℝ≥0∞) μ) :
        ((ℝ≥0 × Ω) × ℝ) → ℝ) ((t, ω), z) ∂ν ∂clock) :
    ∃ I : Lp ℝ (2 : ℝ≥0∞) μ →L[ℝ] Lp ℝ (2 : ℝ≥0∞) P,
      (∀ x : S, I (x : Lp ℝ (2 : ℝ≥0∞) μ) = I₀ x) ∧
      (∀ v, ‖I v‖ = ‖v‖) ∧
      (∀ v, ∫ ω, I v ω ∂P = 0) ∧
      (∀ x : S, (I (x : Lp ℝ (2 : ℝ≥0∞) μ) : Ω → ℝ) =ᵐ[P]
        fun ω =>
          (∫ p, ((x : Lp ℝ (2 : ℝ≥0∞) μ) : ((ℝ≥0 × Ω) × ℝ) → ℝ)
            ((p.1, ω), p.2) ∂(NX ω)) -
          ∫ t, ∫ z, ((x : Lp ℝ (2 : ℝ≥0∞) μ) :
            ((ℝ≥0 × Ω) × ℝ) → ℝ) ((t, ω), z) ∂ν ∂clock) := by
  have hTop : S.topologicalClosure = ⊤ := by
    apply top_unique
    intro v hv
    rw [hS, hR]
    simpa only [exists_prop] using
      (avram_wave4_p1_original_filtration_marked_finite_band_l2_dense
        𝓕 μ hAll v)
  have hDense : DenseRange S.subtype := by
    change DenseRange (fun x : S => (x : Lp ℝ (2 : ℝ≥0∞) μ))
    exact denseRange_subtype_val.mpr
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr hTop)
  obtain ⟨I, hExtend, hNorm⟩ :=
    avram_wave4_p1_dense_elementary_l2_isometry_extension S I₀ hDense hIsom
  refine ⟨I, hExtend, hNorm, ?_, ?_⟩
  · intro v
    have hClosed : IsClosed
        {u : Lp ℝ (2 : ℝ≥0∞) μ | ∫ ω, I u ω ∂P = 0} :=
      isClosed_eq
        ((avram_wave4_p1_probability_l2_expectation_continuous_original_space P).comp
          I.continuous) continuous_const
    exact hDense.induction_on v hClosed (fun x => by
      change (∫ ω, I (x : Lp ℝ (2 : ℝ≥0∞) μ) ω ∂P) = 0
      exact (congrArg (fun z : Lp ℝ (2 : ℝ≥0∞) P => ∫ ω, z ω ∂P)
        (hExtend x)).trans (hZero x))
  · intro x
    rw [hExtend]
    exact hSource x
