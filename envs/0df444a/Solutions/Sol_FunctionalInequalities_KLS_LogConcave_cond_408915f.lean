-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.cond_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:20:55.867997+00:00
-- url     : https://prove2.me/submissions/ae6bf4d3-67f8-4048-8e5e-6fc3006baada

import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.ConditionalProbability
import Mathlib.Topology.Maps.Proper.Basic

noncomputable section
open MeasureTheory Set Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
section Conditioning
open ProbabilityTheory
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
/-- **Conditioning on a closed convex set preserves log-concavity**: if `μ` is log-concave (in the
compact-set sense of `LogConcave`) and `C` is closed and convex with `μ C ≠ 0`, then the
conditional law `μ[|C]` is log-concave. Used to truncate isotropic log-concave laws to balls
(BKL arXiv:2610.05474v1, p. 19: Theorem 4.1 reduces to compactly supported laws). -/
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : ProbabilityMeasure E} (hμ : FunctionalInequalities.KLS.LogConcave μ)
    {C : Set E} (hC : Convex ℝ C) (hCc : IsClosed C) (hpos : (μ : Measure E) C ≠ 0) :
    FunctionalInequalities.KLS.LogConcave (⟨(μ : Measure E)[|C], cond_isProbabilityMeasure hpos⟩ : ProbabilityMeasure E) := by
  intro K₀ K₁ hK₀ hK₁ t ht₀ ht₁
  change
    ((μ : Measure E)[|C] K₀) ^ t * ((μ : Measure E)[|C] K₁) ^ (1 - t) ≤
      (μ : Measure E)[|C]
        {z | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t • x + (1 - t) • y}

  have hmain :
      (μ : Measure E) (K₀ ∩ C) ^ t * (μ : Measure E) (K₁ ∩ C) ^ (1 - t) ≤
        (μ : Measure E)
          {z | ∃ x ∈ K₀ ∩ C, ∃ y ∈ K₁ ∩ C,
            z = t • x + (1 - t) • y} :=
    hμ (K₀ ∩ C) (K₁ ∩ C) (hK₀.inter_right hCc) (hK₁.inter_right hCc) t ht₀ ht₁

  have hsubset :
      {z | ∃ x ∈ K₀ ∩ C, ∃ y ∈ K₁ ∩ C,
          z = t • x + (1 - t) • y} ⊆
        C ∩ {z | ∃ x ∈ K₀, ∃ y ∈ K₁,
          z = t • x + (1 - t) • y} := by
    intro z hz
    rcases hz with ⟨x, ⟨hx₀, hxC⟩, y, ⟨hy₀, hyC⟩, rfl⟩
    refine ⟨hC hxC hyC ht₀.le (sub_nonneg.mpr ht₁.le) (by ring), ?_⟩
    exact ⟨x, hx₀, y, hy₀, rfl⟩

  have hmono :
      (μ : Measure E)
          {z | ∃ x ∈ K₀ ∩ C, ∃ y ∈ K₁ ∩ C,
            z = t • x + (1 - t) • y} ≤
        (μ : Measure E)
          (C ∩ {z | ∃ x ∈ K₀, ∃ y ∈ K₁,
            z = t • x + (1 - t) • y}) :=
    measure_mono hsubset

  have hm_le_one : (μ : Measure E) C ≤ 1 := by
    calc
      (μ : Measure E) C ≤ (μ : Measure E) Set.univ :=
        measure_mono (Set.subset_univ C)
      _ = 1 := by simp

  have hm_top : (μ : Measure E) C ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hm_le_one (by simp))

  have hd₀ : ((μ : Measure E) C)⁻¹ ≠ 0 := by
    simp [hm_top]

  have hd_top : ((μ : Measure E) C)⁻¹ ≠ ⊤ := by
    simp [hpos]

  have hpow :
      ((μ : Measure E) C)⁻¹ ^ t * ((μ : Measure E) C)⁻¹ ^ (1 - t) =
        ((μ : Measure E) C)⁻¹ := by
    calc
      ((μ : Measure E) C)⁻¹ ^ t * ((μ : Measure E) C)⁻¹ ^ (1 - t) =
          ((μ : Measure E) C)⁻¹ ^ (t + (1 - t)) := by
            exact
              (ENNReal.rpow_add (x := ((μ : Measure E) C)⁻¹) t (1 - t) hd₀ hd_top).symm
      _ = ((μ : Measure E) C)⁻¹ := by
        rw [show t + (1 - t) = 1 by ring]
        simp

  have hfactor :
      (((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₀ ∩ C)) ^ t *
          (((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₁ ∩ C)) ^ (1 - t) =
        ((μ : Measure E) C)⁻¹ *
          ((μ : Measure E) (K₀ ∩ C) ^ t *
            (μ : Measure E) (K₁ ∩ C) ^ (1 - t)) := by
    calc
      (((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₀ ∩ C)) ^ t *
            (((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₁ ∩ C)) ^ (1 - t) =
          ((μ : Measure E) C)⁻¹ ^ t * (μ : Measure E) (K₀ ∩ C) ^ t *
            ((((μ : Measure E) C)⁻¹) ^ (1 - t) *
              (μ : Measure E) (K₁ ∩ C) ^ (1 - t)) := by
                rw [ENNReal.mul_rpow_of_nonneg
                      (x := ((μ : Measure E) C)⁻¹)
                      (y := (μ : Measure E) (K₀ ∩ C)) ht₀.le,
                  ENNReal.mul_rpow_of_nonneg
                      (x := ((μ : Measure E) C)⁻¹)
                      (y := (μ : Measure E) (K₁ ∩ C))
                      (sub_nonneg.mpr ht₁.le)]
      _ = ((μ : Measure E) C)⁻¹ ^ t *
            ((μ : Measure E) C)⁻¹ ^ (1 - t) *
              ((μ : Measure E) (K₀ ∩ C) ^ t *
                (μ : Measure E) (K₁ ∩ C) ^ (1 - t)) := by
                ac_rfl
      _ = ((μ : Measure E) C)⁻¹ *
          ((μ : Measure E) (K₀ ∩ C) ^ t *
            (μ : Measure E) (K₁ ∩ C) ^ (1 - t)) := by
              rw [hpow]

  have hcond₀ :
      (μ : Measure E)[|C] K₀ =
        ((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₀ ∩ C) := by
    calc
      (μ : Measure E)[|C] K₀ =
          ((μ : Measure E) C)⁻¹ * (μ : Measure E) (C ∩ K₀) :=
        cond_apply' hK₀.measurableSet (μ : Measure E)
      _ = ((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₀ ∩ C) := by
        rw [Set.inter_comm]

  have hcond₁ :
      (μ : Measure E)[|C] K₁ =
        ((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₁ ∩ C) := by
    calc
      (μ : Measure E)[|C] K₁ =
          ((μ : Measure E) C)⁻¹ * (μ : Measure E) (C ∩ K₁) :=
        cond_apply' hK₁.measurableSet (μ : Measure E)
      _ = ((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₁ ∩ C) := by
        rw [Set.inter_comm]

  have hcond₂ :
      (μ : Measure E)[|C]
          {z | ∃ x ∈ K₀, ∃ y ∈ K₁,
            z = t • x + (1 - t) • y} =
        ((μ : Measure E) C)⁻¹ *
          (μ : Measure E)
            (C ∩ {z | ∃ x ∈ K₀, ∃ y ∈ K₁,
              z = t • x + (1 - t) • y}) :=
    cond_apply hCc.measurableSet (μ : Measure E) _

  calc
    ((μ : Measure E)[|C] K₀) ^ t * ((μ : Measure E)[|C] K₁) ^ (1 - t) =
        (((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₀ ∩ C)) ^ t *
          (((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₁ ∩ C)) ^ (1 - t) := by
            rw [hcond₀, hcond₁]
    _ = ((μ : Measure E) C)⁻¹ *
          ((μ : Measure E) (K₀ ∩ C) ^ t *
            (μ : Measure E) (K₁ ∩ C) ^ (1 - t)) :=
      hfactor
    _ ≤ ((μ : Measure E) C)⁻¹ *
          (μ : Measure E)
            {z | ∃ x ∈ K₀ ∩ C, ∃ y ∈ K₁ ∩ C,
              z = t • x + (1 - t) • y} := by
      gcongr
    _ ≤ ((μ : Measure E) C)⁻¹ *
          (μ : Measure E)
            (C ∩ {z | ∃ x ∈ K₀, ∃ y ∈ K₁,
              z = t • x + (1 - t) • y}) := by
      gcongr
    _ = (μ : Measure E)[|C]
          {z | ∃ x ∈ K₀, ∃ y ∈ K₁,
            z = t • x + (1 - t) • y} :=
      hcond₂.symm
