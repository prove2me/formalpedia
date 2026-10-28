-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.centered_adjointComp_bounds_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:26:20.223466+00:00
-- url     : https://prove2.me/submissions/a7f74a67-0a18-461b-a3b1-9e723d00b145

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Inverse
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_norm_le_of_gap_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_id_gap_of_literature_le_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_orthogonal_ker_iff_mean_eq_zero_readable

section
noncomputable section
open MeasureTheory
section
variable {α : Type*} [MeasurableSpace α]
/-- The zero constant is the zero element of `L²`. -/
@[simp]
theorem FunctionalInequalities.L2.const_zero (μ : ProbabilityMeasure α) : const μ 0 = 0 :=
  map_zero (Lp.const 2 (μ : Measure α))
end
end
end

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.Semigroup.Generated
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU in
/-- **BKL Lemma 2.1, operator-domain part (bounds (20) and (24)).** With `C ≥ C_P(ν) = λ⁻¹`, a
centered `u` in the generator domain with `A u = g` satisfies `‖u‖ ≤ C ‖g‖`,
`‖T̄ u‖² = ⟪g, u⟫ ≤ C ‖g‖²` and `‖T̄ u‖ ≤ √C ‖g‖`. -/
theorem solution {C : NNReal}
    (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    (u : (FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hu : FunctionalInequalities.L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0) :
    ‖(u : Lp ℝ 2 (ν : Measure V))‖ ≤
        (C : ℝ) * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ ∧
      ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ ^ 2 =
        ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u,
          (u : Lp ℝ 2 (ν : Measure V))⟫ ∧
      ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u,
          (u : Lp ℝ 2 (ν : Measure V))⟫ ≤
        (C : ℝ) * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ ^ 2 ∧
      ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ ≤
        Real.sqrt C * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ := by
    have hd :
        Dense
          ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain :
            Set (Lp ℝ 2 (ν : Measure V))) :=
      hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    have hgap :
        ∀ y : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
          (∀ k : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
              hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi k = 0 →
                ⟪(y : Lp ℝ 2 (ν : Measure V)),
                  (k : Lp ℝ 2 (ν : Measure V))⟫ = 0) →
            ‖(y : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
              (C : ℝ) *
                ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi y‖ ^ 2 := by
      intro y hy
      have hymean :
          FunctionalInequalities.L2.mean ν (y : Lp ℝ 2 (ν : Measure V)) = 0 :=
        (FunctionalInequalities.KLS.LogConcave.orthogonal_ker_iff_mean_eq_zero_readable m hν hi hνU hU
          (y : Lp ℝ 2 (ν : Measure V))).mp hy
      have hcenter :
          FunctionalInequalities.L2.center ν (y : Lp ℝ 2 (ν : Measure V)) =
            (y : Lp ℝ 2 (ν : Measure V)) := by
        simp [FunctionalInequalities.L2.center, hymean]
      have h :=
        hν.closedWeightedOperator_id_gap_of_literature_le_readable m hi C hC y
      rw [hcenter] at h
      exact h
    have huorth :
        ∀ k : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
          hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi k = 0 →
            ⟪(u : Lp ℝ 2 (ν : Measure V)),
              (k : Lp ℝ 2 (ν : Measure V))⟫ = 0 :=
      (FunctionalInequalities.KLS.LogConcave.orthogonal_ker_iff_mean_eq_zero_readable m hν hi hνU hU
        (u : Lp ℝ 2 (ν : Measure V))).mpr hu
    obtain ⟨hu₁, hu₂, hu₃⟩ :=
      FunctionalInequalities.Analysis.Semigroup.Generated.norm_le_of_gap_readable
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) hd hgap u huorth
    refine ⟨hu₁, hu₂, hu₃, ?_⟩
    have hsq :
        ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ ^ 2 ≤
          (C : ℝ) *
            ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ ^ 2 := by
      rw [hu₂]
      exact hu₃
    have hsqrt :
        (Real.sqrt (C : ℝ)) ^ 2 = (C : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    have hsqrt_nonneg : 0 ≤ Real.sqrt (C : ℝ) :=
      Real.sqrt_nonneg _
    have hnorm₁ :
        0 ≤
          ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ :=
      norm_nonneg _
    have hnorm₂ :
        0 ≤
          ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ :=
      norm_nonneg _
    by_contra hnot
    have hlt :
        Real.sqrt (C : ℝ) *
            ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ <
          ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ :=
      lt_of_not_ge hnot
    have hprod :
        0 ≤
          Real.sqrt (C : ℝ) *
            ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ :=
      mul_nonneg hsqrt_nonneg hnorm₂
    have hsum :
        0 <
          ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ +
            Real.sqrt (C : ℝ) *
              ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
                (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ := by
      linarith
    have hfac :
        0 <
          (‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ -
            Real.sqrt (C : ℝ) *
              ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
                (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖) *
          (‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ +
            Real.sqrt (C : ℝ) *
              ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
                (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖) :=
      mul_pos (sub_pos.mpr hlt) hsum
    have hsq' :
        (Real.sqrt (C : ℝ) *
            ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖) ^ 2 =
          (C : ℝ) *
            ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ ^ 2 := by
      rw [mul_pow, hsqrt]
    nlinarith [hfac, hsq, hsq']
