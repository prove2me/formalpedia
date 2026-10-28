-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.existsUnique_centered_adjointComp_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:26:21.298871+00:00
-- url     : https://prove2.me/submissions/a036418a-ae95-48d7-bbe5-1d7d86c782f8

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Inverse
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_eq_of_adjointComp_eq_readable
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_exists_adjointComp_eq_of_gap_readable
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
/-- **BKL Lemma 2.1, operator-domain part (existence and uniqueness).** If the literature Poincaré
constant of `ν` is at most `C`, then for every centered `g ∈ L²(ν)` there is exactly one centered
`u` in the domain of the generator `A = T̄†T̄` with `A u = g` (`A = -ℒ`). -/
theorem solution {C : NNReal}
    (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    (g : Lp ℝ 2 (ν : Measure V)) (hg : FunctionalInequalities.L2.mean ν g = 0) :
    ∃! u : (FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      FunctionalInequalities.L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0 ∧
        FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u = g := by
    let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    have hT : T.IsClosed := by
      simpa [T] using hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
    have hd : Dense (T.domain : Set (Lp ℝ 2 (ν : Measure V))) := by
      simpa [T] using
        hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    have hgap :
        ∀ y : T.domain,
          (∀ k : T.domain, T k = 0 → ⟪(y : Lp ℝ 2 (ν : Measure V)), (k : Lp ℝ 2 (ν : Measure V))⟫ = 0) →
            ‖(y : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
              (C : ℝ) * ‖T y‖ ^ 2 := by
      intro y hy
      have hmy :
          FunctionalInequalities.L2.mean ν (y : Lp ℝ 2 (ν : Measure V)) = 0 :=
        (FunctionalInequalities.KLS.LogConcave.orthogonal_ker_iff_mean_eq_zero_readable m hν hi hνU hU (y : Lp ℝ 2 (ν : Measure V))).mp
          (by simpa [T] using hy)
      have h :=
        hν.closedWeightedOperator_id_gap_of_literature_le_readable m hi (C : NNReal) hC y
      simpa [T, FunctionalInequalities.L2.center, hmy] using h
    have hgorth :
        ∀ k : T.domain, T k = 0 →
          ⟪g, (k : Lp ℝ 2 (ν : Measure V))⟫ = 0 := by
      have h :=
        (FunctionalInequalities.KLS.LogConcave.orthogonal_ker_iff_mean_eq_zero_readable m hν hi hνU hU g).mpr hg
      simpa [T] using h
    obtain ⟨u, huorth, hueq⟩ :=
      FunctionalInequalities.Analysis.Semigroup.Generated.exists_adjointComp_eq_of_gap_readable T hT hd hgap g hgorth
    refine ⟨u, ?_, ?_⟩
    · constructor
      · exact
          (FunctionalInequalities.KLS.LogConcave.orthogonal_ker_iff_mean_eq_zero_readable m hν hi hνU hU
            (u : Lp ℝ 2 (ν : Measure V))).mp (by simpa [T] using huorth)
      · simpa [T] using hueq
    · intro v hv
      have hvorth :
          ∀ k : T.domain, T k = 0 →
            ⟪(v : Lp ℝ 2 (ν : Measure V)), (k : Lp ℝ 2 (ν : Measure V))⟫ = 0 := by
        have h :=
          (FunctionalInequalities.KLS.LogConcave.orthogonal_ker_iff_mean_eq_zero_readable m hν hi hνU hU
            (v : Lp ℝ 2 (ν : Measure V))).mpr hv.1
        simpa [T] using h
      have hEq : FunctionalInequalities.Analysis.Semigroup.adjointComp T v = FunctionalInequalities.Analysis.Semigroup.adjointComp T u := by
        calc
          FunctionalInequalities.Analysis.Semigroup.adjointComp T v =
              g := by simpa [T] using hv.2
          _ = FunctionalInequalities.Analysis.Semigroup.adjointComp T u := hueq.symm
      have hvu :
          (v : Lp ℝ 2 (ν : Measure V)) = (u : Lp ℝ 2 (ν : Measure V)) :=
        FunctionalInequalities.Analysis.Semigroup.Generated.eq_of_adjointComp_eq_readable T hd v u hvorth huorth hEq
      exact Subtype.ext hvu
