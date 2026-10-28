-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.letwinCompactBound_of_regularClass_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:28:20.994607+00:00
-- url     : https://prove2.me/submissions/300c376f-835d-450a-ac5d-0171d97c75d9

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_LetwinApproximation
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_letwinQuadraticBound_of_tendsto_moments_readable
import Theorems.Thm_FunctionalInequalities_KLS_BorelLogConcave_exists_integrable_exp_norm_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_regularClass_seq_of_compact_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_logConcave_of_eq_regularClass_readable

section
noncomputable section
open MeasureTheory Set Topology Filter
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]
/-- **A log-concave law has norm moments of every order**: `‖x‖ ^ d` is integrable for every `d`, from the Borell
exponential moment. -/
theorem FunctionalInequalities.KLS.LogConcave.integrable_norm_pow {ν : ProbabilityMeasure E}
    (hν : KLS.LogConcave ν) (d : ℕ) : Integrable (fun x : E => ‖x‖ ^ d) (ν : Measure E) := by
  obtain ⟨r, hr, hi⟩ := ((KLS.LogConcave.borel_iff ν).1 hν).exists_integrable_exp_norm_readable
  exact Probability.integrable_norm_pow_of_integrable_exp_norm hr hi d
end FiniteDimensional
end
end

noncomputable section
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Analysis.BakryEmery
/-- **Reduction of the compact Letwin bound to Letwin's regular class** (Letwin arXiv:2607.24164v1, Lemma A.1): if every isotropic law `1_K e^{−W} dx` with `K` compact convex with nonempty interior and `W` smooth and
uniformly convex satisfies Letwin's quadratic bound, then so does every compactly supported isotropic log-concave law
in positive dimension (`LetwinCompactBound`). -/
theorem solution
    (h : ∀ (n : ℕ), 0 < n → ∀ (K : Set (EuclideanSpace ℝ (Fin n))) (W : EuclideanSpace ℝ (Fin n) → ℝ)
      (κ : ℝ), 0 < κ → IsCompact K → Convex ℝ K → (interior K).Nonempty → ContDiff ℝ ∞ W →
      ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) →
      ∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
        (μ : Measure (EuclideanSpace ℝ (Fin n))) =
          (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
            (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) →
        FunctionalInequalities.KLS.Isotropic μ → FunctionalInequalities.Analysis.BakryEmery.LetwinQuadraticBound (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    FunctionalInequalities.KLS.LogConcave.Suspension.LetwinCompactBound := by
  intro n hn μ hLC hiso hcompact
  have hmem (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hν : FunctionalInequalities.KLS.LogConcave ν) :
      MemLp id 4 (ν : Measure (EuclideanSpace ℝ (Fin n))) :=
    (integrable_norm_rpow_iff (p := 4) continuous_id.aestronglyMeasurable (by norm_num)
      (by norm_num)).mp (by simpa using hν.integrable_norm_pow 4)
  obtain ⟨ζ, hζ, hmom⟩ := FunctionalInequalities.KLS.LogConcave.exists_regularClass_seq_of_compact_readable μ hLC hiso hcompact
  have hζLC (j : ℕ) : FunctionalInequalities.KLS.LogConcave (ζ j) := by
    obtain ⟨-, K, W, κ, hκ, hK, hKc, -, hW, hWc, heq⟩ := hζ j
    exact FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_regularClass_readable (ζ j) hK.isClosed hKc hW.continuous hκ hWc heq
  refine FunctionalInequalities.Analysis.BakryEmery.letwinQuadraticBound_of_tendsto_moments_readable
    (fun j => (ζ j : Measure (EuclideanSpace ℝ (Fin n)))) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (fun j => hmem (ζ j) (hζLC j)) (hmem μ hLC) hmom fun j => ?_
  obtain ⟨hisoj, K, W, κ, hκ, hK, hKc, hKint, hW, hWc, heq⟩ := hζ j
  exact h n hn K W κ hκ hK hKc hKint hW hWc (ζ j) heq hisoj
