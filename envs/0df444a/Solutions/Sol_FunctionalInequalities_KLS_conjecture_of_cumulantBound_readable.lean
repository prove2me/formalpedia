-- Prove2me | solution 1 for FunctionalInequalities.KLS.conjecture_of_cumulantBound_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:48:36.844401+00:00
-- url     : https://prove2.me/submissions/f4d7940b-12e7-459d-a53f-5d8e107abf4d

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Reduction
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_isotropic_localSlope_constant_eq_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_localSlope_le_mul_intrinsicCovariance_readable
import Theorems.Thm_FunctionalInequalities_KLS_localSlope_le_of_cumulantBound_all_readable

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
open FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean FunctionalInequalities.Probability
section Statements
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
section
/-- (1) ⇒ (3). -/
theorem FunctionalInequalities.KLS.affineBound_of_isotropicBound {K : NNReal} (h : IsotropicBound.{u} K) : AffineBound.{u} K := by
  intro E _ _ _ _ _ _ _ μ hμ
  obtain ⟨ν', hν', hiso, heq⟩ := hμ.exists_isotropic_localSlope_constant_eq_readable
  rw [heq]
  exact h _ ν' hν' hiso
/-- (3) ⇒ (2). -/
theorem FunctionalInequalities.KLS.covarianceBound_of_affineBound {K : NNReal} (h : AffineBound.{u} K) : CovarianceBound.{u} K := by
  intro E _ _ _ _ _ _ _ μ hμ
  exact hμ.localSlope_le_mul_intrinsicCovariance_readable (h E μ hμ)
/-- Item (3) for some finite `K` implies the literal KLS proposition on the Euclidean family. -/
theorem FunctionalInequalities.KLS.conjecture_of_affineBound {K : NNReal} (h : AffineBound.{0} K) : Conjecture :=
  ⟨K, fun n μ hμ _ ↦ covarianceBound_of_affineBound h (EuclideanSpace ℝ (Fin n)) μ hμ⟩
end
end Statements
end
end
end

open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped RealInnerProductSpace
universe u
/-- The conditional implication to the project's `KLS.Conjecture`: the universal cumulant bounds of
Theorem 4.1 (an explicit hypothesis `hSource`) imply the dimension-free KLS bound. `KLS.kls`
(`KLS/Target.lean`) is proved through the closed producer `BKL.Localization.conjecture`. -/
theorem solution
    (hSource : ∃ K : ℝ, 1 ≤ K ∧
      ∀ d : ℕ, 2 ≤ d → FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBound d ((d.factorial : ℝ) ^ 2 * K ^ d)) :
    FunctionalInequalities.KLS.Conjecture := by
  obtain ⟨C, hC, hAll⟩ := FunctionalInequalities.KLS.localSlope_le_of_cumulantBound_all_readable.{0}
  obtain ⟨K, hK, hcb⟩ := hSource
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let B : NNReal := ⟨2 * C * K, by positivity⟩
  have hB : (B : ENNReal) = ENNReal.ofReal (2 * C * K) :=
    ENNReal.ofReal_coe_nnreal.symm
  have hIB : FunctionalInequalities.KLS.IsotropicBound.{0} B := by
    intro E _ _ _ _ _ _ _ μ hLC hiso
    rw [hB]
    exact hAll K hK hcb E μ hLC hiso
  exact FunctionalInequalities.KLS.conjecture_of_affineBound (FunctionalInequalities.KLS.affineBound_of_isotropicBound hIB)
