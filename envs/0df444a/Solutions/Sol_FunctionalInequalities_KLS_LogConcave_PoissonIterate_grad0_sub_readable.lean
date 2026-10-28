-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0_sub_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:42:17.407089+00:00
-- url     : https://prove2.me/submissions/8f2cdc71-0118-46ee-9b1b-db783df6c3ec

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Domain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Symmetry

section
noncomputable section
open MeasureTheory
section
variable {α : Type*} [MeasurableSpace α]
/-- Embedding constants into `L²` preserves addition. -/
@[simp]
theorem FunctionalInequalities.L2.const_add (μ : ProbabilityMeasure α) (c d : ℝ) :
    const μ (c + d) = const μ c + const μ d :=
  map_add (Lp.const 2 (μ : Measure α)) c d
/-- The mean preserves addition. -/
@[simp]
theorem FunctionalInequalities.L2.mean_add (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    mean μ (f + g) = mean μ f + mean μ g := by
  rw [mean, inner_add_left]
  rfl
/-- The mean preserves real scalar multiplication. -/
@[simp]
theorem FunctionalInequalities.L2.mean_smul (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (c • f) = c * mean μ f := by
  rw [mean, inner_smul_left]
  rfl
/-- Centering preserves addition. -/
@[simp]
theorem FunctionalInequalities.L2.center_add (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    center μ (f + g) = center μ f + center μ g := by
  simp only [center, mean_add, const_add]
  abel
/-- Centering commutes with real scalar multiplication. -/
@[simp]
theorem FunctionalInequalities.L2.center_smul (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ (c • f) = c • center μ f := by
  simp only [center, mean_smul, const_smul, smul_sub]
end
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace
section General
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
variable {ν : MeasureTheory.ProbabilityMeasure V} (T : MeasureTheory.Lp ℝ 2 (ν : MeasureTheory.Measure V) →ₗ.[ℝ] MeasureTheory.Lp V 2 (ν : MeasureTheory.Measure V))
/-- The total gradient agrees with `T` on its domain. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_of_mem {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ T.domain) :
    weakGrad T u = T ⟨u, hu⟩ :=
  dif_pos hu
variable [FiniteDimensional ℝ V]
end General
end
end

noncomputable section
open MeasureTheory Finset
open FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace
section General
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
  (T : MeasureTheory.Lp ℝ 2 (ν : MeasureTheory.Measure V) →ₗ.[ℝ] MeasureTheory.Lp V 2 (ν : MeasureTheory.Measure V))
/-- `∇₀` is additive on fields with components in `D(T)`. -/
theorem solution {k : ℕ} {u v : FunctionalInequalities.KLS.LogConcave.PoissonIterate.Field ν k} (hu : ∀ I, u I ∈ T.domain)
    (hv : ∀ I, v I ∈ T.domain) : FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T (u - v) = FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T v := by
  funext J
  have hw : FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad T (u (Fin.tail J) - v (Fin.tail J)) =
      FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad T (u (Fin.tail J)) - FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad T (v (Fin.tail J)) := by
    rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_of_mem T (T.domain.sub_mem (hu _) (hv _)), FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_of_mem T (hu _),
      FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_of_mem T (hv _)]
    exact LinearPMap.map_sub T ⟨_, hu _⟩ ⟨_, hv _⟩
  have hL : ∀ (L : V →L[ℝ] ℝ) (a b : Lp V 2 (ν : Measure V)),
      L.compLp (a - b) = L.compLp a - L.compLp b :=
    fun L a b => (L.compLpₗ 2 (ν : Measure V)).map_sub a b
  simp only [FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0, FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField, FunctionalInequalities.KLS.LogConcave.PoissonIterate.partialDeriv, Pi.sub_apply, hw, hL]
  rw [sub_eq_add_neg, FunctionalInequalities.L2.center_add, ← neg_one_smul ℝ, FunctionalInequalities.L2.center_smul, neg_one_smul,
    ← sub_eq_add_neg]
