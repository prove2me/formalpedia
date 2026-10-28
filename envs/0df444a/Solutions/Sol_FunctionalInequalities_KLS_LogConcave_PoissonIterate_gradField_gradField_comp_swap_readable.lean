-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField_gradField_comp_swap_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:25:51.651906+00:00
-- url     : https://prove2.me/submissions/4a08fd5c-a2af-44f0-a995-c6aabef3d3a8

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Domain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Hessian
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Defect
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_compLp_innerSL_closedWeightedOperator_comm_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_convexOn_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_seq_smooth_tendsto_weakHessian_readable

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

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
section
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
section Hessian
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
omit [CompleteSpace V] in
include hν in
/-- The curvature bound `∇²U ≥ 0` of a log-concave tilted law with a `C²` potential. -/
private theorem FunctionalInequalities.KLS.LogConcave.zero_mul_le_bilinearIteratedFDerivTwo (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 2 U) (x v : V) :
    0 * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v := by
  rw [zero_mul]
  exact bilinearIteratedFDerivTwo_nonneg_of_convexOn hU
    (convexOn_of_eq_tilted_readable m hν hνU hU.continuous) x v
/-- **the weak Hessian estimate, weak first derivatives in the form domain.** For `ν = m.tilted (-U)` log-concave,
with `U` of temperate growth and all exponential moments, and `F ∈ D(A)`, every weak first
derivative `∂ᵢ F = ⟪eᵢ, T̄ F⟫` (standard orthonormal basis) lies in `D(T̄)`. No curvature bound
beyond the convexity of `U` implied by log-concavity is assumed. -/
theorem FunctionalInequalities.KLS.LogConcave.compLp_innerSL_mem_closedWeightedOperator_domain
    (hνU : (ν : Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (i : Fin (Module.finrank ℝ V)) :
    (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := by
  have hU2 : ContDiff ℝ 2 U := hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨_, _, _, -, -, hD⟩ := exists_seq_smooth_tendsto_weakHessian_readable m hν hi hνU hUt
    (hU2.of_le (by norm_num)) hexp (zero_mul_le_bilinearIteratedFDerivTwo m hν hνU hU2) F
  exact (hD i).1
end Hessian
end
end
end

noncomputable section
open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
  (hexp : ∀ r : ℝ, MeasureTheory.Integrable (fun x => Real.exp (r * ‖x‖)) (ν : MeasureTheory.Measure V))
  {C : NNReal} (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
/-- A weak partial derivative on `D(T̄)` in terms of `T̄`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.partialDeriv_eq {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (T̄).domain)
    (j : Fin (Module.finrank ℝ V)) :
    partialDeriv T̄ j u = (innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLp (T̄ ⟨u, hu⟩) := by
  rw [partialDeriv, weakGrad_of_mem _ hu]
include hνU hUt hexp in
/-- **Symmetry of the weak Hessian**: for `u ∈ D(A)`, `∂_i ∂_j u = ∂_j ∂_i u`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.partialDeriv_comm {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T̄).domain)
    (i j : Fin (Module.finrank ℝ V)) :
    partialDeriv T̄ i (partialDeriv T̄ j u) = partialDeriv T̄ j (partialDeriv T̄ i u) := by
  have hD : ∀ l, (innerSL ℝ (stdOrthonormalBasis ℝ V l)).compLp (T̄ ⟨u, hu.2⟩) ∈ (T̄).domain :=
    compLp_innerSL_mem_closedWeightedOperator_domain m hν hi hνU hUt hexp ⟨u, hu⟩
  have hc : (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp (T̄ ⟨_, hD j⟩) =
      (innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLp (T̄ ⟨_, hD i⟩) :=
    compLp_innerSL_closedWeightedOperator_comm_readable m hν hi hνU hUt hexp ⟨u, hu⟩ hD j i
  rw [partialDeriv_eq m hν hi hu.2 j, partialDeriv_eq m hν hi hu.2 i,
    partialDeriv_eq m hν hi (hD j), partialDeriv_eq m hν hi (hD i)]
  exact hc
include hνU hUt hexp in
/-- The weak Hessian of a field with components in `D(A)` is symmetric in its first two index
positions: `∂_{J₀} ∂_{J₁} h_I = ∂_{J₁} ∂_{J₀} h_I`. -/
theorem solution {k : ℕ} (h : FunctionalInequalities.KLS.LogConcave.PoissonIterate.Field ν k)
    (hh : ∀ I, h I ∈ (FunctionalInequalities.Analysis.Semigroup.adjointComp T̄).domain)
    (J : Fin (k + 2) → Fin (Module.finrank ℝ V)) :
    FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ h) (J ∘ Equiv.swap 0 1) = FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ h) J := by
  have ht : Fin.tail (Fin.tail (J ∘ Equiv.swap 0 1)) = Fin.tail (Fin.tail J) := by
    funext i
    simp only [Fin.tail, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)]
    intro h1
    rw [← Fin.succ_zero_eq_one] at h1
    exact Fin.succ_ne_zero _ (Fin.succ_injective _ h1)
  simp only [FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField]
  rw [ht]
  simp only [Fin.tail, Function.comp_apply, Equiv.swap_apply_left, Fin.succ_zero_eq_one,
    Equiv.swap_apply_right]
  exact FunctionalInequalities.KLS.LogConcave.PoissonIterate.partialDeriv_comm m hν hi hνU hUt hexp (hh _) _ _
