-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_mean_partialDeriv_sq_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:37.299275+00:00
-- url     : https://prove2.me/submissions/313929af-c5a1-4634-b790-33055f89af7a

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Domain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth_readable

section
noncomputable section
open MeasureTheory
section
variable {α : Type*} [MeasurableSpace α]
/-- The Hilbert-space mean agrees with the integral of any representative supplied by `Lp`. -/
theorem FunctionalInequalities.L2.mean_eq_integral (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ f = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [const_coeFn μ 1] with x hx
  simp [hx]
end
section NormSquare
variable {V : Type*} [MeasurableSpace V]
/-- The `L²` norm squared of a square-integrable function is the integral of its squared norm. -/
theorem FunctionalInequalities.L2.norm_toLp_sq {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {μ : Measure V} {u : V → W} (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
end NormSquare
end
end

section
noncomputable section
open scoped LinearPMap
section
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
/-- Points of the domain of `T†T` are points of the domain of `T`. -/
theorem FunctionalInequalities.Analysis.Semigroup.mem_domain_of_mem_adjointComp_domain (T : H₀ →ₗ.[ℝ] H₁) (x : (adjointComp T).domain) :
    (x : H₀) ∈ T.domain :=
  x.2.2
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
/-- The total generator agrees with `T†T` on its domain. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_of_mem {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T).domain) :
    gen T u = adjointComp T ⟨u, hu⟩ :=
  dif_pos hu
variable [FiniteDimensional ℝ V]
end General
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  (hexp : ∀ r : ℝ, MeasureTheory.Integrable (fun x => Real.exp (r * ‖x‖)) (ν : MeasureTheory.Measure V))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
variable {C : NNReal} (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
omit [SecondCountableTopology V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradient_inner_right' (w x : V) : gradient (fun y : V => ⟪w, y⟫) x = w := by
  have hd : fderiv ℝ (fun y : V => ⟪w, y⟫) x = InnerProductSpace.toDual ℝ V w := by
    change fderiv ℝ (⇑(innerSL ℝ w)) x = _
    rw [((innerSL ℝ w).hasFDerivAt (x := x)).fderiv]
    ext y
    simp
  simp only [gradient, hd, LinearIsometryEquiv.symm_apply_apply]
include hexp in
/-- **The first energy drop of BKL Lemma 3.9** on the generator domain: if
`∫ ⟪v, x⟫² dν ≤ ‖v‖²` for every `v` (`Cov ν ≤ Id` for a centered law), then for `u ∈ D(A)`,
`|∫ ∇u|² = Σ_j (∫ ∂_j u)² ≤ ‖A u‖²`. With `w = ∫ ∇u`, `|w|² = ⟪∇u, ∇⟪w, ·⟫⟫ = ⟪A u, ⟪w, ·⟫⟫`
and `‖⟪w, ·⟫‖ ≤ |w|`. -/
theorem solution
    (hcov : ∀ v : V, ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure V) ≤ ‖v‖ ^ 2)
    {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (FunctionalInequalities.Analysis.Semigroup.adjointComp T̄).domain) :
    ∑ j, FunctionalInequalities.L2.mean ν (FunctionalInequalities.KLS.LogConcave.PoissonIterate.partialDeriv T̄ j u) ^ 2 ≤ ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen T̄ u‖ ^ 2 := by
  set b := stdOrthonormalBasis ℝ V
  have huT : u ∈ (T̄).domain := FunctionalInequalities.Analysis.Semigroup.mem_domain_of_mem_adjointComp_domain _ ⟨u, hu⟩
  set G := (T̄) ⟨u, huT⟩ with hG
  set w : V := ∫ x, G x ∂(ν : Measure V)
  have hGi : Integrable (⇑G) (ν : Measure V) := (Lp.memLp G).integrable (by norm_num)
  have hmean : ∀ j, FunctionalInequalities.L2.mean ν (FunctionalInequalities.KLS.LogConcave.PoissonIterate.partialDeriv T̄ j u) = ⟪b j, w⟫ := by
    intro j
    rw [FunctionalInequalities.L2.mean_eq_integral, FunctionalInequalities.KLS.LogConcave.PoissonIterate.partialDeriv, FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_of_mem _ huT, ← integral_inner hGi]
    exact integral_congr_ae ((innerSL ℝ (b j)).coeFn_compLp _)
  have hsum : ∑ j, FunctionalInequalities.L2.mean ν (FunctionalInequalities.KLS.LogConcave.PoissonIterate.partialDeriv T̄ j u) ^ 2 = ‖w‖ ^ 2 := by
    simp_rw [hmean]
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner w w]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm w (b j), sq]
  obtain ⟨hℓ2, hg2, hmem, hT⟩ :=
    FunctionalInequalities.KLS.LogConcave.exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth_readable m hν hi hexp
      (Function.hasTemperateGrowth_inner_right w)
  have hinner : ⟪FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen T̄ u, hℓ2.toLp _⟫ = ‖w‖ ^ 2 := by
    rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_of_mem _ hu, FunctionalInequalities.Analysis.Semigroup.inner_adjointComp
      (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ⟨u, hu⟩ hmem, hT,
      MeasureTheory.L2.inner_def, ← real_inner_self_eq_norm_sq]
    calc ∫ x, ⟪G x, hg2.toLp (gradient fun y : V => ⟪w, y⟫) x⟫ ∂(ν : Measure V) =
          ∫ x, ⟪w, G x⟫ ∂(ν : Measure V) := by
          refine integral_congr_ae ?_
          filter_upwards [hg2.coeFn_toLp] with x hx
          rw [hx, FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradient_inner_right', real_inner_comm]
      _ = ⟪w, w⟫ := integral_inner hGi w
  have hℓ : ‖hℓ2.toLp (fun y : V => ⟪w, y⟫)‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [FunctionalInequalities.L2.norm_toLp_sq]
    simpa only [Real.norm_eq_abs, sq_abs] using hcov w
  have hCS := real_inner_le_norm (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen T̄ u) (hℓ2.toLp (fun y : V => ⟪w, y⟫))
  rw [hinner] at hCS
  rw [hsum]
  have h0 : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  have h4 : (‖w‖ ^ 2) ^ 2 ≤ ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen T̄ u‖ ^ 2 * ‖w‖ ^ 2 := by
    calc (‖w‖ ^ 2) ^ 2 ≤ (‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen T̄ u‖ * ‖hℓ2.toLp (fun y : V => ⟪w, y⟫)‖) ^ 2 :=
          pow_le_pow_left₀ h0 hCS 2
      _ = ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen T̄ u‖ ^ 2 * ‖hℓ2.toLp (fun y : V => ⟪w, y⟫)‖ ^ 2 := by ring
      _ ≤ ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen T̄ u‖ ^ 2 * ‖w‖ ^ 2 := by gcongr
  nlinarith [sq_nonneg (‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen T̄ u‖)]
