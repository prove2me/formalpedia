-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_taylorField_grad0_step_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:28:14.913919+00:00
-- url     : https://prove2.me/submissions/82c9c37d-806f-4f52-acb7-02e6c60e710d

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Domain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_const_mul_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_symmetrize_apply_comp_cast_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_taylorTensor_center_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_taylorTensor_gen_apply_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_existsUnique_centered_adjointComp_eq_readable

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section Lp
section ScalarLp
omit [CompleteSpace E] [FiniteDimensional ℝ E]
section NormedSpace
variable {G : Type*}
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
section CompleteSpace
variable [CompleteSpace G]
omit [BorelSpace E] in
/-- Tilt averages only see the `μ`-class of a function: every tilt `μ_z` is absolutely
continuous with respect to `μ`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.tiltAverage_congr_ae (μ : Measure E) {f g : E → G} (hfg : f =ᵐ[μ] g) (z : E) :
    tiltAverage μ f z = tiltAverage μ g z := by
  unfold tiltAverage expTilt
  exact integral_congr_ae ((tilted_absolutelyContinuous μ _).ae_le hfg)
omit [BorelSpace E] in
/-- Taylor tensors only see the `μ`-class of a function. -/
theorem FunctionalInequalities.Analysis.BakryEmery.taylorTensor_congr_ae (μ : Measure E) {f g : E → G} (hfg : f =ᵐ[μ] g) (d : ℕ) :
    taylorTensor μ f d = taylorTensor μ g d := by
  unfold taylorTensor
  rw [show tiltAverage μ f = tiltAverage μ g from funext (tiltAverage_congr_ae μ hfg)]
end CompleteSpace
end NormedSpace
end ScalarLp
end Lp
end
end
end

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
/-- Probability normalization makes the mean of a constant equal to that constant. -/
@[simp]
theorem FunctionalInequalities.L2.mean_const (μ : ProbabilityMeasure α) (c : ℝ) : mean μ (const μ c) = c := by
  rw [mean_eq_integral]
  calc
    (∫ x, const μ c x ∂(μ : Measure α)) = ∫ _ : α, c ∂(μ : Measure α) :=
      integral_congr_ae (const_coeFn μ c)
    _ = c := by simp
/-- The mean preserves subtraction. -/
@[simp]
theorem FunctionalInequalities.L2.mean_sub (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    mean μ (f - g) = mean μ f - mean μ g := by
  rw [mean, inner_sub_left]
  rfl
/-- A centered `L²` element has mean zero. -/
@[simp]
theorem FunctionalInequalities.L2.mean_center (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (center μ f) = 0 := by
  simp [center]
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
/-- The total generator agrees with `T†T` on its domain. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_of_mem {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T).domain) :
    gen T u = adjointComp T ⟨u, hu⟩ :=
  dif_pos hu
/-- The total generator is homogeneous on the domain of `T†T`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_smul (c : ℝ) {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T).domain) :
    gen T (c • u) = c • gen T u := by
  rw [gen_of_mem T ((adjointComp T).domain.smul_mem c hu), gen_of_mem T hu]
  exact LinearPMap.map_smul (adjointComp T) c ⟨u, hu⟩
/-- If a centered preimage of `g` under `T†T` exists, the centered inverse is one. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.centeredInv_spec_of_exists {g : Lp ℝ 2 (ν : Measure V)}
    (h : ∃ u : (adjointComp T).domain,
      L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0 ∧ adjointComp T u = g) :
    ∃ hu : centeredInv T g ∈ (adjointComp T).domain, adjointComp T ⟨_, hu⟩ = g := by
  have hc : centeredInv T g = (h.choose : Lp ℝ 2 (ν : Measure V)) := by
    unfold centeredInv
    rw [dif_pos h]
  rw [hc]
  exact ⟨h.choose.2, h.choose_spec.2⟩
variable [FiniteDimensional ℝ V]
/-- The components of `∇₀h` are centered. -/
@[simp]
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.mean_grad0 {k : ℕ} (h : Field ν k) (J : Fin (k + 1) → Fin (Module.finrank ℝ V)) :
    L2.mean ν (grad0 T h J) = 0 :=
  L2.mean_center ν _
end General
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  {C : NNReal} (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
include hνU hU hC in
/-- **BKL Lemma 2.1 for the total centered inverse.** For centered `g`, `centeredInv T̄ g` lies in
`D(A)` and solves `A u = g`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.centeredInv_spec {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    ∃ hu : centeredInv T̄ g ∈ (adjointComp T̄).domain, adjointComp T̄ ⟨_, hu⟩ = g :=
  centeredInv_spec_of_exists _
    (existsUnique_centered_adjointComp_eq_readable m hν hi hνU hU hC g hg).exists
include hνU hU hC in
/-- For centered `g`, `(-L)⁻¹ g ∈ D(A)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.centeredInv_mem_domain {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    centeredInv T̄ g ∈ (adjointComp T̄).domain :=
  (centeredInv_spec m hν hi hνU hU hC hg).1
include hνU hU hC in
/-- For centered `g`, `-L (-L)⁻¹ g = g`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_centeredInv {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    gen T̄ (centeredInv T̄ g) = g := by
  obtain ⟨hu, hAu⟩ := centeredInv_spec m hν hi hνU hU hC hg
  rw [gen_of_mem _ hu, hAu]
include hνU hU hC in
/-- The components of one step lie in `D(A)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.step_mem_domain {k : ℕ} (h : Field ν k) (J : Fin (k + 1) → Fin (Module.finrank ℝ V)) :
    step T̄ h J ∈ (adjointComp T̄).domain :=
  (adjointComp T̄).domain.smul_mem _
    (centeredInv_mem_domain m hν hi hνU hU hC (mean_grad0 (T̄) h J))
include hνU hU hC in
/-- **BKL (30)** for one step: `-L (α (-L)⁻¹ ∇₀h) = α ∇₀h`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.genField_step {k : ℕ} (h : Field ν k) :
    genField T̄ (step T̄ h) = scale T̄ h • grad0 T̄ h := by
  funext J
  rw [genField, step, Pi.smul_apply, Pi.smul_apply, invField,
    gen_smul _ _ (centeredInv_mem_domain m hν hi hνU hU hC (mean_grad0 (T̄) h J)),
    gen_centeredInv m hν hi hνU hU hC (mean_grad0 (T̄) h J)]
end HeatModel
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
section Generic
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- `T_d` is homogeneous on `L²(ν)` classes. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_Lp_smul (c : ℝ) (u : Lp ℝ 2 (ν : Measure V)) (d : ℕ) :
    taylorTensor (ν : Measure V) (⇑(c • u)) d = c • taylorTensor (ν : Measure V) (⇑u) d := by
  rw [taylorTensor_congr_ae _ (Lp.coeFn_smul c u) d]
  exact taylorTensor_const_mul_readable _ c _ d
end Generic
section Slots
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.append_cast_natAdd {α : Type*} {d k : ℕ} (h : d + (k + 2) = d + 1 + (k + 1))
    (a : Fin (d + 1) → α) (I : Fin (k + 1) → α) :
    (fun p : Fin (k + 2) => Fin.append a I (Fin.cast h (Fin.natAdd d p))) =
      Fin.cons (a (Fin.last d)) I := by
  funext p
  induction p using Fin.cases with
  | zero =>
    rw [show Fin.cast h (Fin.natAdd d 0) = Fin.castAdd (k + 1) (Fin.last d) from Fin.ext (by simp),
      Fin.append_left, Fin.cons_zero]
  | succ p =>
    rw [show Fin.cast h (Fin.natAdd d p.succ) = Fin.natAdd (d + 1) p from
      Fin.ext (by simp; omega), Fin.append_right, Fin.cons_succ]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.append_cast_castAdd {α : Type*} {d k : ℕ} (h : d + (k + 2) = d + 1 + (k + 1))
    (a : Fin (d + 1) → α) (I : Fin (k + 1) → α) (p : Fin d) :
    Fin.append a I (Fin.cast h (Fin.castAdd (k + 2) p)) = a (Fin.castSucc p) := by
  rw [show Fin.cast h (Fin.castAdd (k + 2) p) = Fin.castAdd (k + 1) (Fin.castSucc p) from
    Fin.ext (by simp), Fin.append_left]
end Slots
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  (hexp : ∀ r : ℝ, MeasureTheory.Integrable (fun x => Real.exp (r * ‖x‖)) (ν : MeasureTheory.Measure V))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
variable {C : NNReal} (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
include hνU hU hexp hC in
/-- **BKL Corollary 3.7 for one step**: for `d ≥ 1` and `h' = α (-L)⁻¹∇₀h`,
`S_{d+1} T_d(∇₀h') = α T_{d+1}(∇₀h)`, the index positions of the two coefficient arrays identified
by `Fin.cast`. -/
theorem solution {k : ℕ} (h : FunctionalInequalities.KLS.LogConcave.PoissonIterate.Field ν k) {d : ℕ} (hd : 1 ≤ d)
    (J : Fin (d + 1 + (k + 1)) → Fin (Module.finrank ℝ V)) :
    FunctionalInequalities.Analysis.Tensor.symmetrize (Module.finrank ℝ V) (d + (k + 2)) (d + 1)
        (FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField d (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h))) (J ∘ Fin.cast (by omega)) =
      FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h * FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField (d + 1) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ h) J := by
  rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_apply_comp_cast_readable]
  set I : Fin (k + 1) → Fin (Module.finrank ℝ V) := J ∘ Fin.natAdd (d + 1)
  set i : Fin (d + 1) → Fin (Module.finrank ℝ V) := J ∘ Fin.castAdd (k + 1)
  have hgen : FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h I) = FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h • FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ h I :=
    congrFun (FunctionalInequalities.KLS.LogConcave.PoissonIterate.genField_step m hν hi hνU hU hC h) I
  have hR : FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h * FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField (d + 1) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ h) J =
      FunctionalInequalities.Analysis.BakryEmery.taylorTensor (ν : Measure V) (⇑(FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h I))) (d + 1)
        (fun p => stdOrthonormalBasis ℝ V (i p)) := by
    rw [hgen, FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_Lp_smul]
    rfl
  rw [hR, FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_gen_apply_readable m hν hi hνU hU hexp (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step_mem_domain m hν hi hνU hU hC h I)]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField, PiLp.toLp_apply, Function.comp_apply]
  rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.append_cast_natAdd, FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0, FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField, Fin.cons_zero, Fin.tail_cons,
    FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_center_readable hexp _ hd]
  simp only [FunctionalInequalities.KLS.LogConcave.PoissonIterate.append_cast_castAdd, Function.comp_apply]
  rfl
