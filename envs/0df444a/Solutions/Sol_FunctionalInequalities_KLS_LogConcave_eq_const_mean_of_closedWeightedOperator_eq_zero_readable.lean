-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.eq_const_mean_of_closedWeightedOperator_eq_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:43:28.836175+00:00
-- url     : https://prove2.me/submissions/8f5de7d8-1195-4693-8d8d-328724eb1871

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_ZeroGradient
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel
import Theorems.Thm_FunctionalInequalities_Energy_Euclidean_ae_add_eq_of_integral_mul_fderiv_eq_zero_readable
import Theorems.Thm_FunctionalInequalities_Energy_Euclidean_exists_ae_eq_const_of_measurable_of_forall_ae_add_eq_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_restrict_le_smul_of_eq_tilted_readable

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
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
section
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
omit [InnerProductSpace ℝ V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Translation invariance up to null sets passes to the measurable representative. -/
theorem FunctionalInequalities.Energy.Euclidean.forall_ae_add_eq_mk {h : V → ℝ} (hh : AEStronglyMeasurable h m)
    (htr : ∀ v : V, ∀ᵐ x ∂m, h (x + v) = h x) (v : V) :
    ∀ᵐ x ∂m, hh.mk h (x + v) = hh.mk h x := by
  have hmk : ∀ᵐ x ∂m, h (x + v) = hh.mk h (x + v) :=
    (measurePreserving_add_right m v).quasiMeasurePreserving.ae hh.ae_eq_mk
  filter_upwards [hmk, htr v, hh.ae_eq_mk] with x hx₁ hx₂ hx₃
  exact hx₁.symm.trans (hx₂.trans hx₃)
/-- A function invariant under every translation up to null sets is almost everywhere constant. -/
theorem FunctionalInequalities.Energy.Euclidean.exists_ae_eq_const_of_forall_ae_add_eq {h : V → ℝ} (hh : AEStronglyMeasurable h m)
    (htr : ∀ v : V, ∀ᵐ x ∂m, h (x + v) = h x) :
    ∃ c : ℝ, ∀ᵐ x ∂m, h x = c := by
  obtain ⟨c, hc⟩ :=
    exists_ae_eq_const_of_measurable_of_forall_ae_add_eq_readable m
      hh.measurable_mk (forall_ae_add_eq_mk m hh htr)
  refine ⟨c, ?_⟩
  filter_upwards [hh.ae_eq_mk, hc] with x hx₁ hx₂
  exact hx₁.trans hx₂
/-- **Zero weak gradient implies constancy**: a locally integrable `h` with
`∫ h ∂_w φ dm = 0` for all `φ ∈ C_c^∞` and all `w` is `m`-almost everywhere constant. -/
theorem FunctionalInequalities.Energy.Euclidean.exists_ae_eq_const_of_integral_mul_fderiv_eq_zero {h : V → ℝ} (hh : LocallyIntegrable h m)
    (h0 : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ w : V,
      ∫ x, h x * fderiv ℝ φ x w ∂m = 0) :
    ∃ c : ℝ, ∀ᵐ x ∂m, h x = c := by
  exact exists_ae_eq_const_of_forall_ae_add_eq m hh.aestronglyMeasurable
    (fun v => ae_add_eq_of_integral_mul_fderiv_eq_zero_readable m hh h0 v)
end
end
end

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
omit [SecondCountableTopology V] in
/-- Every `L²(ν)` class is locally integrable for Haar measure. -/
theorem FunctionalInequalities.KLS.LogConcave.locallyIntegrable_coeFn (hνU : (ν : Measure V) = m.tilted (-U)) (hU : Continuous U)
    (f : Lp ℝ 2 (ν : Measure V)) : LocallyIntegrable (f : V → ℝ) m := by
  refine (locallyIntegrable_iff).2 fun K hK => ?_
  obtain ⟨c, hc, hle⟩ := restrict_le_smul_of_eq_tilted_readable m hνU hU hK
  have h1 : Integrable (f : V → ℝ) (ν : Measure V) :=
    (Lp.memLp f).integrable (by norm_num)
  exact (h1.smul_measure hc).mono_measure hle
/-- **The kernel of the closed unit gradient consists of constants**: if `T̄ h = 0`, then `h` is the
`L²(ν)` constant equal to its mean. -/
theorem solution (hν : FunctionalInequalities.KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U)
    (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (h0 : hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h = 0) :
    (h : Lp ℝ 2 (ν : Measure V)) = FunctionalInequalities.L2.const ν (FunctionalInequalities.L2.mean ν (h : Lp ℝ 2 (ν : Measure V))) := by
  obtain ⟨c, hc⟩ :=
    FunctionalInequalities.Energy.Euclidean.exists_ae_eq_const_of_integral_mul_fderiv_eq_zero m
      (FunctionalInequalities.KLS.LogConcave.locallyIntegrable_coeFn m hνU hU (h : Lp ℝ 2 (ν : Measure V)))
      (fun φ hφ hφc w =>
        FunctionalInequalities.KLS.LogConcave.integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero_readable
          m hν hi hνU hU h h0 hφ hφc w)
  have hac : (ν : Measure V) ≪ m := by
    rw [hνU]
    exact tilted_absolutelyContinuous m (-U)
  have hae :
      (h : Lp ℝ 2 (ν : Measure V)) =ᵐ[(ν : Measure V)] (fun _ : V => c) :=
    hac.ae_le hc
  have hconst :
      (FunctionalInequalities.L2.const ν c : Lp ℝ 2 (ν : Measure V)) =ᵐ[(ν : Measure V)] (fun _ : V => c) :=
    FunctionalInequalities.L2.const_coeFn ν c
  have hL :
      (h : Lp ℝ 2 (ν : Measure V)) = FunctionalInequalities.L2.const ν c :=
    Lp.ext (hae.trans hconst.symm)
  rw [hL, FunctionalInequalities.L2.mean_const]
