-- Prove2me | solution 1 for BanditAlgorithm.tendsto_gittins_stack_retirement_envelope_zero
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T17:07:52.550958+00:00
-- url     : https://prove2.me/submissions/c062364b-1ba3-49a5-8343-fcfbd47d3d13

import Definitions.Def_GittinsChargeInterleaving
import Definitions.Def_GittinsFiniteRetirementValue
import Definitions.Def_GittinsIndex
import Definitions.Def_MarkovChainKernel
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.ProductMeasure
import Mathlib.Topology.MetricSpace.Bounded
import Theorems.Thm_BanditAlgorithm_gittinsFiniteRetirementValue_mono_of_integrable
import Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_bellman_of_finite_tendsto
import Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_eq_zero_iff_index_le
import Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_lipschitz_charge
import Theorems.Thm_BanditAlgorithm_gittins_stopping_ratio_le_index
import Theorems.Thm_BanditAlgorithm_integrable_discountedStoppedSum
import Theorems.Thm_BanditAlgorithm_integral_discountedStoppedSum_one_bounds
import Theorems.Thm_BanditAlgorithm_integral_discountedStoppedSum_sub_charge
import Theorems.Thm_BanditAlgorithm_measurable_gittinsFiniteRetirementValue
import Theorems.Thm_BanditAlgorithm_measurable_gittinsRetirementValue_of_finite_tendsto


import Definitions.Def_GittinsTerminalPotential
import Definitions.Def_GittinsPrevailingChargeValue
open MeasureTheory ProbabilityTheory
open Filter Topology

namespace BanditAlgorithm

noncomputable def finiteRetirementSegment
    {S : Type*} (α : ℝ) (q : S → ℝ)
    (b m : ℕ) (ω : ℕ → S) : ℝ :=
  ∑ j ∈ Finset.range m, α ^ j * q (ω (b + j))

lemma discountedStoppedSum_coe_nat
    {S : Type*} (α : ℝ) (f : S → ℝ)
    (m : (ℕ → S) → ℕ) (ω : ℕ → S) :
    discountedStoppedSum α f (fun z ↦ (m z : ℕ∞)) ω =
      finiteRetirementSegment α f 0 (m ω) ω := by
  rw [discountedStoppedSum, finiteRetirementSegment,
    tsum_eq_sum (s := Finset.range (m ω))]
  · apply Finset.sum_congr rfl
    intro t ht
    simp only [Finset.mem_range] at ht
    simp [ht]
  · intro t ht
    simp only [Finset.mem_range, not_lt] at ht
    simp [not_lt_of_ge ht]

lemma markovChainMeasure_eq_traj_zero
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    markovChainMeasure P x =
      Kernel.traj (markovChainStep P) 0
        (fun _ : Finset.Iic 0 ↦ x) := by
  rw [← markovChainKernel_apply, markovChainKernel, Kernel.comap_apply]

noncomputable def trajectoryStateMarginal
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) : Measure S :=
  (Kernel.partialTraj (X := fun _ : ℕ ↦ S)
      (markovChainStep P) b (b + t) x₀).map
    (fun z ↦ z ⟨b + t, Finset.mem_Iic.2 le_rfl⟩)

lemma trajectoryStateMarginal_zero
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    trajectoryStateMarginal P b 0 x₀ =
      Measure.dirac (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  simp only [trajectoryStateMarginal, Nat.add_zero,
    Kernel.partialTraj_self, Kernel.id_apply]
  rw [Measure.map_dirac' (by fun_prop)]

private lemma map_bind_kernel
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (f : A → B) (hf : Measurable f)
    (K : Kernel B C) :
    (μ.map f).bind K = μ.bind (fun x ↦ K (f x)) := by
  rw [Measure.bind, Measure.bind, Measure.map_map]
  · rfl
  · exact K.measurable
  · exact hf

lemma trajectoryStateMarginal_succ
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    trajectoryStateMarginal P b (t + 1) x₀ =
      (trajectoryStateMarginal P b t x₀).bind P := by
  rw [trajectoryStateMarginal, trajectoryStateMarginal]
  simp only [Nat.add_succ]
  rw [← Kernel.map_apply _ (by fun_prop)]
  rw [Kernel.partialTraj_succ_eq_comp (by omega : b ≤ b + t)]
  rw [Kernel.map_comp]
  rw [Kernel.map_partialTraj_succ_self]
  rw [Kernel.comp_apply]
  rw [markovChainStep]
  rw [map_bind_kernel
    (Kernel.partialTraj (X := fun _ : ℕ ↦ S)
      (markovChainStep P) b (b + t) x₀)
    (fun z ↦ z ⟨b + t, Finset.mem_Iic.2 le_rfl⟩)
    (by fun_prop) P]
  apply Measure.bind_congr_right
  filter_upwards with z
  rw [Kernel.comap_apply]

lemma trajectoryStateMarginal_eq_from_current
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    trajectoryStateMarginal P b t x₀ =
      trajectoryStateMarginal P 0 t
        (fun _ : Finset.Iic 0 ↦
          x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  induction t with
  | zero =>
      rw [trajectoryStateMarginal_zero, trajectoryStateMarginal_zero]
  | succ t ih =>
      rw [trajectoryStateMarginal_succ,
        trajectoryStateMarginal_succ, ih]

lemma map_traj_eval_eq_trajectoryStateMarginal
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (Kernel.traj (X := fun _ : ℕ ↦ S) (markovChainStep P) b x₀).map
        (fun ω ↦ ω (b + t)) =
      trajectoryStateMarginal P b t x₀ := by
  rw [trajectoryStateMarginal]
  rw [show (fun ω : ℕ → S ↦ ω (b + t)) =
      (fun z : (j : Finset.Iic (b + t)) → S ↦
        z ⟨b + t, Finset.mem_Iic.2 le_rfl⟩) ∘
      Preorder.frestrictLe (π := fun _ : ℕ ↦ S) (b + t) by rfl]
  rw [← Measure.map_map]
  · have hproj :=
      Kernel.traj_map_frestrictLe_apply
        (X := fun _ : ℕ ↦ S) (κ := markovChainStep P)
        b (b + t) x₀
    rw [hproj]
  · fun_prop
  · fun_prop

lemma map_traj_eval_eq_map_markovChainMeasure_eval
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (Kernel.traj (X := fun _ : ℕ ↦ S) (markovChainStep P) b x₀).map
        (fun ω ↦ ω (b + t)) =
      (markovChainMeasure P
        (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩)).map
          (fun ω ↦ ω t) := by
  rw [markovChainMeasure_eq_traj_zero]
  calc
    (Kernel.traj (X := fun _ : ℕ ↦ S)
        (markovChainStep P) b x₀).map (fun ω ↦ ω (b + t)) =
        trajectoryStateMarginal P b t x₀ :=
      map_traj_eval_eq_trajectoryStateMarginal P b t x₀
    _ = trajectoryStateMarginal P 0 t
        (fun _ : Finset.Iic 0 ↦
          x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) :=
      trajectoryStateMarginal_eq_from_current P b t x₀
    _ = (Kernel.traj (X := fun _ : ℕ ↦ S) (markovChainStep P) 0
        (fun _ : Finset.Iic 0 ↦
          x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩)).map
          (fun ω ↦ ω t) := by
      simpa using
        (map_traj_eval_eq_trajectoryStateMarginal P 0 t
          (fun _ : Finset.Iic 0 ↦
            x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩)).symm

lemma constNat_isTrajStoppingTime
    {S : Type*} [MeasurableSpace S] (m : ℕ) :
    IsTrajStoppingTime (fun _ : ℕ → S ↦ (m : ℕ∞)) := by
  intro t
  by_cases hmt : m ≤ t
  · convert MeasurableSet.univ
    ext ω
    simp [hmt]
  · convert MeasurableSet.empty
    ext ω
    simp [hmt]

lemma discountedStoppedSum_const_succ
    {S : Type*} (α : ℝ) (f : S → ℝ) (n : ℕ) (ω : ℕ → S) :
    discountedStoppedSum α f (fun _ ↦ ((n + 1 : ℕ) : ℕ∞)) ω =
      discountedStoppedSum α f (fun _ ↦ (n : ℕ∞)) ω +
        α ^ n * f (ω n) := by
  rw [discountedStoppedSum_coe_nat,
    discountedStoppedSum_coe_nat,
    finiteRetirementSegment, finiteRetirementSegment]
  rw [Finset.sum_range_succ]
  simp

lemma integrable_markovChain_eval_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (t : ℕ) :
    Integrable (fun ω : ℕ → S ↦ r (ω t))
      (markovChainMeasure P x) := by
  have hsucc := integrable_discountedStoppedSum P hr hα0.le hint x
    (constNat_isTrajStoppingTime (S := S) (t + 1))
  have hprev := integrable_discountedStoppedSum P hr hα0.le hint x
    (constNat_isTrajStoppingTime (S := S) t)
  have hdiff := hsucc.sub hprev
  have heq :
      (fun ω : ℕ → S ↦
        discountedStoppedSum α r
            (fun _ ↦ ((t + 1 : ℕ) : ℕ∞)) ω -
          discountedStoppedSum α r (fun _ ↦ (t : ℕ∞)) ω) =
        fun ω ↦ α ^ t * r (ω t) := by
    funext ω
    rw [discountedStoppedSum_const_succ]
    ring
  change Integrable (fun ω : ℕ → S ↦
      discountedStoppedSum α r
          (fun _ ↦ ((t + 1 : ℕ) : ℕ∞)) ω -
        discountedStoppedSum α r (fun _ ↦ (t : ℕ∞)) ω)
      (markovChainMeasure P x) at hdiff
  rw [heq] at hdiff
  have hscaled := hdiff.const_mul (α ^ t)⁻¹
  simpa [mul_assoc, pow_ne_zero t hα0.ne'] using hscaled

noncomputable def truncatedStoppedSum
    {S : Type*} (α : ℝ) (f : S → ℝ)
    (τ : (ℕ → S) → ℕ∞) (N : ℕ) (ω : ℕ → S) : ℝ :=
  ∑ t ∈ Finset.range N,
    if (t : ℕ∞) < τ ω then α ^ t * f (ω t) else 0

private lemma measurableSet_lt_trajStoppingTime
    {S : Type*} [MeasurableSpace S] {τ : (ℕ → S) → ℕ∞}
    (hτ : IsTrajStoppingTime τ) (t : ℕ) :
    MeasurableSet {ω | (t : ℕ∞) < τ ω} := by
  rw [show {ω | (t : ℕ∞) < τ ω} =
      {ω | τ ω ≤ (t : ℕ∞)}ᶜ by ext ω; simp]
  have hfil :
      trajectoryFiltration S t ≤
        (inferInstance : MeasurableSpace (ℕ → S)) := by
    intro A hA
    rcases hA with ⟨B, hB, rfl⟩
    exact hB.preimage (by fun_prop)
  exact (hfil _ (hτ t)).compl

lemma measurable_truncatedStoppedSum
    {S : Type*} [MeasurableSpace S]
    {α : ℝ} {f : S → ℝ} (hf : Measurable f)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ)
    (N : ℕ) :
    Measurable (truncatedStoppedSum α f τ N) := by
  apply Finset.measurable_sum
  intro t ht
  exact Measurable.ite (measurableSet_lt_trajStoppingTime hτ t)
    (measurable_const.mul (hf.comp (measurable_pi_apply t)))
    measurable_const

private lemma measurable_discountedAbsSeries
    {S : Type*} [MeasurableSpace S] {α : ℝ}
    {r : S → ℝ} (hr : Measurable r) :
    Measurable (fun ω : ℕ → S ↦
      ∑' t : ℕ, α ^ t * |r (ω t)|) := by
  apply Measurable.tsum
  intro t
  exact measurable_const.mul
    (by
      have ht : Measurable (fun ω : ℕ → S ↦ r (ω t)) :=
        hr.comp (measurable_pi_apply t)
      fun_prop)

private lemma measurable_discountedAbsSeriesENNReal
    {S : Type*} [MeasurableSpace S] {α : ℝ}
    {r : S → ℝ} (hr : Measurable r) :
    Measurable (fun ω : ℕ → S ↦
      ∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)) := by
  apply Measurable.ennreal_tsum
  intro t
  exact ENNReal.measurable_ofReal.comp
    (measurable_const.mul
      (by
        have ht : Measurable (fun ω : ℕ → S ↦ r (ω t)) :=
          hr.comp (measurable_pi_apply t)
        fun_prop))

private lemma ae_summable_discountedAbsSeries
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    ∀ᵐ ω ∂markovChainMeasure P x,
      Summable (fun t : ℕ ↦ α ^ t * |r (ω t)|) := by
  have hfinite :
      ∀ᵐ ω ∂markovChainMeasure P x,
        (∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)) < ⊤ :=
    ae_lt_top (measurable_discountedAbsSeriesENNReal hr)
      (ne_of_lt (hint x))
  filter_upwards [hfinite] with ω hω
  have hs := ENNReal.summable_toReal (ne_of_lt hω)
  simpa [ENNReal.toReal_ofReal
    (mul_nonneg (pow_nonneg hα0 _) (abs_nonneg _))] using hs

private lemma integrable_discountedAbsSeries
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    Integrable (fun ω : ℕ → S ↦
      ∑' t : ℕ, α ^ t * |r (ω t)|)
      (markovChainMeasure P x) := by
  refine ⟨(measurable_discountedAbsSeries hr).aestronglyMeasurable, ?_⟩
  have hnonneg :
      ∀ᵐ ω ∂markovChainMeasure P x,
        0 ≤ ∑' t : ℕ, α ^ t * |r (ω t)| :=
    Filter.Eventually.of_forall fun ω ↦ tsum_nonneg fun t ↦
      mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)
  rw [hasFiniteIntegral_iff_ofReal hnonneg]
  calc
    (∫⁻ ω, ENNReal.ofReal (∑' t : ℕ, α ^ t * |r (ω t)|)
        ∂markovChainMeasure P x) =
        ∫⁻ ω, ∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)
          ∂markovChainMeasure P x := by
      apply lintegral_congr_ae
      filter_upwards
        [ae_summable_discountedAbsSeries P hr hα0 hint x]
        with ω hω
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun t ↦ mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)) hω
    _ < ⊤ := hint x

noncomputable def discountedAbsoluteRewardValue
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ) (x : S) : ℝ :=
  ∫ ω, ∑' t : ℕ, α ^ t * |r (ω t)|
    ∂markovChainMeasure P x

noncomputable def discountedAbsoluteRewardFuture
    {S : Type*} (r : S → ℝ) (α : ℝ)
    (b : ℕ) (ω : ℕ → S) : ℝ :=
  ∑' t : ℕ, α ^ t * |r (ω (b + t))|

private lemma measurable_discountedAbsoluteRewardFuture
    {S : Type*} [MeasurableSpace S]
    {r : S → ℝ} (hr : Measurable r) (α : ℝ) (b : ℕ) :
    Measurable (discountedAbsoluteRewardFuture r α b) := by
  apply Measurable.tsum
  intro t
  fun_prop

private lemma measurable_discountedAbsoluteRewardFutureENNReal
    {S : Type*} [MeasurableSpace S]
    {r : S → ℝ} (hr : Measurable r) (α : ℝ) (b : ℕ) :
    Measurable (fun ω : ℕ → S ↦
      ∑' t : ℕ,
        ENNReal.ofReal (α ^ t * |r (ω (b + t))|)) := by
  apply Measurable.ennreal_tsum
  intro t
  fun_prop

lemma lintegral_traj_eval_eq_markovChain_eval
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (f : S → ENNReal) (hf : Measurable f)
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (∫⁻ (ω : ℕ → S), f (ω (b + t))
        ∂Kernel.traj (markovChainStep P) b x₀) =
      ∫⁻ (ω : ℕ → S), f (ω t)
        ∂markovChainMeasure P
          (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  have hleft :
      (∫⁻ y, f y ∂
        ((Kernel.traj (markovChainStep P) b x₀).map
          (fun ω : ℕ → S ↦ ω (b + t)))) =
        ∫⁻ (ω : ℕ → S), f (ω (b + t))
          ∂Kernel.traj (markovChainStep P) b x₀ :=
    MeasureTheory.lintegral_map
      hf (measurable_pi_apply (b + t))
  have hright :
      (∫⁻ y, f y ∂
        ((markovChainMeasure P
          (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩)).map
            (fun ω : ℕ → S ↦ ω t))) =
        ∫⁻ (ω : ℕ → S), f (ω t)
          ∂markovChainMeasure P
            (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) :=
    MeasureTheory.lintegral_map hf (measurable_pi_apply t)
  rw [map_traj_eval_eq_map_markovChainMeasure_eval P b t x₀] at hleft
  exact hleft.symm.trans hright

lemma lintegral_discountedAbsoluteRewardFutureENNReal_traj
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    (α : ℝ) (b : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (∫⁻ (ω : ℕ → S), ∑' t : ℕ,
        ENNReal.ofReal (α ^ t * |r (ω (b + t))|)
        ∂Kernel.traj (markovChainStep P) b x₀) =
      ∫⁻ (ω : ℕ → S), ∑' t : ℕ,
        ENNReal.ofReal (α ^ t * |r (ω t)|)
        ∂markovChainMeasure P
          (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  calc
    (∫⁻ (ω : ℕ → S), ∑' t : ℕ,
        ENNReal.ofReal (α ^ t * |r (ω (b + t))|)
        ∂Kernel.traj (markovChainStep P) b x₀) =
        ∑' t : ℕ, ∫⁻ (ω : ℕ → S),
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|)
          ∂Kernel.traj (markovChainStep P) b x₀ :=
      MeasureTheory.lintegral_tsum
        (fun t ↦ (by fun_prop :
          Measurable (fun ω : ℕ → S ↦
            ENNReal.ofReal
              (α ^ t * |r (ω (b + t))|))).aemeasurable)
    _ = ∑' t : ℕ, ∫⁻ (ω : ℕ → S),
          ENNReal.ofReal (α ^ t * |r (ω t)|)
          ∂markovChainMeasure P
            (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
      apply tsum_congr
      intro t
      exact lintegral_traj_eval_eq_markovChain_eval
        P (fun y ↦ ENNReal.ofReal (α ^ t * |r y|))
        (by fun_prop) b t x₀
    _ = ∫⁻ (ω : ℕ → S), ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω t)|)
          ∂markovChainMeasure P
            (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) :=
      (MeasureTheory.lintegral_tsum
        (fun t ↦ (by fun_prop :
          Measurable (fun ω : ℕ → S ↦
            ENNReal.ofReal
              (α ^ t * |r (ω t)|))).aemeasurable)).symm

lemma integrable_discountedAbsoluteRewardFuture_traj
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α)
    (b : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    Integrable (discountedAbsoluteRewardFuture r α b)
      (Kernel.traj (markovChainStep P) b x₀) := by
  let μ :=
    Kernel.traj (X := fun _ : ℕ ↦ S)
      (markovChainStep P) b x₀
  have hlin :
      (∫⁻ ω, ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|) ∂μ) < ⊤ := by
    rw [lintegral_discountedAbsoluteRewardFutureENNReal_traj
      P hr α b x₀]
    exact hint (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩)
  have hfinite :
      ∀ᵐ ω ∂μ,
        (∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|)) < ⊤ :=
    ae_lt_top
      (measurable_discountedAbsoluteRewardFutureENNReal
        hr α b) (ne_of_lt hlin)
  have hsummable :
      ∀ᵐ ω ∂μ,
        Summable (fun t : ℕ ↦
          α ^ t * |r (ω (b + t))|) := by
    filter_upwards [hfinite] with ω hω
    have hs := ENNReal.summable_toReal (ne_of_lt hω)
    simpa [ENNReal.toReal_ofReal
      (mul_nonneg (pow_nonneg hα0 _) (abs_nonneg _))] using hs
  refine ⟨
    (measurable_discountedAbsoluteRewardFuture
      hr α b).aestronglyMeasurable,
    ?_⟩
  have hnonneg :
      ∀ᵐ ω ∂μ,
        0 ≤ discountedAbsoluteRewardFuture r α b ω :=
    Filter.Eventually.of_forall fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)
  rw [hasFiniteIntegral_iff_ofReal hnonneg]
  calc
    (∫⁻ ω, ENNReal.ofReal
        (discountedAbsoluteRewardFuture r α b ω) ∂μ) =
        ∫⁻ ω, ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hsummable] with ω hω
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun t ↦
          mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)) hω
    _ < ⊤ := hlin

theorem integral_discountedAbsoluteRewardFuture_traj
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α)
    (b : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (∫ ω, discountedAbsoluteRewardFuture r α b ω
        ∂Kernel.traj (markovChainStep P) b x₀) =
      discountedAbsoluteRewardValue P r α
        (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  let μ :=
    Kernel.traj (X := fun _ : ℕ ↦ S)
      (markovChainStep P) b x₀
  let y := x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩
  have hleft :=
    integrable_discountedAbsoluteRewardFuture_traj
      P hr hα0 hint b x₀
  have hright :=
    integrable_discountedAbsSeries P hr hα0 hint y
  have hleft0 :
      0 ≤ ∫ ω, discountedAbsoluteRewardFuture r α b ω ∂μ :=
    integral_nonneg fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)
  have hright0 :
      0 ≤ discountedAbsoluteRewardValue P r α y := by
    dsimp [discountedAbsoluteRewardValue]
    exact integral_nonneg fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)
  apply (ENNReal.ofReal_eq_ofReal_iff hleft0 hright0).mp
  dsimp [discountedAbsoluteRewardValue]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    hleft (Filter.Eventually.of_forall fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _))]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    hright (Filter.Eventually.of_forall fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _))]
  change
    (∫⁻ ω, ENNReal.ofReal
      (discountedAbsoluteRewardFuture r α b ω) ∂μ) =
    ∫⁻ ω, ENNReal.ofReal
      (∑' t : ℕ, α ^ t * |r (ω t)|)
      ∂markovChainMeasure P y
  have hlin :
      (∫⁻ ω, ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|) ∂μ) < ⊤ := by
    rw [lintegral_discountedAbsoluteRewardFutureENNReal_traj
      P hr α b x₀]
    exact hint y
  have hleftsum :
      ∀ᵐ ω ∂μ,
        Summable (fun t : ℕ ↦
          α ^ t * |r (ω (b + t))|) := by
    have hfinite :
        ∀ᵐ ω ∂μ,
          (∑' t : ℕ,
            ENNReal.ofReal
              (α ^ t * |r (ω (b + t))|)) < ⊤ :=
      ae_lt_top
        (measurable_discountedAbsoluteRewardFutureENNReal
          hr α b) (ne_of_lt hlin)
    filter_upwards [hfinite] with ω hω
    have hs := ENNReal.summable_toReal (ne_of_lt hω)
    simpa [ENNReal.toReal_ofReal
      (mul_nonneg (pow_nonneg hα0 _) (abs_nonneg _))] using hs
  calc
    (∫⁻ ω, ENNReal.ofReal
        (discountedAbsoluteRewardFuture r α b ω) ∂μ) =
        ∫⁻ ω, ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hleftsum] with ω hω
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun t ↦
          mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)) hω
    _ = ∫⁻ ω, ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω t)|)
          ∂markovChainMeasure P y :=
      lintegral_discountedAbsoluteRewardFutureENNReal_traj
        P hr α b x₀
    _ = ∫⁻ ω, ENNReal.ofReal
          (∑' t : ℕ, α ^ t * |r (ω t)|)
          ∂markovChainMeasure P y := by
      apply lintegral_congr_ae
      filter_upwards
        [ae_summable_discountedAbsSeries
          P hr hα0 hint y] with ω hω
      exact (ENNReal.ofReal_tsum_of_nonneg
        (fun t ↦
          mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)) hω).symm

lemma integrable_discountedAbsoluteRewardFuture_markov
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (N : ℕ) :
    Integrable (discountedAbsoluteRewardFuture r α N)
      (markovChainMeasure P x) := by
  let R : (ℕ → S) → ℝ :=
    fun ω ↦ ∑' t : ℕ, α ^ t * |r (ω t)|
  let Q : (ℕ → S) → ℝ :=
    fun ω ↦ ∑ t ∈ Finset.range N, α ^ t * |r (ω t)|
  have hR : Integrable R (markovChainMeasure P x) :=
    integrable_discountedAbsSeries P hr hα0.le hint x
  have hQ : Integrable Q (markovChainMeasure P x) := by
    apply MeasureTheory.integrable_finset_sum
    intro t ht
    exact (integrable_markovChain_eval_of_discounted
      P hr hα0 hint x t).norm.const_mul (α ^ t)
  have hdiff := hR.sub hQ
  have heq :
      (fun ω ↦ R ω - Q ω) =ᵐ[markovChainMeasure P x]
        fun ω ↦ α ^ N *
          discountedAbsoluteRewardFuture r α N ω := by
    filter_upwards
      [ae_summable_discountedAbsSeries
        P hr hα0.le hint x] with ω hs
    have hsplit := hs.sum_add_tsum_nat_add N
    dsimp [R, Q, discountedAbsoluteRewardFuture]
    rw [← hsplit]
    simp only [add_sub_cancel_left]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro t
    rw [pow_add]
    rw [Nat.add_comm t N]
    ring
  have hscaledInt :
      Integrable
        (fun ω ↦ α ^ N *
          discountedAbsoluteRewardFuture r α N ω)
        (markovChainMeasure P x) :=
    hdiff.congr heq
  have hscaled := hscaledInt.const_mul (α ^ N)⁻¹
  simpa [mul_assoc, pow_ne_zero N hα0.ne'] using hscaled

set_option maxHeartbeats 800000 in
theorem integrable_discountedAbsoluteRewardValue_along_markov
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (N : ℕ) :
    Integrable
      (fun ω : ℕ → S ↦
        discountedAbsoluteRewardValue P r α (ω N))
      (markovChainMeasure P x) ∧
    (∫ ω, discountedAbsoluteRewardValue P r α (ω N)
        ∂markovChainMeasure P x) =
      ∫ ω, discountedAbsoluteRewardFuture r α N ω
        ∂markovChainMeasure P x := by
  let x₀ : (j : Finset.Iic 0) → S := fun _ ↦ x
  let μ :=
    Kernel.traj (X := fun _ : ℕ ↦ S)
      (markovChainStep P) 0 x₀
  let F : (ℕ → S) → ℝ :=
    discountedAbsoluteRewardFuture r α N
  have hFmarkov :
      Integrable F (markovChainMeasure P x) :=
    integrable_discountedAbsoluteRewardFuture_markov
      P hr hα0 hint x N
  have hmeasure : markovChainMeasure P x = μ := by
    rw [markovChainMeasure_eq_traj_zero]
  have hF : Integrable F μ := by
    rwa [← hmeasure]
  have hcond :=
    Kernel.condExp_traj
      (X := fun _ : ℕ ↦ S) (κ := markovChainStep P)
      (a := 0) (b := N) (Nat.zero_le N)
      (x₀ := x₀) hF
  let C : (ℕ → S) → ℝ :=
    MeasureTheory.condExp
      (Filtration.piLE (X := fun _ : ℕ ↦ S) N)
      μ F
  have hCint : Integrable C μ := integrable_condExp
  have heq :
      C =ᵐ[μ] fun ω ↦
        discountedAbsoluteRewardValue P r α (ω N) := by
    filter_upwards [hcond] with ω hω
    change
      MeasureTheory.condExp
        (Filtration.piLE (X := fun _ : ℕ ↦ S) N)
        μ F ω =
        discountedAbsoluteRewardValue P r α (ω N)
    rw [hω]
    simpa [F] using
      (integral_discountedAbsoluteRewardFuture_traj
        P hr hα0.le hint N (Preorder.frestrictLe N ω))
  have hAintμ :
      Integrable
        (fun ω : ℕ → S ↦
          discountedAbsoluteRewardValue P r α (ω N)) μ :=
    hCint.congr heq
  have hintEqμ :
      (∫ ω, discountedAbsoluteRewardValue P r α (ω N) ∂μ) =
        ∫ ω, F ω ∂μ := by
    rw [← integral_congr_ae heq]
    exact integral_condExp
      (Filtration.le
        (Filtration.piLE (X := fun _ : ℕ ↦ S)) N)
  constructor
  · rw [hmeasure]
    exact hAintμ
  · rw [hmeasure]
    simpa [F] using hintEqμ

theorem tendsto_integral_truncatedStoppedSum
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) {τ : (ℕ → S) → ℕ∞}
    (hτ : IsTrajStoppingTime τ) :
    Tendsto
      (fun N ↦ ∫ ω, truncatedStoppedSum α r τ N ω
        ∂markovChainMeasure P x)
      atTop
      (𝓝 (∫ ω, discountedStoppedSum α r τ ω
        ∂markovChainMeasure P x)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun ω : ℕ → S ↦ ∑' t : ℕ, α ^ t * |r (ω t)|)
  · intro N
    exact (measurable_truncatedStoppedSum hr hτ N).aestronglyMeasurable
  · exact integrable_discountedAbsSeries P hr hα0 hint x
  · intro N
    filter_upwards [ae_summable_discountedAbsSeries P hr hα0 hint x]
      with ω hsum
    calc
      ‖truncatedStoppedSum α r τ N ω‖ ≤
          ∑ t ∈ Finset.range N,
            ‖if (t : ℕ∞) < τ ω then α ^ t * r (ω t) else 0‖ := by
        exact norm_sum_le _ _
      _ ≤ ∑ t ∈ Finset.range N, α ^ t * |r (ω t)| := by
        apply Finset.sum_le_sum
        intro t ht
        by_cases hstop : (t : ℕ∞) < τ ω
        · simp [hstop, abs_of_nonneg hα0]
        · simp [hstop, mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)]
      _ ≤ ∑' t : ℕ, α ^ t * |r (ω t)| :=
        hsum.sum_le_tsum (Finset.range N)
          (fun t ht ↦ mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _))
  · filter_upwards [ae_summable_discountedAbsSeries P hr hα0 hint x]
      with ω hsum
    let a : ℕ → ℝ := fun t ↦
      if (t : ℕ∞) < τ ω then α ^ t * r (ω t) else 0
    have ha : Summable a := by
      apply Summable.of_norm_bounded hsum
      intro t
      by_cases hstop : (t : ℕ∞) < τ ω
      · simp [a, hstop, abs_of_nonneg hα0]
      · simp [a, hstop,
          mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)]
    change Tendsto (fun N ↦ ∑ t ∈ Finset.range N, a t)
      atTop (𝓝 (∑' t, a t))
    simpa only [Finset.sum_filter] using ha.hasSum.tendsto_sum_nat

lemma top_isTrajStoppingTime
    {S : Type*} [MeasurableSpace S] :
    IsTrajStoppingTime (fun _ : ℕ → S ↦ (⊤ : ℕ∞)) := by
  intro n
  convert MeasurableSet.empty
  ext ω
  simp

theorem tendsto_discounted_absoluteRewardFuture_integral_zero
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) :
    Tendsto
      (fun N ↦ α ^ N *
        ∫ ω, discountedAbsoluteRewardFuture r α N ω
          ∂markovChainMeasure P x)
      atTop (𝓝 0) := by
  let R : (ℕ → S) → ℝ :=
    fun ω ↦ ∑' t : ℕ, α ^ t * |r (ω t)|
  let Q : ℕ → (ℕ → S) → ℝ :=
    fun N ω ↦ ∑ t ∈ Finset.range N, α ^ t * |r (ω t)|
  have habsMeas : Measurable (fun y ↦ |r y|) := by
    fun_prop
  have hintAbs :
      DiscountedRewardIntegrable P (fun y ↦ |r y|) α := by
    intro y
    simpa only [abs_abs] using hint y
  have hprefix :=
    tendsto_integral_truncatedStoppedSum
      P habsMeas hα0.le hintAbs x
      (top_isTrajStoppingTime (S := S))
  have hprefix' :
      Tendsto
        (fun N ↦ ∫ ω, Q N ω ∂markovChainMeasure P x)
        atTop
        (𝓝 (∫ ω, R ω ∂markovChainMeasure P x)) := by
    simpa [Q, R, truncatedStoppedSum,
      discountedStoppedSum] using hprefix
  have heq : ∀ N,
      α ^ N *
          ∫ ω, discountedAbsoluteRewardFuture r α N ω
            ∂markovChainMeasure P x =
        (∫ ω, R ω ∂markovChainMeasure P x) -
          ∫ ω, Q N ω ∂markovChainMeasure P x := by
    intro N
    have hRint :
        Integrable R (markovChainMeasure P x) :=
      integrable_discountedAbsSeries P hr hα0.le hint x
    have hQint :
        Integrable (Q N) (markovChainMeasure P x) := by
      apply MeasureTheory.integrable_finset_sum
      intro t ht
      exact (integrable_markovChain_eval_of_discounted
        P hr hα0 hint x t).norm.const_mul (α ^ t)
    have hFint :=
      integrable_discountedAbsoluteRewardFuture_markov
        P hr hα0 hint x N
    have hpoint :
        (fun ω ↦ R ω - Q N ω) =ᵐ[markovChainMeasure P x]
          fun ω ↦ α ^ N *
            discountedAbsoluteRewardFuture r α N ω := by
      filter_upwards
        [ae_summable_discountedAbsSeries
          P hr hα0.le hint x] with ω hs
      have hsplit := hs.sum_add_tsum_nat_add N
      dsimp [R, Q, discountedAbsoluteRewardFuture]
      rw [← hsplit]
      simp only [add_sub_cancel_left]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro t
      rw [pow_add, Nat.add_comm t N]
      ring
    rw [← integral_const_mul]
    rw [← integral_sub hRint hQint]
    exact (integral_congr_ae hpoint).symm
  rw [show (fun N ↦ α ^ N *
      ∫ ω, discountedAbsoluteRewardFuture r α N ω
        ∂markovChainMeasure P x) =
      fun N ↦ (∫ ω, R ω ∂markovChainMeasure P x) -
        ∫ ω, Q N ω ∂markovChainMeasure P x by
          funext N
          exact heq N]
  simpa using
    (tendsto_const_nhds
      (x := ∫ ω, R ω ∂markovChainMeasure P x)).sub hprefix'

end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm



@[simp] lemma currentHistoryPrevailingCharge_zero
    {k : ℕ} {S : Type*} (g : S → ℝ)
    (h : MarkovBanditHistory k S 0) (i : Fin k) :
    currentHistoryPrevailingCharge g 0 h i = g (h.2 i) :=
  rfl

lemma ae_summable_discountedAbsSeries_multiarm
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    ∀ᵐ ω ∂markovChainMeasure P x,
      Summable (fun t : ℕ ↦ α ^ t * |r (ω t)|) := by
  have hmeas : Measurable (fun ω : ℕ → S ↦
      ∑' t : ℕ, ENNReal.ofReal
        (α ^ t * |r (ω t)|)) := by
    apply Measurable.ennreal_tsum
    intro t
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.mul
        (by
          have ht : Measurable (fun ω : ℕ → S ↦ r (ω t)) :=
            hr.comp (measurable_pi_apply t)
          fun_prop))
  have hfinite :
      ∀ᵐ ω ∂markovChainMeasure P x,
        (∑' t : ℕ, ENNReal.ofReal
          (α ^ t * |r (ω t)|)) < ⊤ :=
    ae_lt_top hmeas (ne_of_lt (hint x))
  filter_upwards [hfinite] with ω hω
  have hs := ENNReal.summable_toReal (ne_of_lt hω)
  simpa [ENNReal.toReal_ofReal
    (mul_nonneg (pow_nonneg hα0 _) (abs_nonneg _))] using hs

end BanditAlgorithm

namespace BanditAlgorithm




@[simp] lemma stackPullCountBefore_zero
    {k : ℕ} (a : ℕ → Fin k) (i : Fin k) :
    stackPullCountBefore a i 0 = 0 := by
  simp [stackPullCountBefore]

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm




def markovBanditStackHistory
    {k n : ℕ} {S : Type*}
    (ω : Fin k → ℕ → S) (a : ℕ → Fin k) :
    MarkovBanditHistory k S n :=
  (fun t ↦
      (fun i ↦ ω i (stackPullCountBefore a i t), a t),
    fun i ↦ ω i (stackPullCountBefore a i n))

@[simp] lemma markovBanditStackHistory_zero
    {k : ℕ} {S : Type*}
    (ω : Fin k → ℕ → S) (a : ℕ → Fin k) :
    markovBanditStackHistory (n := 0) ω a =
      (fun t ↦ t.elim0, fun i ↦ ω i 0) := by
  apply Prod.ext
  · funext t
    exact Fin.elim0 t
  · funext i
    simp [markovBanditStackHistory]

noncomputable def markovBanditArmPrevailingChargeStack
    {k : ℕ} {S : Type*} (g : S → ℝ)
    (ω : Fin k → ℕ → S) (i : Fin k) (u : ℕ) : ℝ :=
  (Finset.range (u + 1)).inf'
    ⟨0, Finset.mem_range.2 (Nat.zero_lt_succ u)⟩
    (fun v ↦ g (ω i v))

@[simp] lemma markovBanditArmPrevailingChargeStack_zero
    {k : ℕ} {S : Type*} (g : S → ℝ)
    (ω : Fin k → ℕ → S) (i : Fin k) :
    markovBanditArmPrevailingChargeStack g ω i 0 = g (ω i 0) := by
  simp [markovBanditArmPrevailingChargeStack]

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm



abbrev MarkovBanditStackSpace (k : ℕ) (S : Type*) :=
  Fin k → ℕ → S


noncomputable def markovBanditStackMeasure
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) : Measure (MarkovBanditStackSpace k S) :=
  Measure.pi (fun i ↦ markovChainMeasure P (x i))

instance markovBanditStackMeasure.instIsProbabilityMeasure
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) :
    IsProbabilityMeasure (markovBanditStackMeasure P x) := by
  rw [markovBanditStackMeasure]
  letI : ∀ i : Fin k,
      IsProbabilityMeasure (markovChainMeasure P (x i)) := fun i ↦ by
    rw [markovChainMeasure]
    infer_instance
  exact MeasureTheory.Measure.pi.instIsProbabilityMeasure _

theorem map_markovBanditStackMeasure_arm
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) (i : Fin k) :
    (markovBanditStackMeasure P x).map (fun omega ↦ omega i) =
      markovChainMeasure P (x i) := by
  letI : ∀ j : Fin k,
      IsProbabilityMeasure (markovChainMeasure P (x j)) := fun j ↦ by
    rw [← markovChainKernel_apply]
    infer_instance
  rw [markovBanditStackMeasure, Measure.pi_map_eval]
  simp


def finiteStackPullCountBefore
    {k n : ℕ} (a : Fin n → Fin k) (i : Fin k) (t : ℕ) : ℕ :=
  ∑ s : Fin n, if (s : ℕ) < t ∧ a s = i then 1 else 0

def markovBanditFiniteStackHistory
    {k n : ℕ} {S : Type*}
    (omega : MarkovBanditStackSpace k S) (a : Fin n → Fin k) :
    MarkovBanditHistory k S n :=
  (fun t ↦
      (fun i ↦ omega i (finiteStackPullCountBefore a i t), a t),
    fun i ↦ omega i (finiteStackPullCountBefore a i n))

abbrev MarkovBanditStackPrefixSpace
    (k : ℕ) (S : Type*) (m : Fin k → ℕ) :=
  ∀ i : Fin k, Finset.Iic (m i) → S

def markovBanditStackPrefixes
    {k : ℕ} {S : Type*} (m : Fin k → ℕ)
    (omega : MarkovBanditStackSpace k S) :
    MarkovBanditStackPrefixSpace k S m :=
  fun i t ↦ omega i t

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

def markovBanditStackPrefixCurrent
    {k : ℕ} {S : Type*} (m : Fin k → ℕ) (i : Fin k)
    (q : MarkovBanditStackPrefixSpace k S m) : S :=
  q i ⟨m i, Finset.mem_Iic.2 le_rfl⟩

lemma measurable_markovBanditStackPrefixCurrent
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (m : Fin k → ℕ) (i : Fin k) :
    Measurable (markovBanditStackPrefixCurrent (S := S) m i) :=
  (measurable_pi_apply _).comp (measurable_pi_apply i)

noncomputable def markovBanditStackPrefixStep
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (m : Fin k → ℕ) (i : Fin k) :
    Kernel (MarkovBanditStackPrefixSpace k S m) S :=
  P.comap (markovBanditStackPrefixCurrent m i)
    (measurable_markovBanditStackPrefixCurrent m i)

instance markovBanditStackPrefixStep.instIsMarkovKernel
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (m : Fin k → ℕ) (i : Fin k) :
    IsMarkovKernel (markovBanditStackPrefixStep P m i) := by
  rw [markovBanditStackPrefixStep]
  infer_instance

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

lemma finiteStackPullCountBefore_mono
    {k n : ℕ} (a : Fin n → Fin k) (i : Fin k)
    {s t : ℕ} (hst : s ≤ t) :
    finiteStackPullCountBefore a i s ≤
      finiteStackPullCountBefore a i t := by
  classical
  apply Finset.sum_le_sum
  intro u hu
  by_cases hs : (u : ℕ) < s ∧ a u = i
  · have ht : (u : ℕ) < t ∧ a u = i :=
      ⟨lt_of_lt_of_le hs.1 hst, hs.2⟩
    simp [hs, ht]
  · simp [hs]

def markovBanditPrefixHistoryBefore
    {k n : ℕ} {S : Type*}
    (a : Fin n → Fin k)
    (q : MarkovBanditStackPrefixSpace k S
      (fun i ↦ finiteStackPullCountBefore a i n))
    (t : Fin (n + 1)) : MarkovBanditHistory k S t :=
  (fun u ↦
      (fun i ↦ q i ⟨finiteStackPullCountBefore a i u,
        Finset.mem_Iic.2 (finiteStackPullCountBefore_mono a i
          (Nat.le_trans (Nat.le_of_lt u.isLt) (Nat.le_of_lt_succ t.isLt)))⟩,
        a ⟨u, lt_of_lt_of_le u.isLt (Nat.le_of_lt_succ t.isLt)⟩),
    fun i ↦ q i ⟨finiteStackPullCountBefore a i t,
      Finset.mem_Iic.2 (finiteStackPullCountBefore_mono a i
        (Nat.le_of_lt_succ t.isLt))⟩)

noncomputable def markovBanditActionLikelihood
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (a : Fin n → Fin k)
    (q : MarkovBanditStackPrefixSpace k S
      (fun i ↦ finiteStackPullCountBefore a i n)) : ENNReal :=
  ∏ t : Fin n,
    (pi.select t) (markovBanditPrefixHistoryBefore a q t.castSucc) {a t}

noncomputable def markovBanditStackActionLikelihood
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (a : Fin n → Fin k)
    (omega : MarkovBanditStackSpace k S) : ENNReal :=
  markovBanditActionLikelihood pi a
    (markovBanditStackPrefixes
      (fun i ↦ finiteStackPullCountBefore a i n) omega)

noncomputable def markovBanditFixedActionHistoryMeasure
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S)
    (a : Fin n → Fin k) : Measure (MarkovBanditHistory k S n) :=
  ((markovBanditStackMeasure P x).withDensity
      (markovBanditStackActionLikelihood pi a)).map
    (fun omega ↦ markovBanditFiniteStackHistory omega a)

instance markovBanditFixedActionHistoryMeasure.instSFinite
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S)
    (a : Fin n → Fin k) :
    SFinite (markovBanditFixedActionHistoryMeasure P pi x a) := by
  rw [markovBanditFixedActionHistoryMeasure]
  infer_instance

noncomputable def markovBanditSelectMass
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (i : Fin k)
    (h : MarkovBanditHistory k S n) : ENNReal :=
  (pi.select n) h {i}

noncomputable def markovBanditFixedActionStepKernel
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (i : Fin k) :
    Kernel (MarkovBanditHistory k S n) (Fin k × S) :=
  ((P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
      ((measurable_pi_apply i).comp measurable_snd)).withDensity
    (fun h _ ↦ markovBanditSelectMass pi i h)).map
      (fun y ↦ (i, y))

instance markovBanditFixedActionStepKernel.instIsSFiniteKernel
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (i : Fin k) :
    IsSFiniteKernel (markovBanditFixedActionStepKernel
      (n := n) P pi i) := by
  let K : Kernel (MarkovBanditHistory k S n) S :=
    P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
      ((measurable_pi_apply i).comp measurable_snd)
  letI : IsSFiniteKernel (K.withDensity
      (fun h _ ↦ markovBanditSelectMass pi i h)) :=
    ProbabilityTheory.Kernel.IsSFiniteKernel.withDensity K (fun h _ ↦ by
      exact measure_ne_top ((pi.select n) h) {i})
  rw [markovBanditFixedActionStepKernel]
  infer_instance

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm


end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm




lemma summable_pow_mul_prefix_of_summable
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n)
    (hb : Summable (fun n ↦ α ^ n * b n)) :
    Summable (fun n ↦ α ^ n * ∑ v ∈ Finset.range n, b v) := by
  have hnorm : |α| < 1 := by simpa [abs_of_nonneg hα0]
  have hgeom : Summable (fun n : ℕ ↦ α ^ n) :=
    summable_geometric_of_norm_lt_one hnorm
  have hgeomShift : Summable (fun n : ℕ ↦ α ^ (n + 1)) := by
    exact (summable_nat_add_iff 1).2 hgeom
  let f : ℕ → ℝ := fun n ↦ α ^ (n + 1)
  let g : ℕ → ℝ := fun n ↦ α ^ n * b n
  have hf : Summable f := hgeomShift
  have hg : Summable g := hb
  have hprod : Summable (fun p : ℕ × ℕ ↦ f p.1 * g p.2) :=
    hf.mul_of_nonneg hg
      (fun n ↦ pow_nonneg hα0 _)
      (fun n ↦ mul_nonneg (pow_nonneg hα0 _) (hb0 n))
  have hcauchy : Summable (fun N ↦
      ∑ m ∈ Finset.range (N + 1), f m * g (N - m)) :=
    summable_sum_mul_range_of_summable_mul hprod
  have heq : (fun N ↦
      ∑ m ∈ Finset.range (N + 1), f m * g (N - m)) =
      fun N ↦ α ^ (N + 1) *
        ∑ v ∈ Finset.range (N + 1), b v := by
    funext N
    calc
      (∑ m ∈ Finset.range (N + 1), f m * g (N - m)) =
          ∑ m ∈ Finset.range (N + 1),
            α ^ (N + 1) * b (N - m) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmN : m ≤ N := by
          simpa [Finset.mem_range] using Nat.le_of_lt_succ
            (Finset.mem_range.1 hm)
        dsimp [f, g]
        rw [← mul_assoc, ← pow_add]
        congr 2
        omega
      _ = α ^ (N + 1) *
          ∑ m ∈ Finset.range (N + 1), b (N - m) := by
        rw [Finset.mul_sum]
      _ = α ^ (N + 1) *
          ∑ v ∈ Finset.range (N + 1), b v := by
        congr 1
        simpa using Finset.sum_range_reflect b (N + 1)
  rw [heq] at hcauchy
  exact (summable_nat_add_iff 1).1 (by simpa using hcauchy)


end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm



end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm



lemma tendsto_geometric_reverse_convolution_zero
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {b : ℕ → ℝ} (hb : Filter.Tendsto b Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun N ↦ ∑ u ∈ Finset.range (N + 1), α ^ (N - u) * b u)
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hC⟩ :=
    isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto b hb)
  have hgeom : Summable (fun m : ℕ ↦ C * α ^ m) := by
    exact (summable_geometric_of_norm_lt_one (by
      simpa [abs_of_nonneg hα0] using hα1)).mul_left C
  let f : ℕ → ℕ → ℝ := fun N m ↦
    if m ≤ N then α ^ m * b (N - m) else 0
  have hf : ∀ m : ℕ,
      Filter.Tendsto (fun N ↦ f N m) Filter.atTop (nhds 0) := by
    intro m
    have hmain : Filter.Tendsto (fun N ↦ α ^ m * b (N - m))
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul
        (hb.comp (Filter.tendsto_sub_atTop_nat m)))
    apply hmain.congr'
    filter_upwards [Filter.eventually_ge_atTop m] with N hNm
    simp only [f, if_pos hNm]
  have hbound : ∀ N m, ‖f N m‖ ≤ C * α ^ m := by
    intro N m
    by_cases hm : m ≤ N
    · rw [show f N m = α ^ m * b (N - m) by simp [f, hm]]
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hα0 m)]
      have hbC : ‖b (N - m)‖ ≤ C :=
        hC (b (N - m)) (Set.mem_range_self (N - m))
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_right hbC (pow_nonneg hα0 m)
    · simp [f, hm]
      exact mul_nonneg (le_trans (norm_nonneg _) (hC (b 0) (Set.mem_range_self 0)))
        (pow_nonneg hα0 m)
  have htsum : Filter.Tendsto (fun N ↦ ∑' m, f N m)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_tsum_of_dominated_convergence hgeom hf
      (Filter.Eventually.of_forall hbound)
  apply htsum.congr'
  filter_upwards with N
  rw [show (∑' m, f N m) = ∑ m ∈ Finset.range (N + 1), f N m by
    rw [tsum_eq_sum]
    intro m hm
    simp only [Finset.mem_range, not_lt] at hm
    simp [f, Nat.not_le.mpr hm]]
  calc
    (∑ m ∈ Finset.range (N + 1), f N m) =
        ∑ m ∈ Finset.range (N + 1), α ^ m * b (N - m) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmN : m ≤ N := Nat.le_of_lt_succ (Finset.mem_range.1 hm)
      simp [f, hmN]
    _ = ∑ u ∈ Finset.range (N + 1), α ^ (N - u) * b u := by
      rw [← Finset.sum_range_reflect
        (fun u ↦ α ^ (N - u) * b u) (N + 1)]
      apply Finset.sum_congr rfl
      intro m hm
      have hmN : m ≤ N := Nat.le_of_lt_succ (Finset.mem_range.1 hm)
      congr 2
      omega

noncomputable def markovBanditRetirementEnvelope
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ)
    (omega : MarkovBanditStackSpace k S) (N : ℕ) : ℝ :=
  ∑ i : Fin k, (
    (∑ u ∈ Finset.range (N + 1),
        discountedAbsoluteRewardValue P r α (omega i u)) +
      (∑' t : ℕ, α ^ t) *
        (discountedAbsoluteRewardValue P r α (omega i 0) +
          ∑ v ∈ Finset.range N, |r (omega i (v + 1))|))

lemma integrable_comp_of_map_eq
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) (nu : Measure B) (g : A → B)
    (hg : Measurable g) (hmap : mu.map g = nu)
    {f : B → ℝ} (hf : Integrable f nu) :
    Integrable (fun x ↦ f (g x)) mu := by
  have hfmap : Integrable f (mu.map g) := by rwa [hmap]
  exact (integrable_map_measure hfmap.1 hg.aemeasurable).1 hfmap

lemma integrable_discountedAbsoluteRewardValue_stack_arm
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : Fin k → S) (i : Fin k) (u : ℕ) :
    Integrable (fun omega : MarkovBanditStackSpace k S ↦
      discountedAbsoluteRewardValue P r α (omega i u))
      (markovBanditStackMeasure P x) := by
  exact integrable_comp_of_map_eq
    (markovBanditStackMeasure P x) (markovChainMeasure P (x i))
    (fun omega ↦ omega i) (measurable_pi_apply i)
    (map_markovBanditStackMeasure_arm P x i)
    (integrable_discountedAbsoluteRewardValue_along_markov
      P hr hα0 hint (x i) u).1

lemma integrable_abs_reward_stack_arm
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : Fin k → S) (i : Fin k) (u : ℕ) :
    Integrable (fun omega : MarkovBanditStackSpace k S ↦
      |r (omega i u)|) (markovBanditStackMeasure P x) := by
  exact integrable_comp_of_map_eq
    (markovBanditStackMeasure P x) (markovChainMeasure P (x i))
    (fun omega ↦ omega i) (measurable_pi_apply i)
    (map_markovBanditStackMeasure_arm P x i)
    (integrable_markovChain_eval_of_discounted
      P hr hα0 hint (x i) u).abs

lemma integral_comp_of_map_eq
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) (nu : Measure B) (g : A → B)
    (hg : Measurable g) (hmap : mu.map g = nu)
    {f : B → ℝ} (hf : Integrable f nu) :
    (∫ x, f (g x) ∂mu) = ∫ y, f y ∂nu := by
  have hfmap : Integrable f (mu.map g) := by rwa [hmap]
  calc
    (∫ x, f (g x) ∂mu) = ∫ y, f y ∂mu.map g :=
      (integral_map hg.aemeasurable hfmap.1).symm
    _ = _ := by rw [hmap]

theorem integral_discountedAbsoluteRewardValue_stack_arm
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : Fin k → S) (i : Fin k) (u : ℕ) :
    (∫ omega, discountedAbsoluteRewardValue P r α (omega i u)
        ∂markovBanditStackMeasure P x) =
      ∫ path, discountedAbsoluteRewardValue P r α (path u)
        ∂markovChainMeasure P (x i) := by
  exact integral_comp_of_map_eq
    (markovBanditStackMeasure P x) (markovChainMeasure P (x i))
    (fun omega ↦ omega i) (measurable_pi_apply i)
    (map_markovBanditStackMeasure_arm P x i)
    (integrable_discountedAbsoluteRewardValue_along_markov
      P hr hα0 hint (x i) u).1

theorem integral_abs_reward_stack_arm
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : Fin k → S) (i : Fin k) (u : ℕ) :
    (∫ omega, |r (omega i u)| ∂markovBanditStackMeasure P x) =
      ∫ path, |r (path u)| ∂markovChainMeasure P (x i) := by
  exact integral_comp_of_map_eq
    (markovBanditStackMeasure P x) (markovChainMeasure P (x i))
    (fun omega ↦ omega i) (measurable_pi_apply i)
    (map_markovBanditStackMeasure_arm P x i)
    (integrable_markovChain_eval_of_discounted
      P hr hα0 hint (x i) u).abs

theorem summable_discounted_integral_abs_reward_markov
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    Summable (fun u ↦ α ^ u *
      ∫ path, |r (path u)| ∂markovChainMeasure P x) := by
  let mu := markovChainMeasure P x
  let F : ℕ → (ℕ → S) → ℝ := fun u path ↦ α ^ u * |r (path u)|
  have hFmeas : ∀ u, AEStronglyMeasurable (F u) mu := by
    intro u
    have hm : Measurable (fun path : ℕ → S ↦
        α ^ u * |r (path u)|) := by fun_prop
    exact hm.aestronglyMeasurable
  have hsumAE : ∀ᵐ path ∂mu, Summable (fun u ↦ F u path) := by
    simpa [F, mu] using
      ae_summable_discountedAbsSeries_multiarm P hr hα0.le hint x
  have hfull : Integrable (fun path ↦ ∑' u, F u path) mu := by
    have habs : Measurable (fun y ↦ |r y|) := by fun_prop
    have hintAbs : DiscountedRewardIntegrable P (fun y ↦ |r y|) α := by
      intro y
      simpa only [abs_abs] using hint y
    refine (integrable_discountedStoppedSum P habs hα0.le hintAbs x
        (top_isTrajStoppingTime (S := S))).congr
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    simp [F, discountedStoppedSum]
  have hhas : HasSum (fun u ↦ ∫ path, F u path ∂mu)
      (∫ path, ∑' u, F u path ∂mu) := by
    apply hasSum_integral_of_dominated_convergence F hFmeas
    · intro u
      exact Filter.Eventually.of_forall fun path ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (pow_nonneg hα0.le u) (abs_nonneg _))]
    · exact hsumAE
    · exact hfull
    · filter_upwards [hsumAE] with path hpath
      exact hpath.hasSum
  apply hhas.summable.congr
  intro u
  rw [integral_const_mul]

theorem tendsto_alpha_pow_integral_absoluteValue_prefix_stack_arm
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : Fin k → S) (i : Fin k) :
    Filter.Tendsto (fun N ↦ α ^ N *
      ∫ omega, ∑ u ∈ Finset.range (N + 1),
        discountedAbsoluteRewardValue P r α (omega i u)
        ∂markovBanditStackMeasure P x) Filter.atTop (nhds 0) := by
  let b : ℕ → ℝ := fun u ↦ α ^ u *
    ∫ path, discountedAbsoluteRewardValue P r α (path u)
      ∂markovChainMeasure P (x i)
  have hb : Filter.Tendsto b Filter.atTop (nhds 0) := by
    have ht := tendsto_discounted_absoluteRewardFuture_integral_zero
      P hr hα0 hint (x i)
    have heq : b = fun u ↦ α ^ u *
        ∫ path, discountedAbsoluteRewardFuture r α u path
          ∂markovChainMeasure P (x i) := by
      funext u
      dsimp [b]
      rw [(integrable_discountedAbsoluteRewardValue_along_markov
        P hr hα0 hint (x i) u).2]
    rwa [heq]
  have hconv := tendsto_geometric_reverse_convolution_zero
    hα0.le hα1 hb
  apply hconv.congr'
  filter_upwards with N
  rw [integral_finset_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [integral_discountedAbsoluteRewardValue_stack_arm
      P hr hα0 hint x i u]
    dsimp [b]
    have huN : u ≤ N := Nat.le_of_lt_succ (Finset.mem_range.1 hu)
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  · intro u hu
    exact integrable_discountedAbsoluteRewardValue_stack_arm
      P hr hα0 hint x i u

theorem tendsto_alpha_pow_integral_absReward_prefix_stack_arm
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : Fin k → S) (i : Fin k) :
    Filter.Tendsto (fun N ↦ α ^ N *
      ∫ omega, ∑ v ∈ Finset.range N, |r (omega i (v + 1))|
        ∂markovBanditStackMeasure P x) Filter.atTop (nhds 0) := by
  let b : ℕ → ℝ := fun v ↦
    ∫ path, |r (path (v + 1))| ∂markovChainMeasure P (x i)
  have hfull := summable_discounted_integral_abs_reward_markov
    P hr hα0 hint (x i)
  have hshift : Summable (fun v ↦ α ^ (v + 1) * b v) := by
    exact (summable_nat_add_iff 1).2 hfull
  have hb : Summable (fun v ↦ α ^ v * b v) := by
    have hs := hshift.mul_left α⁻¹
    refine hs.congr fun v ↦ ?_
    rw [pow_succ, show α ^ v * α * b v = α * (α ^ v * b v) by ring, ← mul_assoc,
      inv_mul_cancel₀ hα0.ne', one_mul]
  have hprefix := summable_pow_mul_prefix_of_summable
    hα0.le hα1 (fun v ↦ integral_nonneg fun path ↦ abs_nonneg _) hb
  have ht := hprefix.tendsto_atTop_zero
  apply ht.congr'
  filter_upwards with N
  rw [integral_finset_sum]
  · rw [Finset.mul_sum, ← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    rw [integral_abs_reward_stack_arm
      P hr hα0 hint x i (v + 1)]
  · intro v hv
    exact integrable_abs_reward_stack_arm
      P hr hα0 hint x i (v + 1)

theorem tendsto_alpha_pow_integral_initial_absoluteValue_stack_arm
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : Fin k → S) (i : Fin k) :
    Filter.Tendsto (fun N ↦ α ^ N *
      ∫ omega, discountedAbsoluteRewardValue P r α (omega i 0)
        ∂markovBanditStackMeasure P x) Filter.atTop (nhds 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hα0.le hα1
  simpa using hp.mul_const
    (∫ omega, discountedAbsoluteRewardValue P r α (omega i 0)
      ∂markovBanditStackMeasure P x)

theorem tendsto_alpha_pow_integral_retirementEnvelope_arm
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : Fin k → S) (i : Fin k) :
    Filter.Tendsto (fun N ↦ α ^ N *
      ∫ omega,
        ((∑ u ∈ Finset.range (N + 1),
            discountedAbsoluteRewardValue P r α (omega i u)) +
          (∑' t : ℕ, α ^ t) *
            (discountedAbsoluteRewardValue P r α (omega i 0) +
              ∑ v ∈ Finset.range N, |r (omega i (v + 1))|))
        ∂markovBanditStackMeasure P x) Filter.atTop (nhds 0) := by
  let M := markovBanditStackMeasure P x
  let G : ℝ := ∑' t : ℕ, α ^ t
  let A : ℕ → MarkovBanditStackSpace k S → ℝ := fun N omega ↦
    ∑ u ∈ Finset.range (N + 1),
      discountedAbsoluteRewardValue P r α (omega i u)
  let B : MarkovBanditStackSpace k S → ℝ := fun omega ↦
    discountedAbsoluteRewardValue P r α (omega i 0)
  let C : ℕ → MarkovBanditStackSpace k S → ℝ := fun N omega ↦
    ∑ v ∈ Finset.range N, |r (omega i (v + 1))|
  have hAint : ∀ N, Integrable (A N) M := by
    intro N
    apply MeasureTheory.integrable_finsetSum
    intro u hu
    exact integrable_discountedAbsoluteRewardValue_stack_arm
      P hr hα0 hint x i u
  have hBint : Integrable B M :=
    integrable_discountedAbsoluteRewardValue_stack_arm
      P hr hα0 hint x i 0
  have hCint : ∀ N, Integrable (C N) M := by
    intro N
    apply MeasureTheory.integrable_finsetSum
    intro v hv
    exact integrable_abs_reward_stack_arm P hr hα0 hint x i (v + 1)
  have hAt := tendsto_alpha_pow_integral_absoluteValue_prefix_stack_arm
    P hr hα0 hα1 hint x i
  have hBt := tendsto_alpha_pow_integral_initial_absoluteValue_stack_arm
    P hr hα0 hα1 hint x i
  have hCt := tendsto_alpha_pow_integral_absReward_prefix_stack_arm
    P hr hα0 hα1 hint x i
  have ht : Filter.Tendsto (fun N ↦
      α ^ N * (∫ omega, A N omega ∂M) +
        G * (α ^ N * (∫ omega, B omega ∂M) +
          α ^ N * (∫ omega, C N omega ∂M)))
      Filter.atTop (nhds 0) := by
    have hBC := hBt.add hCt
    have hG : Filter.Tendsto (fun N ↦ G *
        (α ^ N * (∫ omega, B omega ∂M) +
          α ^ N * (∫ omega, C N omega ∂M)))
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hBC)
    simpa [A, B, C, M, G] using hAt.add hG
  apply ht.congr'
  filter_upwards with N
  change α ^ N * (∫ omega, A N omega ∂M) +
      G * (α ^ N * (∫ omega, B omega ∂M) +
        α ^ N * (∫ omega, C N omega ∂M)) =
    α ^ N * ∫ omega, A N omega + G * (B omega + C N omega) ∂M
  symm
  have hadd :
      (∫ omega, A N omega + G * (B omega + C N omega) ∂M) =
        (∫ omega, A N omega ∂M) +
          ∫ omega, G * (B omega + C N omega) ∂M := by
    exact integral_add (hAint N)
      ((hBint.add (hCint N)).const_mul G)
  calc
    α ^ N * ∫ omega, A N omega + G * (B omega + C N omega) ∂M =
        α ^ N * ((∫ omega, A N omega ∂M) +
          ∫ omega, G * (B omega + C N omega) ∂M) := by
      rw [hadd]
    _ = _ := by
      rw [integral_const_mul, integral_add hBint (hCint N)]
      ring

theorem tendsto_alpha_pow_integral_markovBanditRetirementEnvelope
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : Fin k → S) :
    Filter.Tendsto (fun N ↦ α ^ N *
      ∫ omega, markovBanditRetirementEnvelope P r α omega N
        ∂markovBanditStackMeasure P x) Filter.atTop (nhds 0) := by
  let M := markovBanditStackMeasure P x
  let F : ℕ → Fin k → MarkovBanditStackSpace k S → ℝ := fun N i omega ↦
    ((∑ u ∈ Finset.range (N + 1),
        discountedAbsoluteRewardValue P r α (omega i u)) +
      (∑' t : ℕ, α ^ t) *
        (discountedAbsoluteRewardValue P r α (omega i 0) +
          ∑ v ∈ Finset.range N, |r (omega i (v + 1))|))
  have hFint : ∀ N i, Integrable (F N i) M := by
    intro N i
    apply Integrable.add
    · apply MeasureTheory.integrable_finsetSum
      intro u hu
      exact integrable_discountedAbsoluteRewardValue_stack_arm
        P hr hα0 hint x i u
    · apply Integrable.const_mul
      exact (integrable_discountedAbsoluteRewardValue_stack_arm
        P hr hα0 hint x i 0).add (by
          apply MeasureTheory.integrable_finsetSum
          intro v hv
          exact integrable_abs_reward_stack_arm P hr hα0 hint x i (v + 1))
  have hFi : ∀ i : Fin k, Filter.Tendsto (fun N ↦ α ^ N *
      ∫ omega, F N i omega ∂M) Filter.atTop (nhds 0) := by
    intro i
    exact tendsto_alpha_pow_integral_retirementEnvelope_arm
      P hr hα0 hα1 hint x i
  have hsum : ∀ s : Finset (Fin k), Filter.Tendsto
      (fun N ↦ ∑ i ∈ s, α ^ N * ∫ omega, F N i omega ∂M)
      Filter.atTop (nhds 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (nhds 0))
    | @insert i s hi ih =>
        simpa [Finset.sum_insert hi] using (hFi i).add ih
  have hall := hsum Finset.univ
  apply hall.congr'
  filter_upwards with N
  change (∑ i : Fin k, α ^ N * ∫ omega, F N i omega ∂M) =
    α ^ N * ∫ omega, ∑ i : Fin k, F N i omega ∂M
  rw [integral_finset_sum]
  · rw [Finset.mul_sum]
  · intro i hi
    exact hFint N i

end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal


theorem solution
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : BanditAlgorithm.DiscountedRewardIntegrable P r α)
    (x : Fin k → S) :
    let absoluteValue := fun y : S ↦
      ∫ path, ∑' t : ℕ, α ^ t * |r (path t)|
        ∂BanditAlgorithm.markovChainMeasure P y
    let envelope := fun (N : ℕ) (ω : Fin k → ℕ → S) ↦ ∑ i : Fin k,
      ((∑ u ∈ Finset.range (N + 1), absoluteValue (ω i u)) +
        (∑' t : ℕ, α ^ t) *
          (absoluteValue (ω i 0) +
            ∑ v ∈ Finset.range N, |r (ω i (v + 1))|))
    let stackMeasure : Measure (Fin k → ℕ → S) :=
      Measure.pi (fun i ↦ BanditAlgorithm.markovChainMeasure P (x i))
    Filter.Tendsto (fun N ↦ α ^ N * ∫ ω, envelope N ω ∂stackMeasure)
      Filter.atTop (nhds 0) := by
  change Filter.Tendsto (fun N ↦ α ^ N *
      ∫ ω, BanditAlgorithm.markovBanditRetirementEnvelope P r α ω N
        ∂BanditAlgorithm.markovBanditStackMeasure P x)
    Filter.atTop (nhds 0)
  exact BanditAlgorithm.tendsto_alpha_pow_integral_markovBanditRetirementEnvelope
    P hr hα0 hα1 hint x
