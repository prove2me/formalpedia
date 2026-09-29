-- Prove2me | solution 1 for BanditAlgorithm.summable_discounted_markovBanditRoundReward
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T17:24:55.371801+00:00
-- url     : https://prove2.me/submissions/6d95ccbc-65dd-412f-ab13-9970d9dcae8e

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

lemma top_isTrajStoppingTime
    {S : Type*} [MeasurableSpace S] :
    IsTrajStoppingTime (fun _ : ℕ → S ↦ (⊤ : ℕ∞)) := by
  intro n
  convert MeasurableSet.empty
  ext ω
  simp

lemma integral_markovChain_eval_zero
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (f : S → ℝ) (hf : Measurable f) (x : S) :
    (∫ ω, f (ω 0) ∂markovChainMeasure P x) = f x := by
  rw [markovChainMeasure_eq_traj_zero]
  let x₀ : (j : Finset.Iic 0) → S := fun _ ↦ x
  have hsm :
      AEStronglyMeasurable
        (fun ω : ℕ → S ↦ f (ω 0))
        (Kernel.traj (markovChainStep P) 0 x₀) :=
    (hf.comp (measurable_pi_apply 0)).aestronglyMeasurable
  rw [Kernel.integral_traj
    (X := fun _ : ℕ ↦ S) (κ := markovChainStep P) x₀ hsm]
  rw [show (fun ω : ℕ → S ↦
      f ((Function.updateFinset ω (Finset.Iic 0) x₀) 0)) =
        fun _ ↦ f x by
      funext ω
      simp [Function.updateFinset, x₀]]
  simp

lemma integrable_markovChain_eval_zero
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (f : S → ℝ) (hf : Measurable f) (x : S) :
    Integrable (fun ω : ℕ → S ↦ f (ω 0))
      (markovChainMeasure P x) := by
  let x₀ : (j : Finset.Iic 0) → S := fun _ ↦ x
  have hmap :
      Integrable f
        ((markovChainMeasure P x).map
          (fun ω : ℕ → S ↦ ω 0)) := by
    rw [markovChainMeasure_eq_traj_zero]
    rw [map_traj_eval_eq_trajectoryStateMarginal P 0 0 x₀]
    rw [trajectoryStateMarginal_zero]
    exact integrable_dirac' hf.stronglyMeasurable (by simp)
  exact (integrable_map_measure
    hf.aestronglyMeasurable
    (measurable_pi_apply 0).aemeasurable).1 hmap

end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm



@[simp] lemma currentHistoryPrevailingCharge_zero
    {k : ℕ} {S : Type*} (g : S → ℝ)
    (h : MarkovBanditHistory k S 0) (i : Fin k) :
    currentHistoryPrevailingCharge g 0 h i = g (h.2 i) :=
  rfl

private lemma measurable_discountedAbsSeries_multiarm
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

private lemma integrable_discountedAbsSeries_multiarm
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    Integrable (fun ω : ℕ → S ↦
      ∑' t : ℕ, α ^ t * |r (ω t)|)
      (markovChainMeasure P x) := by
  have habs : Measurable (fun y ↦ |r y|) := by
    fun_prop
  have hintAbs : DiscountedRewardIntegrable P
      (fun y ↦ |r y|) α := by
    intro y
    simpa only [abs_abs] using hint y
  refine (integrable_discountedStoppedSum P habs hα0 hintAbs x
      (top_isTrajStoppingTime (S := S))).congr
    (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp [discountedStoppedSum]

theorem measurable_discountedAbsoluteRewardValue
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} :
    Measurable (discountedAbsoluteRewardValue P r α) := by
  rw [show discountedAbsoluteRewardValue P r α =
      fun x ↦ ∫ ω, (∑' t : ℕ, α ^ t * |r (ω t)|)
        ∂markovChainKernel P x by
    funext x
    rw [markovChainKernel_apply]
    rfl]
  exact (measurable_discountedAbsSeries_multiarm hr).stronglyMeasurable
    |>.integral_kernel.measurable

lemma map_markovChainMeasure_eval_one
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    (markovChainMeasure P x).map (fun ω : ℕ → S ↦ ω 1) =
      P x := by
  let x₀ : (j : Finset.Iic 0) → S := fun _ ↦ x
  rw [markovChainMeasure_eq_traj_zero]
  rw [map_traj_eval_eq_trajectoryStateMarginal P 0 1 x₀]
  rw [show 1 = 0 + 1 by omega]
  rw [trajectoryStateMarginal_succ,
    trajectoryStateMarginal_zero]
  exact Measure.dirac_bind P.measurable x

lemma integrable_discountedAbsoluteRewardValue_kernel
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    Integrable (discountedAbsoluteRewardValue P r α) (P x) := by
  have htraj :=
    (integrable_discountedAbsoluteRewardValue_along_markov
      P hr hα0 hint x 1).1
  have hmap : Integrable (discountedAbsoluteRewardValue P r α)
      ((markovChainMeasure P x).map (fun ω : ℕ → S ↦ ω 1)) :=
    (integrable_map_measure
      (measurable_discountedAbsoluteRewardValue P hr).aestronglyMeasurable
      (measurable_pi_apply 1).aemeasurable).2 htraj
  rwa [map_markovChainMeasure_eval_one P x] at hmap

theorem discountedAbsoluteRewardValue_bellman
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    discountedAbsoluteRewardValue P r α x =
      |r x| + α * ∫ y,
        discountedAbsoluteRewardValue P r α y ∂P x := by
  let μ := markovChainMeasure P x
  let R : (ℕ → S) → ℝ := fun ω ↦
    ∑' t : ℕ, α ^ t * |r (ω t)|
  let F : (ℕ → S) → ℝ :=
    discountedAbsoluteRewardFuture r α 1
  have hRint : Integrable R μ := by
    simpa [R, μ] using integrable_discountedAbsSeries_multiarm
      P hr hα0.le hint x
  have hFint : Integrable F μ := by
    simpa [F, μ] using
      integrable_discountedAbsoluteRewardFuture_markov
        P hr hα0 hint x 1
  have hsplit : R =ᵐ[μ] fun ω ↦ |r (ω 0)| + α * F ω := by
    filter_upwards
      [ae_summable_discountedAbsSeries_multiarm
        P hr hα0.le hint x]
      with ω hsum
    dsimp [R, F, discountedAbsoluteRewardFuture]
    have hs := hsum.sum_add_tsum_nat_add 1
    calc
      (∑' t : ℕ, α ^ t * |r (ω t)|) =
          (∑ t ∈ Finset.range 1, α ^ t * |r (ω t)|) +
            ∑' t : ℕ, α ^ (t + 1) * |r (ω (t + 1))| := hs.symm
      _ = |r (ω 0)| + α *
          ∑' t : ℕ, α ^ t * |r (ω (1 + t))| := by
        simp only [Finset.sum_range_one, pow_zero, one_mul]
        congr 1
        rw [← tsum_mul_left]
        apply tsum_congr
        intro t
        rw [pow_succ]
        rw [Nat.add_comm t 1]
        ring
  have hEval :=
    (integrable_discountedAbsoluteRewardValue_along_markov
      P hr hα0 hint x 1).2
  have hmapInt :
      (∫ ω, discountedAbsoluteRewardValue P r α (ω 1) ∂μ) =
        ∫ y, discountedAbsoluteRewardValue P r α y ∂P x := by
    rw [← map_markovChainMeasure_eval_one P x]
    rw [integral_map (measurable_pi_apply 1).aemeasurable
      (measurable_discountedAbsoluteRewardValue P hr).aestronglyMeasurable]
  change (∫ ω, R ω ∂μ) =
    |r x| + α * ∫ y,
      discountedAbsoluteRewardValue P r α y ∂P x
  rw [integral_congr_ae hsplit]
  rw [integral_add
    (integrable_markovChain_eval_zero P (fun y ↦ |r y|) (by fun_prop) x)
    (hFint.const_mul α)]
  rw [integral_markovChain_eval_zero P (fun y ↦ |r y|) (by fun_prop) x]
  rw [integral_const_mul]
  rw [← hEval, hmapInt]

noncomputable def markovBanditAbsoluteStatePotential
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ)
    (h : MarkovBanditHistory k S n) : ℝ :=
  ∑ i : Fin k, discountedAbsoluteRewardValue P r α (h.2 i)

lemma measurable_markovBanditAbsoluteStatePotential
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} :
    Measurable (markovBanditAbsoluteStatePotential
      (k := k) (n := n) P r α) := by
  refine Finset.measurable_sum Finset.univ ?_
  intro i hi
  exact (measurable_discountedAbsoluteRewardValue P hr).comp
    ((measurable_pi_apply i).comp measurable_snd)

lemma markovBanditAbsoluteStatePotential_nonneg
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) {α : ℝ} (hα0 : 0 ≤ α)
    (h : MarkovBanditHistory k S n) :
    0 ≤ markovBanditAbsoluteStatePotential P r α h := by
  apply Finset.sum_nonneg
  intro i hi
  dsimp [discountedAbsoluteRewardValue]
  exact integral_nonneg fun ω ↦
    tsum_nonneg fun t ↦
      mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)

lemma markovBanditAbsoluteStatePotential_update
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ)
    (h : MarkovBanditHistory k S n) (a : Fin k) (y : S) :
    markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, a), Function.update h.2 a y) =
      (∑ i ∈ Finset.univ.erase a,
        discountedAbsoluteRewardValue P r α (h.2 i)) +
        discountedAbsoluteRewardValue P r α y := by
  rw [markovBanditAbsoluteStatePotential]
  let F : Fin k → ℝ := fun i ↦
    discountedAbsoluteRewardValue P r α
      ((Function.update h.2 a y) i)
  change (∑ i, F i) = _
  rw [← Finset.sum_erase_add Finset.univ F (Finset.mem_univ a)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hia : i ≠ a := Finset.ne_of_mem_erase hi
    simp [F, Function.update, hia]
  · simp [F, Function.update]

lemma integrable_markovBanditAbsoluteStatePotential_step_action
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (h : MarkovBanditHistory k S n) (a : Fin k) :
    Integrable (fun y ↦
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, a), Function.update h.2 a y))
      (P (h.2 a)) := by
  rw [show (fun y ↦
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, a), Function.update h.2 a y)) =
    fun y ↦
      (∑ i ∈ Finset.univ.erase a,
        discountedAbsoluteRewardValue P r α (h.2 i)) +
      discountedAbsoluteRewardValue P r α y by
    funext y
    exact markovBanditAbsoluteStatePotential_update P r α h a y]
  exact (integrable_const _).add
    (integrable_discountedAbsoluteRewardValue_kernel
      P hr hα0 hint (h.2 a))

lemma measurable_markovBanditAbsoluteStatePotential_step
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (h : MarkovBanditHistory k S n) :
    Measurable (fun q : Fin k × S ↦
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, q.1),
          Function.update h.2 q.1 q.2)) := by
  apply measurable_from_prod_countable_right
  intro a
  rw [show (fun y ↦
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, a), Function.update h.2 a y)) =
    fun y ↦
      (∑ i ∈ Finset.univ.erase a,
        discountedAbsoluteRewardValue P r α (h.2 i)) +
      discountedAbsoluteRewardValue P r α y by
    funext y
    exact markovBanditAbsoluteStatePotential_update P r α h a y]
  exact measurable_const.add
    (measurable_discountedAbsoluteRewardValue P hr)

lemma integrable_markovBanditAbsoluteStatePotential_step
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S)
    (h : MarkovBanditHistory k S n) :
    Integrable (fun q : Fin k × S ↦
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, q.1),
          Function.update h.2 q.1 q.2))
      (markovBanditStepKernel P π n h) := by
  rw [markovBanditStepKernel]
  apply (ProbabilityTheory.integrable_compProd_iff
    (measurable_markovBanditAbsoluteStatePotential_step
      P hr h).aestronglyMeasurable).2
  constructor
  · filter_upwards with a
    rw [Kernel.comap_apply]
    exact integrable_markovBanditAbsoluteStatePotential_step_action
      P hr hα0 hint h a
  · exact Integrable.of_finite

lemma markovBanditAbsoluteStatePotential_eq_inactive_add
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ)
    (h : MarkovBanditHistory k S n) (a : Fin k) :
    markovBanditAbsoluteStatePotential P r α h =
      (∑ i ∈ Finset.univ.erase a,
        discountedAbsoluteRewardValue P r α (h.2 i)) +
      discountedAbsoluteRewardValue P r α (h.2 a) := by
  rw [markovBanditAbsoluteStatePotential]
  exact (Finset.sum_erase_add Finset.univ _
    (Finset.mem_univ a)).symm

lemma integral_markovBanditAbsoluteStatePotential_step_action
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (h : MarkovBanditHistory k S n) (a : Fin k) :
    (∫ y,
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, a), Function.update h.2 a y)
      ∂P (h.2 a)) =
      (∑ i ∈ Finset.univ.erase a,
        discountedAbsoluteRewardValue P r α (h.2 i)) +
      ∫ y, discountedAbsoluteRewardValue P r α y ∂P (h.2 a) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun y ↦
    markovBanditAbsoluteStatePotential_update P r α h a y)]
  rw [integral_add (integrable_const _)
    (integrable_discountedAbsoluteRewardValue_kernel
      P hr hα0 hint (h.2 a))]
  simp

lemma integral_markovBanditAbsoluteStatePotential_step_action_le
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (h : MarkovBanditHistory k S n) (a : Fin k) :
    (∫ y,
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, a), Function.update h.2 a y)
      ∂P (h.2 a)) ≤
      (1 + α⁻¹) * markovBanditAbsoluteStatePotential P r α h := by
  rw [integral_markovBanditAbsoluteStatePotential_step_action
    P hr hα0 hint h a]
  have hbell := discountedAbsoluteRewardValue_bellman
    P hr hα0 hint (h.2 a)
  have hsplit := markovBanditAbsoluteStatePotential_eq_inactive_add
    P r α h a
  have hA0 : 0 ≤ discountedAbsoluteRewardValue P r α (h.2 a) := by
    dsimp [discountedAbsoluteRewardValue]
    exact integral_nonneg fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0.le t) (abs_nonneg _)
  have hI0 : 0 ≤ ∫ y,
      discountedAbsoluteRewardValue P r α y ∂P (h.2 a) :=
    integral_nonneg fun y ↦ by
      dsimp [discountedAbsoluteRewardValue]
      exact integral_nonneg fun ω ↦
        tsum_nonneg fun t ↦
          mul_nonneg (pow_nonneg hα0.le t) (abs_nonneg _)
  have hrest0 : 0 ≤ ∑ i ∈ Finset.univ.erase a,
      discountedAbsoluteRewardValue P r α (h.2 i) := by
    apply Finset.sum_nonneg
    intro i hi
    dsimp [discountedAbsoluteRewardValue]
    exact integral_nonneg fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0.le t) (abs_nonneg _)
  field_simp
  nlinarith [abs_nonneg (r (h.2 a))]

lemma integral_markovBanditAbsoluteStatePotential_step_le
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S)
    (h : MarkovBanditHistory k S n) :
    (∫ q,
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, q.1), Function.update h.2 q.1 q.2)
      ∂markovBanditStepKernel P π n h) ≤
      (1 + α⁻¹) * markovBanditAbsoluteStatePotential P r α h := by
  have hInt := integrable_markovBanditAbsoluteStatePotential_step
    P hr hα0 hint π h
  rw [markovBanditStepKernel]
  rw [ProbabilityTheory.integral_compProd hInt]
  let J : Fin k → ℝ := fun a ↦
    ∫ y,
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, a), Function.update h.2 a y)
      ∂(P.comap
        (fun p : MarkovBanditHistory k S n × Fin k ↦ p.1.2 p.2)
        measurable_currentArmState) (h, a)
  have hleft : Integrable J (π.select n h) :=
    Integrable.of_finite
  have hright : Integrable (fun _ : Fin k ↦
      (1 + α⁻¹) * markovBanditAbsoluteStatePotential P r α h)
      (π.select n h) := integrable_const _
  change (∫ a, J a ∂(π.select n h)) ≤
    (1 + α⁻¹) * markovBanditAbsoluteStatePotential P r α h
  calc
    (∫ a, J a ∂(π.select n h)) ≤
        ∫ _a : Fin k,
          (1 + α⁻¹) * markovBanditAbsoluteStatePotential P r α h
          ∂(π.select n h) := by
      apply integral_mono hleft hright
      intro a
      dsimp [J]
      exact integral_markovBanditAbsoluteStatePotential_step_action_le
        P hr hα0 hint h a
    _ = _ := by simp

theorem integrable_markovBanditAbsoluteStatePotential
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    ∀ n : ℕ,
      Integrable (markovBanditAbsoluteStatePotential P r α)
        (markovBanditMeasure P π x n) := by
  intro n
  induction n with
  | zero =>
      rw [markovBanditMeasure]
      exact integrable_dirac'
        (measurable_markovBanditAbsoluteStatePotential
          (n := 0) P hr).stronglyMeasurable (by simp)
  | succ n ih =>
      rw [markovBanditMeasure]
      apply (integrable_map_measure
        (measurable_markovBanditAbsoluteStatePotential
          (n := n + 1) P hr).aestronglyMeasurable
        measurable_markovBanditSnoc.aemeasurable).2
      let μ := markovBanditMeasure P π x n
      let K := markovBanditStepKernel P π n
      let F : MarkovBanditHistory k S n × (Fin k × S) → ℝ :=
        fun p ↦ markovBanditAbsoluteStatePotential P r α
          (Fin.snoc p.1.1 (p.1.2, p.2.1),
            Function.update p.1.2 p.2.1 p.2.2)
      have hFmeas : Measurable F :=
        (measurable_markovBanditAbsoluteStatePotential
          (n := n + 1) P hr).comp measurable_markovBanditSnoc
      apply (Measure.integrable_compProd_iff
        hFmeas.aestronglyMeasurable).2
      constructor
      · exact Filter.Eventually.of_forall fun h ↦
          integrable_markovBanditAbsoluteStatePotential_step
            P hr hα0 hint π h
      · let C : ℝ := 1 + α⁻¹
        let G : MarkovBanditHistory k S n → ℝ := fun h ↦
          ∫ q, ‖F (h, q)‖ ∂K h
        have hGsm : StronglyMeasurable G := by
          exact hFmeas.norm.stronglyMeasurable
            |>.integral_kernel_prod_right'
        have hCB : Integrable (fun h : MarkovBanditHistory k S n ↦
            C * markovBanditAbsoluteStatePotential P r α h) μ := by
          exact ih.const_mul C
        apply hCB.mono' hGsm.aestronglyMeasurable
        exact Filter.Eventually.of_forall fun h ↦ by
          rw [show G h =
              ∫ q, F (h, q) ∂K h by
            dsimp [G]
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun q ↦ by
              change |F (h, q)| = F (h, q)
              exact abs_of_nonneg
                (markovBanditAbsoluteStatePotential_nonneg
                  P r hα0.le _)]
          dsimp [C, K, F]
          rw [abs_of_nonneg (integral_nonneg fun q ↦
            markovBanditAbsoluteStatePotential_nonneg P r hα0.le _)]
          exact integral_markovBanditAbsoluteStatePotential_step_le
            P hr hα0 hint π h

lemma integrable_compProd_fst_of_integrable
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [SFinite μ]
    (K : Kernel A B) [IsMarkovKernel K]
    {f : A → ℝ} (hf : Integrable f μ) :
    Integrable (fun p : A × B ↦ f p.1) (μ.compProd K) := by
  have hfmap : Integrable f (Measure.map Prod.fst (μ.compProd K)) := by
    change Integrable f ((μ.compProd K).fst)
    rw [Measure.fst_compProd]
    exact hf
  simpa [Function.comp_def] using
    (integrable_map_measure hfmap.1 measurable_fst.aemeasurable).1 hfmap

lemma abs_reward_le_discountedAbsoluteRewardValue
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α) (y : S) :
    |r y| ≤ discountedAbsoluteRewardValue P r α y := by
  rw [discountedAbsoluteRewardValue_bellman P hr hα0 hint y]
  have hI : 0 ≤ ∫ z,
      discountedAbsoluteRewardValue P r α z ∂P y :=
    integral_nonneg fun z ↦ by
      unfold discountedAbsoluteRewardValue
      exact integral_nonneg fun ω ↦
        tsum_nonneg fun t ↦
          mul_nonneg (pow_nonneg hα0.le t) (abs_nonneg _)
  nlinarith

lemma measurable_selectedCurrentReward_step
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    {r : S → ℝ} (hr : Measurable r) :
    Measurable (fun p : MarkovBanditHistory k S n × (Fin k × S) ↦
      r (p.1.2 p.2.1)) := by
  exact hr.comp (measurable_currentArmState.comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))

lemma integrable_selectedCurrentReward_step
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    Integrable (fun p : MarkovBanditHistory k S n × (Fin k × S) ↦
      r (p.1.2 p.2.1))
      ((markovBanditMeasure P π x n).compProd
        (markovBanditStepKernel P π n)) := by
  have hB := integrable_compProd_fst_of_integrable
    (markovBanditMeasure P π x n) (markovBanditStepKernel P π n)
    (integrable_markovBanditAbsoluteStatePotential
      P hr hα0 hint π x n)
  apply hB.mono'
    (measurable_selectedCurrentReward_step hr).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p ↦
    le_trans
      (abs_reward_le_discountedAbsoluteRewardValue
        P hr hα0 hint (p.1.2 p.2.1))
      (Finset.single_le_sum
        (f := fun i : Fin k ↦
          discountedAbsoluteRewardValue P r α (p.1.2 i))
        (fun i _ ↦ by
          unfold discountedAbsoluteRewardValue
          exact integral_nonneg fun ω ↦
            tsum_nonneg fun t ↦
              mul_nonneg (pow_nonneg hα0.le t) (abs_nonneg _))
        (Finset.mem_univ p.2.1))

lemma integrable_integral_measure_compProd
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [SFinite μ]
    (K : Kernel A B) [IsSFiniteKernel K]
    {f : A × B → ℝ} (hf : Integrable f (μ.compProd K)) :
    Integrable (fun a ↦ ∫ b, f (a, b) ∂K a) μ := by
  rw [Measure.compProd] at hf
  simpa using hf.integral_compProd

lemma sum_range_pow_mul_sub_succ
    (α : ℝ) (V : ℕ → ℝ) : ∀ N : ℕ,
    (∑ n ∈ Finset.range N,
      α ^ n * (V n - α * V (n + 1))) =
        V 0 - α ^ N * V N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

lemma measurable_markovBanditRoundReward_integrand
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    {r : S → ℝ} (hr : Measurable r) :
    Measurable (fun h : MarkovBanditHistory k S (n + 1) ↦
      r ((h.1 (Fin.last n)).1 ((h.1 (Fin.last n)).2))) := by
  have hjoint : Measurable
      (fun q : (Fin k → S) × Fin k ↦ r (q.1 q.2)) :=
    measurable_from_prod_countable_left fun a ↦ by
      exact hr.comp (measurable_pi_apply a)
  exact hjoint.comp
    ((measurable_fst.comp
        ((measurable_pi_apply (Fin.last n)).comp measurable_fst)).prodMk
      (measurable_snd.comp
        ((measurable_pi_apply (Fin.last n)).comp measurable_fst)))

lemma markovBanditRoundReward_eq_step_integral
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    markovBanditRoundReward P r π x n =
      ∫ p, r (p.1.2 p.2.1)
        ∂(markovBanditMeasure P π x n).compProd
          (markovBanditStepKernel P π n) := by
  rw [markovBanditRoundReward, markovBanditMeasure]
  rw [integral_map measurable_markovBanditSnoc.aemeasurable
    (measurable_markovBanditRoundReward_integrand hr).aestronglyMeasurable]
  congr 1
  funext p
  simp [Fin.snoc]

lemma alpha_mul_integral_markovBanditAbsoluteStatePotential_step_action_le
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (h : MarkovBanditHistory k S n) (a : Fin k) :
    α * (∫ y,
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, a), Function.update h.2 a y)
      ∂P (h.2 a)) ≤
      markovBanditAbsoluteStatePotential P r α h - |r (h.2 a)| := by
  let R : ℝ := ∑ i ∈ Finset.univ.erase a,
    discountedAbsoluteRewardValue P r α (h.2 i)
  let A : ℝ := discountedAbsoluteRewardValue P r α (h.2 a)
  let I : ℝ := ∫ y,
    discountedAbsoluteRewardValue P r α y ∂P (h.2 a)
  have hstep := integral_markovBanditAbsoluteStatePotential_step_action
    P hr hα0 hint h a
  have hsplit := markovBanditAbsoluteStatePotential_eq_inactive_add
    P r α h a
  have hbell := discountedAbsoluteRewardValue_bellman
    P hr hα0 hint (h.2 a)
  have hR : 0 ≤ R := by
    apply Finset.sum_nonneg
    intro i hi
    unfold discountedAbsoluteRewardValue
    exact integral_nonneg fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0.le t) (abs_nonneg _)
  change (∫ y,
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, a), Function.update h.2 a y)
      ∂P (h.2 a)) = R + I at hstep
  change markovBanditAbsoluteStatePotential P r α h = R + A at hsplit
  change A = |r (h.2 a)| + α * I at hbell
  rw [hstep, hsplit, hbell]
  nlinarith

lemma integrable_abs_selectedCurrentReward_step_history
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    (π : MarkovBanditPolicy k S)
    (h : MarkovBanditHistory k S n) :
    Integrable (fun q : Fin k × S ↦ |r (h.2 q.1)|)
      (markovBanditStepKernel P π n h) := by
  rw [markovBanditStepKernel]
  have hm : Measurable (fun q : Fin k × S ↦ |r (h.2 q.1)|) :=
    (measurable_of_finite fun a : Fin k ↦ |r (h.2 a)|).comp
      measurable_fst
  apply (ProbabilityTheory.integrable_compProd_iff
    hm.aestronglyMeasurable).2
  constructor
  · filter_upwards with a
    rw [Kernel.comap_apply]
    exact integrable_const _
  · exact Integrable.of_finite

lemma alpha_mul_integral_markovBanditAbsoluteStatePotential_step_le
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S)
    (h : MarkovBanditHistory k S n) :
    α * (∫ q,
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, q.1), Function.update h.2 q.1 q.2)
      ∂markovBanditStepKernel P π n h) ≤
      markovBanditAbsoluteStatePotential P r α h -
        ∫ q, |r (h.2 q.1)| ∂markovBanditStepKernel P π n h := by
  have hB := integrable_markovBanditAbsoluteStatePotential_step
    P hr hα0 hint π h
  have hR := integrable_abs_selectedCurrentReward_step_history
    P hr π h
  rw [markovBanditStepKernel] at hB hR ⊢
  rw [ProbabilityTheory.integral_compProd hB,
    ProbabilityTheory.integral_compProd hR]
  simp only [Kernel.comap_apply]
  let J : Fin k → ℝ := fun a ↦
    ∫ y, markovBanditAbsoluteStatePotential P r α
      (Fin.snoc h.1 (h.2, a), Function.update h.2 a y)
      ∂P (h.2 a)
  have hJ : Integrable J (π.select n h) := by
    simpa [J, Kernel.comap_apply] using hB.integral_compProd
  have hRfin : Integrable (fun a : Fin k ↦ |r (h.2 a)|)
      (π.select n h) := Integrable.of_finite
  simp
  change α * (∫ a, J a ∂π.select n h) ≤
    markovBanditAbsoluteStatePotential P r α h -
      ∫ a, |r (h.2 a)| ∂π.select n h
  calc
    α * (∫ a, J a ∂π.select n h) =
        ∫ a, α * J a ∂π.select n h := by
      rw [integral_const_mul]
    _ ≤ ∫ a, markovBanditAbsoluteStatePotential P r α h -
          |r (h.2 a)| ∂π.select n h := by
      apply integral_mono (hJ.const_mul α)
        ((integrable_const _).sub hRfin)
      intro a
      exact alpha_mul_integral_markovBanditAbsoluteStatePotential_step_action_le
        P hr hα0 hα1 hint h a
    _ = _ := by
      rw [integral_sub (integrable_const _) hRfin]
      simp

noncomputable def markovBanditExpectedAbsoluteStatePotential
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ)
    (π : MarkovBanditPolicy k S) (x : Fin k → S)
    (n : ℕ) : ℝ :=
  ∫ h, markovBanditAbsoluteStatePotential P r α h
    ∂markovBanditMeasure P π x n

noncomputable def markovBanditRoundAbsoluteReward
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (π : MarkovBanditPolicy k S)
    (x : Fin k → S) (n : ℕ) : ℝ :=
  ∫ p, |r (p.1.2 p.2.1)|
    ∂(markovBanditMeasure P π x n).compProd
      (markovBanditStepKernel P π n)

theorem alpha_mul_expectedAbsoluteStatePotential_succ_le
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) (n : ℕ) :
    α * markovBanditExpectedAbsoluteStatePotential P r α π x (n + 1) ≤
      markovBanditExpectedAbsoluteStatePotential P r α π x n -
        markovBanditRoundAbsoluteReward P r π x n := by
  let μ := markovBanditMeasure P π x n
  let K := markovBanditStepKernel P π n
  let B : MarkovBanditHistory k S n → ℝ :=
    markovBanditAbsoluteStatePotential P r α
  let Q : MarkovBanditHistory k S n × (Fin k × S) → ℝ := fun p ↦
    markovBanditAbsoluteStatePotential P r α
      (Fin.snoc p.1.1 (p.1.2, p.2.1),
        Function.update p.1.2 p.2.1 p.2.2)
  let R : MarkovBanditHistory k S n × (Fin k × S) → ℝ := fun p ↦
    |r (p.1.2 p.2.1)|
  have hB : Integrable B μ :=
    integrable_markovBanditAbsoluteStatePotential
      P hr hα0 hint π x n
  have hQ : Integrable Q (μ.compProd K) := by
    have hs := integrable_markovBanditAbsoluteStatePotential
      P hr hα0 hint π x (n + 1)
    rw [markovBanditMeasure] at hs
    simpa [Q, Function.comp_def] using
      (integrable_map_measure hs.1
        measurable_markovBanditSnoc.aemeasurable).1 hs
  have hR : Integrable R (μ.compProd K) := by
    simpa [R, Real.norm_eq_abs] using
      (integrable_selectedCurrentReward_step
        P hr hα0 hint π x).abs
  have hQc : Integrable (fun h ↦ ∫ q, Q (h, q) ∂K h) μ :=
    integrable_integral_measure_compProd μ K hQ
  have hRc : Integrable (fun h ↦ ∫ q, R (h, q) ∂K h) μ :=
    integrable_integral_measure_compProd μ K hR
  have hpoint : ∀ h : MarkovBanditHistory k S n,
      α * (∫ q, Q (h, q) ∂K h) ≤
        B h - ∫ q, R (h, q) ∂K h := by
    intro h
    exact alpha_mul_integral_markovBanditAbsoluteStatePotential_step_le
      P hr hα0 hα1 hint π h
  have hmono : α * (∫ h, ∫ q, Q (h, q) ∂K h ∂μ) ≤
      (∫ h, B h ∂μ) - ∫ h, ∫ q, R (h, q) ∂K h ∂μ := by
    rw [← integral_const_mul]
    rw [← integral_sub hB hRc]
    apply integral_mono (hQc.const_mul α) (hB.sub hRc)
    exact hpoint
  have hnext :
      markovBanditExpectedAbsoluteStatePotential P r α π x (n + 1) =
        ∫ p, Q p ∂μ.compProd K := by
    rw [markovBanditExpectedAbsoluteStatePotential,
      markovBanditMeasure]
    rw [integral_map measurable_markovBanditSnoc.aemeasurable
      (by
        exact (integrable_markovBanditAbsoluteStatePotential
          P hr hα0 hint π x (n + 1)).1)]
  rw [hnext, markovBanditExpectedAbsoluteStatePotential,
    markovBanditRoundAbsoluteReward]
  rw [Measure.integral_compProd hQ, Measure.integral_compProd hR]
  exact hmono

lemma markovBanditExpectedAbsoluteStatePotential_nonneg
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) {α : ℝ} (hα0 : 0 < α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) (n : ℕ) :
    0 ≤ markovBanditExpectedAbsoluteStatePotential P r α π x n := by
  exact integral_nonneg fun h ↦
    markovBanditAbsoluteStatePotential_nonneg P r hα0.le h

lemma markovBanditRoundAbsoluteReward_nonneg
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (π : MarkovBanditPolicy k S)
    (x : Fin k → S) (n : ℕ) :
    0 ≤ markovBanditRoundAbsoluteReward P r π x n :=
  integral_nonneg fun _ ↦ abs_nonneg _

lemma markovBanditExpectedAbsoluteStatePotential_zero
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (α : ℝ)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    markovBanditExpectedAbsoluteStatePotential P r α π x 0 =
      ∑ i : Fin k, discountedAbsoluteRewardValue P r α (x i) := by
  rw [markovBanditExpectedAbsoluteStatePotential, markovBanditMeasure]
  rw [integral_dirac' _ _
    (measurable_markovBanditAbsoluteStatePotential P hr).stronglyMeasurable]
  rfl

theorem finite_sum_markovBanditRoundAbsoluteReward_le_initial
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      α ^ n * markovBanditRoundAbsoluteReward P r π x n) ≤
      ∑ i : Fin k, discountedAbsoluteRewardValue P r α (x i) := by
  let B : ℕ → ℝ := fun n ↦
    markovBanditExpectedAbsoluteStatePotential P r α π x n
  calc
    (∑ n ∈ Finset.range N,
        α ^ n * markovBanditRoundAbsoluteReward P r π x n) ≤
        ∑ n ∈ Finset.range N,
          α ^ n * (B n - α * B (n + 1)) := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hα0.le n)
      have hs := alpha_mul_expectedAbsoluteStatePotential_succ_le
        P hr hα0 hα1 hint π x n
      dsimp [B]
      linarith
    _ = B 0 - α ^ N * B N :=
      sum_range_pow_mul_sub_succ α B N
    _ ≤ B 0 := by
      have hBN : 0 ≤ B N :=
        markovBanditExpectedAbsoluteStatePotential_nonneg
          P r hα0 π x N
      have hp : 0 ≤ α ^ N := pow_nonneg hα0.le N
      nlinarith
    _ = _ := markovBanditExpectedAbsoluteStatePotential_zero
      P hr α π x

theorem summable_discounted_markovBanditRoundAbsoluteReward
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    Summable (fun n ↦
      α ^ n * markovBanditRoundAbsoluteReward P r π x n) := by
  apply summable_of_sum_range_le
  · intro n
    exact mul_nonneg (pow_nonneg hα0.le n)
      (markovBanditRoundAbsoluteReward_nonneg P r π x n)
  · intro N
    exact finite_sum_markovBanditRoundAbsoluteReward_le_initial
      P hr hα0 hα1 hint π x N

lemma abs_markovBanditRoundReward_le
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) (n : ℕ) :
    |markovBanditRoundReward P r π x n| ≤
      markovBanditRoundAbsoluteReward P r π x n := by
  rw [markovBanditRoundReward_eq_step_integral
    P hr hα0 hint π x]
  exact abs_integral_le_integral_abs

theorem summable_discounted_markovBanditRoundReward
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    Summable (fun n ↦ α ^ n * markovBanditRoundReward P r π x n) := by
  apply Summable.of_norm_bounded
    (summable_discounted_markovBanditRoundAbsoluteReward
      P hr hα0 hα1 hint π x)
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hα0.le]
  exact mul_le_mul_of_nonneg_left
    (abs_markovBanditRoundReward_le P hr hα0 hint π x n)
    (pow_nonneg hα0.le n)

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




end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm



end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm



end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal


theorem solution
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : BanditAlgorithm.DiscountedRewardIntegrable P r α)
    (π : BanditAlgorithm.MarkovBanditPolicy k S) (x : Fin k → S) :
    Summable (fun n ↦ α ^ n *
      BanditAlgorithm.markovBanditRoundReward P r π x n) := by
  exact BanditAlgorithm.summable_discounted_markovBanditRoundReward
    P hr hα0 hα1 hint π x
