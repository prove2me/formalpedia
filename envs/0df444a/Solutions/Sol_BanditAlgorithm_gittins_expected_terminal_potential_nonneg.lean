-- Prove2me | solution 1 for BanditAlgorithm.gittins_expected_terminal_potential_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T17:13:52.6958+00:00
-- url     : https://prove2.me/submissions/fb768c2c-789e-464e-9f1c-d87e4793c863

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

noncomputable def finiteRetirementTime
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ) :
    ℕ → ℕ → (ℕ → S) → ℕ
  | _, 0, _ => 0
  | b, n + 1, ω =>
      if 0 < r (ω b) - γ +
          α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P (ω b)
      then 1 + finiteRetirementTime P r α γ (b + 1) n ω
      else 0

noncomputable def finiteRetirementSegment
    {S : Type*} (α : ℝ) (q : S → ℝ)
    (b m : ℕ) (ω : ℕ → S) : ℝ :=
  ∑ j ∈ Finset.range m, α ^ j * q (ω (b + j))

lemma finiteRetirementSegment_succ
    {S : Type*} (α : ℝ) (q : S → ℝ)
    (b m : ℕ) (ω : ℕ → S) :
    finiteRetirementSegment α q b (m + 1) ω =
      q (ω b) + α * finiteRetirementSegment α q (b + 1) m ω := by
  rw [finiteRetirementSegment, finiteRetirementSegment]
  simp only [Finset.sum_range_succ']
  simp only [pow_zero, one_mul]
  have htail :
      (∑ k ∈ Finset.range m,
        α ^ (k + 1) * q (ω (b + (k + 1)))) =
        α * ∑ j ∈ Finset.range m, α ^ j * q (ω (b + 1 + j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_succ]
    ring_nf
  rw [htail]
  simp [add_comm]

lemma measurable_finiteRetirementTime
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) {r : S → ℝ} (hr : Measurable r)
    (α γ : ℝ) :
    ∀ b n, Measurable (finiteRetirementTime P r α γ b n) := by
  intro b n
  induction n generalizing b with
  | zero =>
      simp [finiteRetirementTime]
  | succ n ih =>
      have hv :=
        measurable_gittinsFiniteRetirementValue P hr α γ n
      have hcont : Measurable (fun x ↦
          r x - γ +
            α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x) := by
        exact (hr.sub measurable_const).add
          (measurable_const.mul
            hv.stronglyMeasurable.integral_kernel.measurable)
      rw [show finiteRetirementTime P r α γ b (n + 1) =
          fun ω ↦
            if 0 < r (ω b) - γ +
                α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P (ω b)
            then 1 + finiteRetirementTime P r α γ (b + 1) n ω
            else 0 by rfl]
      apply Measurable.ite
      · exact measurableSet_lt measurable_const
          (hcont.comp (measurable_pi_apply b))
      · fun_prop
      · exact measurable_const

private lemma measurable_trajectory_eval_le
    {S : Type*} [MeasurableSpace S] {b N : ℕ} (hbN : b ≤ N) :
    Measurable[trajectoryFiltration S N] (fun ω : ℕ → S ↦ ω b) := by
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → S)) :=
    Filtration.piLE (X := fun _ : ℕ ↦ S)
  have hadapt :
      Adapted ℱ (fun t (ω : ℕ → S) ↦ ω t) := by
    intro t
    dsimp [ℱ]
    rw [Filtration.piLE_eq_comap_frestrictLe]
    change Measurable[MeasurableSpace.comap
      (fun (ω : ℕ → S) (i : Finset.Iic t) ↦ ω i.1) inferInstance]
        ((fun z : (i : Finset.Iic t) → S ↦
            z ⟨t, Finset.mem_Iic.2 le_rfl⟩) ∘
          (fun (ω : ℕ → S) (i : Finset.Iic t) ↦ ω i.1))
    exact (measurable_pi_apply _).comp (comap_measurable _)
  have hmeas : Measurable[ℱ N] (fun ω : ℕ → S ↦ ω b) :=
    hadapt.measurable_le hbN
  have hfil : ℱ N = trajectoryFiltration S N := by
    dsimp [ℱ, trajectoryFiltration]
    rw [Filtration.piLE_eq_comap_frestrictLe]
    rfl
  rwa [hfil] at hmeas

lemma measurableSet_finiteRetirementTime_le
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) {r : S → ℝ} (hr : Measurable r)
    (α γ : ℝ) :
    ∀ b n m,
      MeasurableSet[trajectoryFiltration S (b + m)]
        {ω | finiteRetirementTime P r α γ b n ω ≤ m} := by
  intro b n
  induction n generalizing b with
  | zero =>
      intro m
      convert MeasurableSet.univ
      ext ω
      simp [finiteRetirementTime]
  | succ n ih =>
      intro m
      let c : S → ℝ := fun x ↦
        r x - γ +
          α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x
      have hc : Measurable c := by
        exact (hr.sub measurable_const).add
          (measurable_const.mul
            ((measurable_gittinsFiniteRetirementValue P hr α γ n).stronglyMeasurable
              |>.integral_kernel.measurable))
      cases m with
      | zero =>
          have heval :
              Measurable[trajectoryFiltration S (b + 0)]
                (fun ω : ℕ → S ↦ c (ω b)) :=
            hc.comp (measurable_trajectory_eval_le (by omega))
          have hpos :
              MeasurableSet[trajectoryFiltration S (b + 0)]
                {ω : ℕ → S | 0 < c (ω b)} :=
            measurableSet_lt measurable_const heval
          convert hpos.compl using 1
          ext ω
          simp [finiteRetirementTime, c]
      | succ m =>
          have heval :
              Measurable[trajectoryFiltration S (b + (m + 1))]
                (fun ω : ℕ → S ↦ c (ω b)) :=
            hc.comp (measurable_trajectory_eval_le (by omega))
          have hpos :
              MeasurableSet[trajectoryFiltration S (b + (m + 1))]
                {ω : ℕ → S | 0 < c (ω b)} :=
            measurableSet_lt measurable_const heval
          have hrec :
              MeasurableSet[trajectoryFiltration S (b + (m + 1))]
                {ω |
                  finiteRetirementTime P r α γ (b + 1) n ω ≤ m} := by
            have heq : b + 1 + m = b + (m + 1) := by omega
            rw [← heq]
            exact ih (b + 1) m
          have hset :
              {ω | finiteRetirementTime P r α γ b (n + 1) ω ≤ m + 1} =
                {ω : ℕ → S | 0 < c (ω b)}ᶜ ∪
                  ({ω : ℕ → S | 0 < c (ω b)} ∩
                    {ω |
                      finiteRetirementTime P r α γ (b + 1) n ω ≤ m}) := by
            ext ω
            simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff,
              Set.mem_inter_iff]
            rw [show finiteRetirementTime P r α γ b (n + 1) ω =
                if 0 < c (ω b) then
                  1 + finiteRetirementTime P r α γ (b + 1) n ω
                else 0 by rfl]
            by_cases hp : 0 < c (ω b)
            · simp [hp]
              omega
            · simp [hp]
          rw [hset]
          exact hpos.compl.union (hpos.inter hrec)

lemma finiteRetirementTime_le
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ) :
    ∀ b n ω, finiteRetirementTime P r α γ b n ω ≤ n := by
  intro b n
  induction n generalizing b with
  | zero =>
      intro ω
      simp [finiteRetirementTime]
  | succ n ih =>
      intro ω
      rw [show finiteRetirementTime P r α γ b (n + 1) ω =
          if 0 < r (ω b) - γ +
              α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P (ω b)
          then 1 + finiteRetirementTime P r α γ (b + 1) n ω
          else 0 by rfl]
      split_ifs
      · simpa [Nat.add_comm] using
          Nat.add_le_add_left (ih (b + 1) ω) 1
      · exact Nat.zero_le _

lemma finiteRetirementSegment_time_succ
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ)
    (b n : ℕ) (ω : ℕ → S) :
    finiteRetirementSegment α (fun x ↦ r x - γ) b
        (finiteRetirementTime P r α γ b (n + 1) ω) ω =
      if 0 < r (ω b) - γ +
          α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P (ω b)
      then
        r (ω b) - γ +
          α * finiteRetirementSegment α (fun x ↦ r x - γ) (b + 1)
            (finiteRetirementTime P r α γ (b + 1) n ω) ω
      else 0 := by
  rw [show finiteRetirementTime P r α γ b (n + 1) ω =
      if 0 < r (ω b) - γ +
          α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P (ω b)
      then 1 + finiteRetirementTime P r α γ (b + 1) n ω
      else 0 by rfl]
  split_ifs with h
  · rw [show 1 + finiteRetirementTime P r α γ (b + 1) n ω =
        finiteRetirementTime P r α γ (b + 1) n ω + 1 by omega]
    rw [finiteRetirementSegment_succ]
  · simp [finiteRetirementSegment]

private lemma updateFinset_apply_of_lt
    {S : Type*} (ω : ℕ → S) {b i : ℕ} (hbi : b < i)
    (x₀ : (j : Finset.Iic b) → S) :
    Function.updateFinset ω (Finset.Iic b) x₀ i = ω i := by
  unfold Function.updateFinset
  split_ifs with hi
  · have hib : i ≤ b := Finset.mem_Iic.mp hi
    omega
  · rfl

private lemma finiteRetirementTime_updateFinset_before
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ)
    (ω : ℕ → S) {b c n : ℕ} (hbc : b < c)
    (x₀ : (j : Finset.Iic b) → S) :
    finiteRetirementTime P r α γ c n
        (Function.updateFinset ω (Finset.Iic b) x₀) =
      finiteRetirementTime P r α γ c n ω := by
  induction n generalizing c with
  | zero =>
      simp [finiteRetirementTime]
  | succ n ih =>
      rw [show finiteRetirementTime P r α γ c (n + 1)
            (Function.updateFinset ω (Finset.Iic b) x₀) =
          if 0 < r ((Function.updateFinset ω (Finset.Iic b) x₀) c) - γ +
              α * ∫ y, gittinsFiniteRetirementValue P r α γ n y
                ∂P ((Function.updateFinset ω (Finset.Iic b) x₀) c)
          then 1 + finiteRetirementTime P r α γ (c + 1) n
            (Function.updateFinset ω (Finset.Iic b) x₀)
          else 0 by rfl]
      rw [show finiteRetirementTime P r α γ c (n + 1) ω =
          if 0 < r (ω c) - γ +
              α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P (ω c)
          then 1 + finiteRetirementTime P r α γ (c + 1) n ω
          else 0 by rfl]
      rw [updateFinset_apply_of_lt ω hbc x₀]
      by_cases hc : 0 < r (ω c) - γ +
          α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P (ω c)
      · rw [if_pos hc, if_pos hc]
        exact congrArg (fun z ↦ 1 + z)
          (ih (c := c + 1) (by omega))
      · rw [if_neg hc, if_neg hc]

private lemma finiteRetirementSegment_updateFinset_before
    {S : Type*} (α : ℝ) (q : S → ℝ)
    (ω : ℕ → S) {b c m : ℕ} (hbc : b < c)
    (x₀ : (j : Finset.Iic b) → S) :
    finiteRetirementSegment α q c m
        (Function.updateFinset ω (Finset.Iic b) x₀) =
      finiteRetirementSegment α q c m ω := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [updateFinset_apply_of_lt]
  omega

private lemma integral_partialTraj_succ_current
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (f : S → ℝ) (hf : StronglyMeasurable f)
    (b : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (∫ (x : (j : Finset.Iic (b + 1)) → S),
        f (x ⟨b + 1, Finset.mem_Iic.2 le_rfl⟩)
        ∂Kernel.partialTraj (X := fun _ : ℕ ↦ S)
          (markovChainStep P) b (b + 1) x₀) =
      ∫ y, f y ∂P (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  let e : ((j : Finset.Iic (b + 1)) → S) → S :=
    fun x ↦ x ⟨b + 1, Finset.mem_Iic.2 le_rfl⟩
  have hmapK :=
    Kernel.map_partialTraj_succ_self
      (X := fun _ : ℕ ↦ S) (κ := markovChainStep P) b
  have hmap :=
    congrArg
      (fun K : Kernel ((j : Finset.Iic b) → S) S ↦ K x₀)
      hmapK
  try dsimp only at hmap
  rw [Kernel.map_apply _ (by fun_prop)] at hmap
  rw [← MeasureTheory.integral_map_of_stronglyMeasurable
    (by fun_prop : Measurable e) hf]
  rw [hmap]
  rfl

noncomputable def finiteRetirementPayoff
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ)
    (b n : ℕ) (ω : ℕ → S) : ℝ :=
  finiteRetirementSegment α (fun x ↦ r x - γ) b
    (finiteRetirementTime P r α γ b n ω) ω

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

private lemma sum_range_ite_lt
    {m n : ℕ} (hmn : m ≤ n) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range n, if j < m then f j else 0) =
      ∑ j ∈ Finset.range m, f j := by
  symm
  calc
    (∑ j ∈ Finset.range m, f j) =
        ∑ j ∈ Finset.range m, if j < m then f j else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [Finset.mem_range] at hj
          simp [hj]
    _ = ∑ j ∈ Finset.range n, if j < m then f j else 0 := by
      apply Finset.sum_subset (Finset.range_mono hmn)
      intro j hjn hjm
      simp only [Finset.mem_range, not_lt] at hjm
      simp [hjm]

lemma finiteRetirementPayoff_eq_sum_range
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ)
    (b n : ℕ) (ω : ℕ → S) :
    finiteRetirementPayoff P r α γ b n ω =
      ∑ j ∈ Finset.range n,
        if j < finiteRetirementTime P r α γ b n ω then
          α ^ j * (r (ω (b + j)) - γ)
        else 0 := by
  rw [finiteRetirementPayoff, finiteRetirementSegment]
  exact (sum_range_ite_lt
    (finiteRetirementTime_le P r α γ b n ω)
    (fun j ↦ α ^ j * (r (ω (b + j)) - γ))).symm

lemma integrable_finiteRetirementPayoff
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) {r : S → ℝ} (hr : Measurable r)
    (α γ : ℝ) (b n : ℕ)
    (μ : Measure (ℕ → S))
    [IsFiniteMeasure μ]
    (hcoord : ∀ j < n, Integrable (fun ω ↦ r (ω (b + j))) μ) :
    Integrable (finiteRetirementPayoff P r α γ b n) μ := by
  rw [show finiteRetirementPayoff P r α γ b n =
      fun ω ↦ ∑ j ∈ Finset.range n,
        if j < finiteRetirementTime P r α γ b n ω then
          α ^ j * (r (ω (b + j)) - γ)
        else 0 by
          funext ω
          exact finiteRetirementPayoff_eq_sum_range P r α γ b n ω]
  apply integrable_finset_sum
  intro j hj
  have hset : MeasurableSet
      {ω : ℕ → S | j < finiteRetirementTime P r α γ b n ω} :=
    measurableSet_lt measurable_const
      (measurable_finiteRetirementTime P hr α γ b n)
  have hterm : Integrable
      (fun ω : ℕ → S ↦ α ^ j * (r (ω (b + j)) - γ)) μ :=
    ((hcoord j (Finset.mem_range.1 hj)).sub
      (integrable_const γ)).const_mul (α ^ j)
  rw [show (fun ω : ℕ → S ↦
      if j < finiteRetirementTime P r α γ b n ω then
        α ^ j * (r (ω (b + j)) - γ)
      else 0) =
      {ω : ℕ → S | j < finiteRetirementTime P r α γ b n ω}.indicator
        (fun ω ↦ α ^ j * (r (ω (b + j)) - γ)) by
          funext ω
          simp only [Set.indicator, Set.mem_setOf_eq, Pi.zero_apply]]
  exact hterm.indicator hset

lemma discountedStoppedSum_finiteRetirementForcedTime
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ)
    (n : ℕ) (ω : ℕ → S) :
    discountedStoppedSum α (fun y ↦ r y - γ)
        (fun ω ↦
          ((1 + finiteRetirementTime P r α γ 1 n ω : ℕ) : ℕ∞)) ω =
      r (ω 0) - γ +
        α * finiteRetirementPayoff P r α γ 1 n ω := by
  rw [discountedStoppedSum_coe_nat]
  rw [show 1 + finiteRetirementTime P r α γ 1 n ω =
      finiteRetirementTime P r α γ 1 n ω + 1 by omega]
  rw [finiteRetirementSegment_succ]
  rfl

lemma markovChainMeasure_eq_traj_zero
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    markovChainMeasure P x =
      Kernel.traj (markovChainStep P) 0
        (fun _ : Finset.Iic 0 ↦ x) := by
  rw [← markovChainKernel_apply, markovChainKernel, Kernel.comap_apply]

set_option maxHeartbeats 800000 in
theorem integral_finiteRetirementPayoff
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (α γ : ℝ)
    (hpay : ∀ b n (x₀ : (j : Finset.Iic b) → S),
      Integrable (finiteRetirementPayoff P r α γ b n)
        (Kernel.traj (markovChainStep P) b x₀))
    (hpaySucc : ∀ b n (x₀ : (j : Finset.Iic b) → S),
      Integrable (finiteRetirementPayoff P r α γ (b + 1) n)
        (Kernel.traj (markovChainStep P) b x₀)) :
    ∀ b n (x₀ : (j : Finset.Iic b) → S),
      (∫ ω, finiteRetirementPayoff P r α γ b n ω
          ∂Kernel.traj (markovChainStep P) b x₀) =
        gittinsFiniteRetirementValue P r α γ n
          (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  intro b n
  induction n generalizing b with
  | zero =>
      intro x₀
      simp [finiteRetirementPayoff, finiteRetirementTime,
        finiteRetirementSegment, gittinsFiniteRetirementValue]
  | succ n ih =>
      intro x₀
      let x : S := x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩
      let c : ℝ :=
        r x - γ +
          α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x
      have hfix :
          (∫ ω, finiteRetirementPayoff P r α γ b (n + 1) ω
              ∂Kernel.traj (markovChainStep P) b x₀) =
            ∫ ω,
              finiteRetirementPayoff P r α γ b (n + 1)
                (Function.updateFinset ω (Finset.Iic b) x₀)
              ∂Kernel.traj (markovChainStep P) b x₀ :=
        Kernel.integral_traj
          (X := fun _ : ℕ ↦ S) (κ := markovChainStep P)
          x₀ (hpay b (n + 1) x₀).1
      rw [hfix]
      by_cases hc : 0 < c
      · have hpath :
            (fun ω ↦
              finiteRetirementPayoff P r α γ b (n + 1)
                (Function.updateFinset ω (Finset.Iic b) x₀)) =
              fun ω ↦
                r x - γ +
                  α * finiteRetirementPayoff P r α γ (b + 1) n ω := by
          funext ω
          rw [finiteRetirementPayoff,
            finiteRetirementSegment_time_succ]
          have hxb :
              Function.updateFinset ω (Finset.Iic b) x₀ b = x := by
            simp [Function.updateFinset, x]
          rw [hxb]
          rw [if_pos hc]
          rw [finiteRetirementPayoff]
          rw [finiteRetirementTime_updateFinset_before
            P r α γ ω (by omega) x₀]
          rw [finiteRetirementSegment_updateFinset_before
            α (fun z ↦ r z - γ) ω (by omega) x₀]
        rw [hpath]
        rw [integral_add
          (integrable_const (r x - γ))
          ((hpaySucc b n x₀).const_mul α)]
        rw [integral_const_mul]
        have hdecomp :=
          Kernel.integral_traj_partialTraj
            (X := fun _ : ℕ ↦ S) (κ := markovChainStep P)
            (Nat.le_succ b)
            (hpaySucc b n x₀)
        have hchild :
            (∫ ω, finiteRetirementPayoff P r α γ (b + 1) n ω
                ∂Kernel.traj (markovChainStep P) b x₀) =
              ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x := by
          rw [← hdecomp]
          have hinner :
              (fun z : (j : Finset.Iic (b + 1)) → S ↦
                ∫ ω, finiteRetirementPayoff P r α γ (b + 1) n ω
                  ∂Kernel.traj (markovChainStep P) (b + 1) z) =
                fun z ↦
                  gittinsFiniteRetirementValue P r α γ n
                    (z ⟨b + 1, Finset.mem_Iic.2 le_rfl⟩) := by
            funext z
            exact ih (b + 1) z
          rw [hinner]
          exact integral_partialTraj_succ_current P
            (gittinsFiniteRetirementValue P r α γ n)
            (measurable_gittinsFiniteRetirementValue P hr α γ n).stronglyMeasurable
            b x₀
        rw [hchild]
        simpa [gittinsFiniteRetirementValue, x, c] using
          (max_eq_right hc.le).symm
      · have hpath :
            (fun ω ↦
              finiteRetirementPayoff P r α γ b (n + 1)
                (Function.updateFinset ω (Finset.Iic b) x₀)) =
              fun _ ↦ 0 := by
          funext ω
          rw [finiteRetirementPayoff,
            finiteRetirementSegment_time_succ]
          have hxb :
              Function.updateFinset ω (Finset.Iic b) x₀ b = x := by
            simp [Function.updateFinset, x]
          rw [hxb]
          rw [if_neg hc]
        rw [hpath]
        have hc' : c ≤ 0 := le_of_not_gt hc
        simpa [gittinsFiniteRetirementValue, x, c] using hc'

theorem integral_finiteRetirementPayoff_next
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (α γ : ℝ)
    (hpay : ∀ b n (x₀ : (j : Finset.Iic b) → S),
      Integrable (finiteRetirementPayoff P r α γ b n)
        (Kernel.traj (markovChainStep P) b x₀))
    (hpaySucc : ∀ b n (x₀ : (j : Finset.Iic b) → S),
      Integrable (finiteRetirementPayoff P r α γ (b + 1) n)
        (Kernel.traj (markovChainStep P) b x₀))
    (b n : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (∫ ω, finiteRetirementPayoff P r α γ (b + 1) n ω
        ∂Kernel.traj (markovChainStep P) b x₀) =
      ∫ y, gittinsFiniteRetirementValue P r α γ n y
        ∂P (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  have hdecomp :=
    Kernel.integral_traj_partialTraj
      (X := fun _ : ℕ ↦ S) (κ := markovChainStep P)
      (Nat.le_succ b)
      (hpaySucc b n x₀)
  rw [← hdecomp]
  have hinner :
      (fun z : (j : Finset.Iic (b + 1)) → S ↦
        ∫ ω, finiteRetirementPayoff P r α γ (b + 1) n ω
          ∂Kernel.traj (markovChainStep P) (b + 1) z) =
        fun z ↦
          gittinsFiniteRetirementValue P r α γ n
            (z ⟨b + 1, Finset.mem_Iic.2 le_rfl⟩) := by
    funext z
    exact integral_finiteRetirementPayoff P hr α γ hpay hpaySucc
      (b + 1) n z
  rw [hinner]
  exact integral_partialTraj_succ_current P
    (gittinsFiniteRetirementValue P r α γ n)
    (measurable_gittinsFiniteRetirementValue P hr α γ n).stronglyMeasurable
    b x₀

theorem integral_discountedStoppedSum_finiteRetirementForcedTime
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (α γ : ℝ)
    (hpay : ∀ b n (x₀ : (j : Finset.Iic b) → S),
      Integrable (finiteRetirementPayoff P r α γ b n)
        (Kernel.traj (markovChainStep P) b x₀))
    (hpaySucc : ∀ b n (x₀ : (j : Finset.Iic b) → S),
      Integrable (finiteRetirementPayoff P r α γ (b + 1) n)
        (Kernel.traj (markovChainStep P) b x₀))
    (n : ℕ) (x : S) :
    (∫ ω, discountedStoppedSum α (fun y ↦ r y - γ)
        (fun ω ↦
          ((1 + finiteRetirementTime P r α γ 1 n ω : ℕ) : ℕ∞)) ω
        ∂markovChainMeasure P x) =
      r x - γ +
        α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x := by
  rw [markovChainMeasure_eq_traj_zero]
  rw [show (fun ω ↦ discountedStoppedSum α (fun y ↦ r y - γ)
      (fun ω ↦
        ((1 + finiteRetirementTime P r α γ 1 n ω : ℕ) : ℕ∞)) ω) =
      fun ω ↦ r (ω 0) - γ +
        α * finiteRetirementPayoff P r α γ 1 n ω by
          funext ω
          exact discountedStoppedSum_finiteRetirementForcedTime
            P r α γ n ω]
  let x₀ : (j : Finset.Iic 0) → S := fun _ ↦ x
  have hr0 : Measurable (fun ω : ℕ → S ↦ r (ω 0)) :=
    hr.comp (measurable_pi_apply 0)
  have hsm :
      AEStronglyMeasurable
        (fun ω : ℕ → S ↦
          r (ω 0) - γ +
            α * finiteRetirementPayoff P r α γ 1 n ω)
        (Kernel.traj (markovChainStep P) 0 x₀) :=
    (hr0.aestronglyMeasurable.sub aestronglyMeasurable_const).add
      ((hpaySucc 0 n x₀).1.const_mul α)
  rw [Kernel.integral_traj
    (X := fun _ : ℕ ↦ S) (κ := markovChainStep P) x₀ hsm]
  have hupdated :
      (fun ω : ℕ → S ↦
        r ((Function.updateFinset ω (Finset.Iic 0) x₀) 0) - γ +
          α * finiteRetirementPayoff P r α γ 1 n
            (Function.updateFinset ω (Finset.Iic 0) x₀)) =
        fun ω ↦
          r x - γ + α * finiteRetirementPayoff P r α γ 1 n ω := by
    funext ω
    have hpayoff :
        finiteRetirementPayoff P r α γ 1 n
            (Function.updateFinset ω (Finset.Iic 0) x₀) =
          finiteRetirementPayoff P r α γ 1 n ω := by
      rw [finiteRetirementPayoff]
      rw [finiteRetirementTime_updateFinset_before
        P r α γ ω (by omega : 0 < 1) x₀]
      rw [finiteRetirementSegment_updateFinset_before
        α (fun z ↦ r z - γ) ω (by omega : 0 < 1) x₀]
      rfl
    rw [hpayoff]
    simp [Function.updateFinset, x₀]
  rw [hupdated]
  rw [integral_add (integrable_const (r x - γ))
    ((hpaySucc 0 n x₀).const_mul α)]
  rw [integral_const_mul]
  rw [integral_finiteRetirementPayoff_next P hr α γ hpay hpaySucc
    0 n x₀]
  simp [x₀]

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

lemma integrable_traj_eval_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    Integrable (fun ω : ℕ → S ↦ r (ω (b + t)))
      (Kernel.traj (markovChainStep P) b x₀) := by
  have hmap :
      Integrable r
        ((markovChainMeasure P
          (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩)).map
            (fun ω : ℕ → S ↦ ω t)) := by
    exact (integrable_map_measure hr.aestronglyMeasurable
      (measurable_pi_apply t).aemeasurable).2
        (integrable_markovChain_eval_of_discounted
          P hr hα0 hint
          (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) t)
  rw [← map_traj_eval_eq_map_markovChainMeasure_eval P b t x₀] at hmap
  exact hmap.comp_measurable (measurable_pi_apply (b + t))

lemma integrable_finiteRetirementPayoff_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (b n : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    Integrable (finiteRetirementPayoff P r α γ b n)
      (Kernel.traj (markovChainStep P) b x₀) := by
  apply integrable_finiteRetirementPayoff P hr α γ b n
  intro j hj
  exact integrable_traj_eval_of_discounted
    P hr hα0 hint b j x₀

lemma integrable_finiteRetirementPayoff_next_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (b n : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    Integrable (finiteRetirementPayoff P r α γ (b + 1) n)
      (Kernel.traj (markovChainStep P) b x₀) := by
  apply integrable_finiteRetirementPayoff P hr α γ (b + 1) n
  intro j hj
  simpa [Nat.add_assoc, Nat.add_comm 1 j] using
    (integrable_traj_eval_of_discounted
      P hr hα0 hint b (j + 1) x₀)

theorem integral_discountedStoppedSum_finiteRetirementForcedTime_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (n : ℕ) (x : S) :
    (∫ ω, discountedStoppedSum α (fun y ↦ r y - γ)
        (fun ω ↦
          ((1 + finiteRetirementTime P r α γ 1 n ω : ℕ) : ℕ∞)) ω
        ∂markovChainMeasure P x) =
      r x - γ +
        α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x := by
  exact integral_discountedStoppedSum_finiteRetirementForcedTime
    P hr α γ
    (fun b n x₀ ↦
      integrable_finiteRetirementPayoff_of_discounted
        P hr hα0 hint γ b n x₀)
    (fun b n x₀ ↦
      integrable_finiteRetirementPayoff_next_of_discounted
        P hr hα0 hint γ b n x₀)
    n x

lemma finiteRetirementForcedTime_isStoppingTime
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) {r : S → ℝ} (hr : Measurable r)
    (α γ : ℝ) (n : ℕ) :
    IsTrajStoppingTime
      (fun ω ↦ ((1 + finiteRetirementTime P r α γ 1 n ω : ℕ) : ℕ∞)) := by
  intro t
  cases t with
  | zero =>
      convert MeasurableSet.empty
      ext ω
      simp
  | succ t =>
      have h :=
        measurableSet_finiteRetirementTime_le P hr α γ 1 n t
      have heq : 1 + t = t + 1 := by omega
      rw [← heq]
      have hset :
          {ω | ((1 + finiteRetirementTime P r α γ 1 n ω : ℕ) : ℕ∞) ≤
              ((1 + t : ℕ) : ℕ∞)} =
            {ω | finiteRetirementTime P r α γ 1 n ω ≤ t} := by
        ext ω
        norm_cast
        simp
      rw [hset]
      exact h

lemma gittinsRetirementCandidateSet_bddAbove
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (γ : ℝ) :
    BddAbove (insert 0 {v : ℝ |
      ∃ τ : (ℕ → S) → ℕ∞,
        IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
        v = ∫ ω, discountedStoppedSum α (fun y ↦ r y - γ) τ ω
          ∂markovChainMeasure P x}) := by
  let G : ℝ := ∑' t : ℕ, α ^ t
  let U : ℝ := (gittinsIndex P r α x - γ) * G
  refine ⟨max 0 U, ?_⟩
  intro v hv
  rcases hv with (rfl | ⟨τ, hτ, hτ1, rfl⟩)
  · exact le_max_left _ _
  · rw [integral_discountedStoppedSum_sub_charge
      P hr hα0.le hα1 hint x hτ]
    let den : ℝ :=
      ∫ ω, discountedStoppedSum α (fun _ : S ↦ 1) τ ω
        ∂markovChainMeasure P x
    let num : ℝ :=
      ∫ ω, discountedStoppedSum α r τ ω
        ∂markovChainMeasure P x
    have hbounds :=
      integral_discountedStoppedSum_one_bounds
        P hα0.le hα1 x hτ hτ1
    have hden : 0 < den := by
      dsimp [den]
      linarith [hbounds.1]
    have hdenG : den ≤ G := by
      exact hbounds.2
    have hratio : num / den ≤ gittinsIndex P r α x :=
      gittins_stopping_ratio_le_index
        P hr hα0 hα1 hint x τ hτ hτ1
    have hnum : num ≤ gittinsIndex P r α x * den := by
      rwa [div_le_iff₀ hden] at hratio
    have hnet :
        num - γ * den ≤
          (gittinsIndex P r α x - γ) * den := by
      nlinarith
    apply hnet.trans
    by_cases hδ : 0 ≤ gittinsIndex P r α x - γ
    · exact (mul_le_mul_of_nonneg_left hdenG hδ).trans
        (le_max_right _ _)
    · have hδ' : gittinsIndex P r α x - γ < 0 := lt_of_not_ge hδ
      have : (gittinsIndex P r α x - γ) * den ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg hδ'.le hden.le
      exact this.trans (le_max_left _ _)

theorem gittinsFiniteRetirementValue_le_retirementValue
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (n : ℕ) (x : S) :
    gittinsFiniteRetirementValue P r α γ n x ≤
      gittinsRetirementValue P r α γ x := by
  let B : Set ℝ := insert 0 {v : ℝ |
    ∃ τ : (ℕ → S) → ℕ∞,
      IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      v = ∫ ω, discountedStoppedSum α (fun y ↦ r y - γ) τ ω
        ∂markovChainMeasure P x}
  have hBdd : BddAbove B :=
    gittinsRetirementCandidateSet_bddAbove
      P hr hα0 hα1 hint x γ
  have hzero : (0 : ℝ) ∈ B := Set.mem_insert 0 _
  have hzle : 0 ≤ gittinsRetirementValue P r α γ x := by
    rw [gittinsRetirementValue]
    change 0 ≤ sSup B
    exact le_csSup hBdd hzero
  cases n with
  | zero =>
      simpa [gittinsFiniteRetirementValue] using hzle
  | succ n =>
      let V : ℝ :=
        gittinsFiniteRetirementValue P r α γ (n + 1) x
      let c : ℝ :=
        r x - γ +
          α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x
      have hV : V = max 0 c := by
        rfl
      by_cases hV0 : V = 0
      · simpa [V, hV0] using hzle
      · have hVnonneg : 0 ≤ V := by
          rw [hV]
          exact le_max_left _ _
        have hVpos : 0 < V := lt_of_le_of_ne hVnonneg (Ne.symm hV0)
        have hcpos : 0 < c := by
          by_contra hc
          have hcle : c ≤ 0 := le_of_not_gt hc
          have : V = 0 := by
            rw [hV, max_eq_left hcle]
          exact hV0 this
        let τ : (ℕ → S) → ℕ∞ :=
          fun ω ↦
            ((1 + finiteRetirementTime P r α γ 1 n ω : ℕ) : ℕ∞)
        have hτ : IsTrajStoppingTime τ :=
          finiteRetirementForcedTime_isStoppingTime P hr α γ n
        have hτ1 : ∀ ω, 1 ≤ τ ω := by
          intro ω
          simp [τ]
        have hvalue :
            (∫ ω, discountedStoppedSum α (fun y ↦ r y - γ) τ ω
                ∂markovChainMeasure P x) = V := by
          rw [integral_discountedStoppedSum_finiteRetirementForcedTime_of_discounted
            P hr hα0 hint γ n x]
          rw [hV, max_eq_right hcpos.le]
        have hmem : V ∈ B := by
          right
          exact ⟨τ, hτ, hτ1, hvalue.symm⟩
        rw [gittinsRetirementValue]
        change V ≤ sSup B
        exact le_csSup hBdd hmem

lemma gittinsRetirementValue_nonneg
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (x : S) :
    0 ≤ gittinsRetirementValue P r α γ x := by
  simpa [gittinsFiniteRetirementValue] using
    (gittinsFiniteRetirementValue_le_retirementValue
      P hr hα0 hα1 hint γ 0 x)

end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm



@[simp] lemma currentHistoryPrevailingCharge_zero
    {k : ℕ} {S : Type*} (g : S → ℝ)
    (h : MarkovBanditHistory k S 0) (i : Fin k) :
    currentHistoryPrevailingCharge g 0 h i = g (h.2 i) :=
  rfl

lemma currentGittinsRetirementPotential_nonneg
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (h : MarkovBanditHistory k S n) :
    0 ≤ currentGittinsRetirementPotential P r α h := by
  apply Finset.sum_nonneg
  intro i hi
  exact gittinsRetirementValue_nonneg
    P hr hα0 hα1 hint _ _

lemma markovBanditExpectedRetirementPotential_nonneg
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) (n : ℕ) :
    0 ≤ markovBanditExpectedRetirementPotential P r α π x n := by
  exact integral_nonneg fun h ↦
    currentGittinsRetirementPotential_nonneg
      P hr hα0 hα1 hint h

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
    (π : BanditAlgorithm.MarkovBanditPolicy k S) (x : Fin k → S) (N : ℕ) :
    0 ≤ BanditAlgorithm.markovBanditExpectedRetirementPotential
      P r α π x N := by
  exact BanditAlgorithm.markovBanditExpectedRetirementPotential_nonneg
    P hr hα0 hα1 hint π x N
