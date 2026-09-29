-- Prove2me | solution 1 for BanditAlgorithm.etc_arm_expected_pull_count_step_bound
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-07-22T15:13:50.876374+00:00
-- url     : https://prove2.me/submissions/74ab9465-939d-484b-a91f-73136e766f85

import Definitions.Def_etcPolicy
import Theorems.Thm_BanditAlgorithm_etc_commit_arm_probability_bound
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
Direct proof work for Lattimore--Szepesvári, Theorem 6.1, Eqs. (6.2)--(6.3),
printed pp. 92--93.  These lemmas give the exact one-step occupation recursion
under a deterministic ETC selection kernel; they are the canonical-bandit
measure bridge needed before applying the two-sample subgaussian tail bound.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private theorem sum_roundRobin_arm_indicator_etc {k : ℕ} (hk : 0 < k)
    (m : ℕ) (i : Fin k) :
    (∑ r : Fin (m * k),
      if (⟨r % k, Nat.mod_lt r hk⟩ : Fin k) = i then (1 : ℝ) else 0) = m := by
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin k ≃ Fin (m * k))]
  have hmod (x : Fin m × Fin k) :
      (⟨x.2 % k, Nat.mod_lt x.2 hk⟩ : Fin k) = x.2 := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt x.2.isLt
  simp [finProdFinEquiv, hmod]
  have hset :
      ({x : Fin m × Fin k | x.2 = i} : Finset (Fin m × Fin k)) =
        Finset.univ ×ˢ {i} := by
    ext x
    simp
    constructor
    · intro hx
      exact ⟨x.1, Prod.ext rfl hx.symm⟩
    · rintro ⟨a, ha⟩
      exact (congrArg Prod.snd ha).symm
  rw [hset, Finset.card_product]
  simp

private theorem armPullCount_snoc_etc {k n : ℕ} (i : Fin k) (h : BanditHistory k n)
    (z : Fin k × ℝ) :
    armPullCount i (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armPullCount i h + if z.1 = i then 1 else 0 := by
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_add]
  simp only [armPullCount]
  have hset (g : BanditHistory k n) :
      ({t | (g t).1 = i}.toFinset.card : ℝ) =
        ∑ t, if (g t).1 = i then 1 else 0 := by
    have hs : {t | (g t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (g t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (g t).1 = i)
        Finset.univ).symm
  rw [hset]
  have hsnoc :
      (({t | (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i}.toFinset.card : ℕ) : ℝ) =
        ∑ t, if (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i then 1 else 0 := by
    have hs : {t | (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i}.toFinset =
        Finset.univ.filter
          (fun t ↦ (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ)
        (fun t : Fin (n + 1) ↦
          (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i)
        Finset.univ).symm
  rw [hsnoc, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

private theorem measurable_armPullCount_cast_etc {k n : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) := by
  rw [show (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) =
      fun h ↦ ∑ t, if (h t).1 = i then (1 : ℝ) else 0 by
    funext h
    rw [armPullCount]
    have hs : {t | (h t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (h t).1 = i)
        Finset.univ).symm]
  apply Finset.measurable_sum
  intro t ht
  have ha : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact Measurable.ite ((measurableSet_singleton i).preimage ha)
    measurable_const measurable_const

private theorem banditStepKernel_apply_eq_map_of_selected_etc
    {k : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    {r : ℕ} (h : BanditHistory k r) (a : Fin k)
    (hselect : (π.select r) h = Measure.dirac a) :
    banditStepKernel ν π r h = (ν.P a).map (Prod.mk a) := by
  rw [banditStepKernel]
  ext s hs
  rw [Kernel.compProd_apply hs, hselect, lintegral_dirac]
  rw [Measure.map_apply measurable_prodMk_left hs]
  rw [Kernel.comap_apply]
  simp [banditRewardKernel, Kernel.ofFunOfCountable]

private theorem banditStepKernel_ae_selected_arm_etc
    {k : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    {r : ℕ} (h : BanditHistory k r) (a : Fin k)
    (hselect : (π.select r) h = Measure.dirac a) :
    ∀ᵐ z ∂banditStepKernel ν π r h, z.1 = a := by
  rw [banditStepKernel_apply_eq_map_of_selected_etc ν π h a hselect]
  exact (ae_map_iff (μ := ν.P a) measurable_prodMk_left.aemeasurable
    (by measurability)).2 (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- Exact one-step conditional occupation identity under deterministic arm `a`. -/
private theorem integral_banditStepKernel_pullCount_snoc_etc
    {k : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    {r : ℕ} (h : BanditHistory k r) (a i : Fin k)
    (hselect : (π.select r) h = Measure.dirac a) :
    ∫ z, (armPullCount i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) : ℝ)
      ∂banditStepKernel ν π r h =
      armPullCount i h + if a = i then 1 else 0 := by
  calc
    (∫ z, (armPullCount i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) : ℝ)
      ∂banditStepKernel ν π r h) =
        ∫ _z, ((armPullCount i h : ℝ) + if a = i then 1 else 0)
          ∂banditStepKernel ν π r h := by
      apply integral_congr_ae
      filter_upwards [banditStepKernel_ae_selected_arm_etc ν π h a hselect] with z hz
      rw [armPullCount_snoc_etc, Nat.cast_add]
      simp [hz]
    _ = armPullCount i h + if a = i then 1 else 0 := by simp

/-- Pull counts are bounded and therefore integrable at every finite horizon. -/
private theorem integrable_armPullCount_etc {k n : ℕ} (ν : StochasticBandit k)
    (π : BanditPolicy k) (i : Fin k) :
    Integrable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact (measurable_armPullCount_cast_etc i).aemeasurable
  · filter_upwards [] with h
    constructor
    · positivity
    · rw [show (armPullCount i h : ℝ) =
          ∑ t, if (h t).1 = i then (1 : ℝ) else 0 by
        rw [armPullCount]
        have hs : {t | (h t).1 = i}.toFinset =
            Finset.univ.filter (fun t ↦ (h t).1 = i) := by
          ext t
          simp
        rw [hs]
        simpa using
          (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (h t).1 = i)
            Finset.univ).symm]
      calc
        (∑ t, if (h t).1 = i then (1 : ℝ) else 0) ≤
            ∑ _t : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro t ht
          split <;> norm_num
        _ = n := by simp

private theorem armPullCount_cast_le_length_etc {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) : (armPullCount i h : ℝ) ≤ n := by
  rw [show (armPullCount i h : ℝ) =
      ∑ t, if (h t).1 = i then (1 : ℝ) else 0 by
    rw [armPullCount]
    have hs : {t | (h t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (h t).1 = i)
        Finset.univ).symm]
  calc
    (∑ t, if (h t).1 = i then (1 : ℝ) else 0) ≤
        ∑ _t : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      split <;> norm_num
    _ = n := by simp

private theorem integral_armPullCount_le_horizon_etc {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k) :
    ∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π n ≤ n := by
  calc
    (∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π n) ≤
        ∫ _h : BanditHistory k n, (n : ℝ) ∂banditMeasure ν π n := by
      apply integral_mono (integrable_armPullCount_etc ν π i) (integrable_const _)
      intro h
      change (armPullCount i h : ℝ) ≤ (n : ℝ)
      exact armPullCount_cast_le_length_etc i h
    _ = n := by simp

/-- Lift the deterministic one-step occupation identity through the canonical
bandit measure. This is the induction step behind the exploration/commit count
formula in Eq. (6.2). -/
private theorem integral_armPullCount_succ_of_deterministic_etc
    {k r : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (a : BanditHistory k r → Fin k)
    (hselect : ∀ h, (π.select r) h = Measure.dirac (a h)) (i : Fin k) :
    ∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π (r + 1) =
      ∫ h, ((armPullCount i h : ℝ) + if a h = i then 1 else 0)
        ∂banditMeasure ν π r := by
  let μ := banditMeasure ν π r
  let κ := banditStepKernel ν π r
  let snoc : BanditHistory k r × (Fin k × ℝ) → BanditHistory k (r + 1) :=
    fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2
  have hsnoc : Measurable snoc := measurable_banditHistorySnoc
  have hcomp : Integrable
      (fun p : BanditHistory k r × (Fin k × ℝ) ↦
        (armPullCount i (snoc p) : ℝ)) (μ.compProd κ) := by
    apply Integrable.of_mem_Icc 0 (r + 1)
    · exact ((measurable_armPullCount_cast_etc i).comp hsnoc).aemeasurable
    · filter_upwards [] with p
      refine ⟨by positivity, ?_⟩
      simpa only [Nat.cast_add, Nat.cast_one] using
        (armPullCount_cast_le_length_etc i (snoc p))
  rw [banditMeasure,
    integral_map hsnoc.aemeasurable
      (measurable_armPullCount_cast_etc i).aestronglyMeasurable]
  change (∫ p, (armPullCount i (snoc p) : ℝ) ∂(μ.compProd κ)) = _
  rw [Measure.integral_compProd hcomp]
  apply integral_congr_ae
  filter_upwards [] with h
  exact integral_banditStepKernel_pullCount_snoc_etc
    ν π h (a h) i (hselect h)

/-- During the exploration prefix, ETC deterministically adds the indicator of
the round-robin arm to the expected occupation count. -/
private theorem integral_armPullCount_succ_exploration_etc
    {k : ℕ} (hk : 0 < k) {ν : StochasticBandit k} {m r : ℕ}
    {π : BanditPolicy k} (hπ : IsETCPolicy hk m π) (hr : r < m * k)
    (i : Fin k) :
    ∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π (r + 1) =
      (∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π r) +
        if (⟨r % k, Nat.mod_lt r hk⟩ : Fin k) = i then 1 else 0 := by
  obtain ⟨commit, hmax, hpolicy⟩ := hπ
  have hrec := integral_armPullCount_succ_of_deterministic_etc ν π
    (fun _h : BanditHistory k r ↦ (⟨r % k, Nat.mod_lt r hk⟩ : Fin k))
    (fun h ↦ (hpolicy r h).1 hr) i
  rw [hrec]
  rw [integral_add (integrable_armPullCount_etc ν π i) (integrable_const _)]
  simp

private theorem integral_armPullCount_during_exploration_etc
    {k : ℕ} (hk : 0 < k) {ν : StochasticBandit k} (m : ℕ)
    {π : BanditPolicy k} (hπ : IsETCPolicy hk m π) (i : Fin k) :
    ∀ r, r ≤ m * k →
      ∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π r =
        ∑ s : Fin r,
          if (⟨s % k, Nat.mod_lt s hk⟩ : Fin k) = i then 1 else 0 := by
  intro r hr
  induction r with
  | zero => simp [banditMeasure, armPullCount]
  | succ r ih =>
      have hrlt : r < m * k := Nat.lt_of_succ_le hr
      rw [integral_armPullCount_succ_exploration_etc hk hπ hrlt i]
      rw [ih (Nat.le_of_succ_le hr), Fin.sum_univ_castSucc]
      rfl

private theorem integral_armPullCount_at_commit_time_etc
    {k : ℕ} (hk : 0 < k) {ν : StochasticBandit k} (m : ℕ)
    {π : BanditPolicy k} (hπ : IsETCPolicy hk m π) (i : Fin k) :
    ∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π (m * k) = m := by
  rw [integral_armPullCount_during_exploration_etc hk m hπ i (m * k) le_rfl]
  exact sum_roundRobin_arm_indicator_etc hk m i

/-- After exploration, the ETC occupation recursion is driven by the single
committed empirical-mean maximizer chosen from the exploration prefix. -/
private theorem integral_armPullCount_succ_commit_etc
    {k : ℕ} (hk : 0 < k) {ν : StochasticBandit k} {m r : ℕ}
    {π : BanditPolicy k} (hπ : IsETCPolicy hk m π) (hr : m * k ≤ r)
    (i : Fin k) :
    ∃ commit : BanditHistory k (m * k) → Fin k,
      (∀ h₀ : BanditHistory k (m * k), ∀ j : Fin k,
        armEmpiricalMean j h₀ ≤ armEmpiricalMean (commit h₀) h₀) ∧
      (∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π (r + 1) =
        ∫ h, ((armPullCount i h : ℝ) +
          if commit (banditExplorationPrefix hr h) = i then 1 else 0)
          ∂banditMeasure ν π r) := by
  obtain ⟨commit, hmax, hpolicy⟩ := hπ
  refine ⟨commit, hmax, ?_⟩
  exact integral_armPullCount_succ_of_deterministic_etc ν π
    (fun h ↦ commit (banditExplorationPrefix hr h))
    (fun h ↦ (hpolicy r h).2 hr) i

end BanditAlgorithm


theorem solution
    {k : ℕ} (hk : 0 < k)
    {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {m : ℕ} (hm : 1 ≤ m) {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsETCPolicy hk m π) (i : Fin k) :
    ∀ r : ℕ, m * k ≤ r →
      MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π (r + 1))
          (fun h : BanditAlgorithm.BanditHistory k (r + 1) ↦
            (BanditAlgorithm.armPullCount i h : ℝ)) ≤
        MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π r)
          (fun h : BanditAlgorithm.BanditHistory k r ↦
            (BanditAlgorithm.armPullCount i h : ℝ)) +
          Real.exp (-(m * (BanditAlgorithm.banditGap ν i) ^ 2) / 4) := by
  obtain ⟨commit, _hmax, hselect, hprob⟩ :=
    BanditAlgorithm.etc_commit_arm_probability_bound hk hν hm hπ i
  intro r hr
  rw [BanditAlgorithm.integral_armPullCount_succ_of_deterministic_etc ν π
    (fun h : BanditAlgorithm.BanditHistory k r ↦
      commit (BanditAlgorithm.banditExplorationPrefix hr h))
    (fun h ↦ hselect r h hr) i]
  rw [integral_add
    (BanditAlgorithm.integrable_armPullCount_etc ν π i) (hprob r hr).1]
  exact add_le_add le_rfl (hprob r hr).2
