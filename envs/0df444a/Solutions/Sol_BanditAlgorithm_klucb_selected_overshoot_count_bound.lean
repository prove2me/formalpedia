-- Prove2me | solution 1 for BanditAlgorithm.klucb_selected_overshoot_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:45:01.425805+00:00
-- url     : https://prove2.me/submissions/5dc42c77-d4ac-4460-827b-a3fc4a90daa6

import Definitions.Def_banditHistoryPrefix
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_klucbFailureCount
import Definitions.Def_klucbFeasibilityFailureCount
import Definitions.Def_klucbTruncatedRelativeEntropy
import Definitions.Def_ucbStoppedCenteredSum
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.Order
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 0

/- Complete accepted source by Harry_Xu, submission 0259d29b-c996-48cb-8810-caa12f4c4ce5. -/
namespace OvershootDependency0
open _root_.BanditAlgorithm

/-!
Canonical-model stopped-reward concentration for an arbitrary (possibly
randomized) bandit policy.  This is the reward-stack / bounded optional
stopping bridge from Lattimore--Szepesvári §4.6, Exercise 4.4, used in the
proofs of Theorems 7.1 and 8.1.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private theorem armPullCount_snoc_ast {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) (z : Fin k × ℝ) :
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
      (({t |
          (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i}.toFinset.card :
          ℕ) : ℝ) =
        ∑ t, if
          (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i
        then 1 else 0 := by
    have hs : {t |
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i}.toFinset =
        Finset.univ.filter
          (fun t ↦
            (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i) := by
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

private theorem measurable_armPullCount_cast_ast {k n : ℕ} (i : Fin k) :
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

private theorem measurable_stoppedScoreFactor_ast {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ) (t : ℝ) :
    Measurable (fun p : BanditHistory k m × (Fin k × ℝ) ↦ Real.exp
      (if armPullCount i p.1 < u ∧ p.2.1 = i then
        t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)) := by
  apply Measurable.exp
  have hcount : Measurable
      (fun p : BanditHistory k m × (Fin k × ℝ) ↦
        (armPullCount i p.1 : ℝ)) :=
    (measurable_armPullCount_cast_ast i).comp measurable_fst
  have hlt : MeasurableSet
      {p : BanditHistory k m × (Fin k × ℝ) |
        armPullCount i p.1 < u} := by
    simpa only [Nat.cast_lt] using measurableSet_lt hcount
      (measurable_const : Measurable
        (fun _ : BanditHistory k m × (Fin k × ℝ) ↦ (u : ℝ)))
  have heq : MeasurableSet
      {p : BanditHistory k m × (Fin k × ℝ) | p.2.1 = i} :=
    (measurableSet_singleton i).preimage measurable_snd.fst
  exact Measurable.ite (hlt.inter heq)
    ((measurable_snd.snd.sub measurable_const).const_mul t
      |>.sub measurable_const)
    measurable_const

private theorem integrable_banditStepKernel_stoppedScoreFactor_ast
    {k m : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) (π : BanditPolicy k)
    (h : BanditHistory k m) (i : Fin k) (u : ℕ) (t : ℝ) :
    Integrable (fun z : Fin k × ℝ ↦ Real.exp
      (if armPullCount i h < u ∧ z.1 = i then
        t * (z.2 - banditArmMean ν i) - t ^ 2 / 8 else 0))
      (banditStepKernel ν π m h) := by
  rw [banditStepKernel]
  apply (ProbabilityTheory.integrable_compProd_iff
    ((measurable_stoppedScoreFactor_ast ν i u t).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable).2
  constructor
  · filter_upwards with a
    rw [Kernel.comap_apply]
    by_cases hc : armPullCount i h < u ∧ a = i
    · have hlt := hc.1
      have hai := hc.2
      subst a
      simp only [Function.comp_apply, id_eq, hlt, and_self, if_pos]
      rw [show (banditRewardKernel ν) i = ν.P i by
        simp [banditRewardKernel, Kernel.ofFunOfCountable]]
      change Integrable
        (fun y : ℝ ↦ Real.exp
          (t * (y - banditArmMean ν i) - t ^ 2 / 8)) (ν.P i)
      have hbase :=
        (hν.2 i).integrable_exp_mul t |>.mul_const
          (Real.exp (-(t ^ 2 / 8)))
      convert hbase using 1
      funext y
      rw [← Real.exp_add]
      congr 1
    · simp [hc]
  · exact Integrable.of_finite

private theorem banditStepKernel_integral_stoppedScoreFactor_le_one_ast
    {k m : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) (π : BanditPolicy k)
    (h : BanditHistory k m) (i : Fin k) (u : ℕ) (t : ℝ) :
    ∫ z : Fin k × ℝ, Real.exp
      (if armPullCount i h < u ∧ z.1 = i then
        t * (z.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)
      ∂banditStepKernel ν π m h ≤ 1 := by
  have hint :=
    integrable_banditStepKernel_stoppedScoreFactor_ast
      ν hν π h i u t
  rw [banditStepKernel] at hint ⊢
  rw [ProbabilityTheory.integral_compProd hint]
  calc
    (∫ a, ∫ y, Real.exp
        (if armPullCount i h < u ∧ a = i then
          t * (y - banditArmMean ν i) - t ^ 2 / 8 else 0)
        ∂((banditRewardKernel ν).comap Prod.snd measurable_snd) (h, a)
        ∂(π.select m) h) ≤
        ∫ _a, (1 : ℝ) ∂(π.select m) h := by
      apply integral_mono_ae hint.integral_compProd (integrable_const 1)
      filter_upwards with a
      rw [Kernel.comap_apply]
      by_cases hc : armPullCount i h < u ∧ a = i
      · have hlt := hc.1
        have hai := hc.2
        subst a
        simp only [hlt, and_self, if_pos]
        rw [show (banditRewardKernel ν) i = ν.P i by
          simp [banditRewardKernel, Kernel.ofFunOfCountable]]
        have hm := (hν.2 i).mgf_le t
        rw [mgf] at hm
        have hm' :
            (∫ y, Real.exp (t * (y - banditArmMean ν i)) ∂ν.P i) ≤
              Real.exp (t ^ 2 / 8) := by
          convert hm using 1 <;> norm_num <;> ring_nf
        calc
          (∫ y, Real.exp
              (t * (y - banditArmMean ν i) - t ^ 2 / 8) ∂ν.P i) =
              Real.exp (-(t ^ 2 / 8)) *
                ∫ y, Real.exp (t * (y - banditArmMean ν i)) ∂ν.P i := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with y
            rw [← Real.exp_add]
            congr 1
            ring
          _ ≤ Real.exp (-(t ^ 2 / 8)) * Real.exp (t ^ 2 / 8) :=
            mul_le_mul_of_nonneg_left hm' (Real.exp_nonneg _)
          _ = 1 := by
            rw [← Real.exp_add]
            ring_nf
            simp
      · simp [hc]
    _ = 1 := by simp

private theorem armStoppedCenteredSum_snoc_ast {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    armStoppedCenteredSum ν i u (m + 1)
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armStoppedCenteredSum ν i u m h +
        if armPullCount i h < u ∧ z.1 = i then
          z.2 - banditArmMean ν i
        else 0 := by
  simp [armStoppedCenteredSum]

private theorem min_armPullCount_snoc_ast {k m : ℕ}
    (i : Fin k) (u : ℕ) (h : BanditHistory k m) (z : Fin k × ℝ) :
    min (armPullCount i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z)) u =
      min (armPullCount i h) u +
        if armPullCount i h < u ∧ z.1 = i then 1 else 0 := by
  rw [armPullCount_snoc_ast]
  by_cases hi : z.1 = i
  · by_cases hlt : armPullCount i h < u
    · simp [hi, hlt]
      omega
    · simp [hi, hlt]
      omega
  · simp [hi]

private theorem measurable_armStoppedCenteredSum_ast {k : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ) (m : ℕ) :
    Measurable (armStoppedCenteredSum ν i u m) := by
  induction m with
  | zero => simp [armStoppedCenteredSum]
  | succ m ih =>
      have hinit : Measurable
          (fun h : BanditHistory k (m + 1) ↦ Fin.init h) := by
        rw [measurable_pi_iff]
        intro t
        exact measurable_pi_apply (Fin.castSucc t)
      have hlast : Measurable
          (fun h : BanditHistory k (m + 1) ↦ h (Fin.last m)) :=
        measurable_pi_apply (Fin.last m)
      have hcount : Measurable (fun h : BanditHistory k (m + 1) ↦
          (armPullCount i (Fin.init h) : ℝ)) :=
        (measurable_armPullCount_cast_ast i).comp hinit
      have hlt : MeasurableSet {h : BanditHistory k (m + 1) |
          armPullCount i (Fin.init h) < u} := by
        simpa only [Nat.cast_lt] using
          measurableSet_lt hcount
            (measurable_const : Measurable
              (fun _ : BanditHistory k (m + 1) ↦ (u : ℝ)))
      have heq : MeasurableSet {h : BanditHistory k (m + 1) |
          (h (Fin.last m)).1 = i} :=
        (measurableSet_singleton i).preimage hlast.fst
      change Measurable (fun h : BanditHistory k (m + 1) ↦
        armStoppedCenteredSum ν i u m (Fin.init h) +
          if armPullCount i (Fin.init h) < u ∧
              (h (Fin.last m)).1 = i then
            (h (Fin.last m)).2 - banditArmMean ν i else 0)
      exact (ih.comp hinit).add
        (Measurable.ite (hlt.inter heq)
          (hlast.snd.sub measurable_const) measurable_const)

private noncomputable def armStoppedExpScoreAst {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ) (t : ℝ)
    (h : BanditHistory k m) : ℝ :=
  Real.exp (t * armStoppedCenteredSum ν i u m h -
    t ^ 2 / 8 * ((min (armPullCount i h) u : ℕ) : ℝ))

private theorem measurable_armStoppedExpScoreAst {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ) (t : ℝ) :
    Measurable
      (armStoppedExpScoreAst ν i u t : BanditHistory k m → ℝ) := by
  apply Measurable.exp
  apply
    (measurable_const.mul (measurable_armStoppedCenteredSum_ast ν i u m)).sub
  have hmin : Measurable (fun h : BanditHistory k m ↦
      min (armPullCount i h : ℝ) (u : ℝ)) :=
    (measurable_armPullCount_cast_ast i).min measurable_const
  simpa only [Nat.cast_min] using hmin.const_mul (t ^ 2 / 8)

private theorem armStoppedExpScoreAst_snoc {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ) (t : ℝ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    armStoppedExpScoreAst ν i u t
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armStoppedExpScoreAst ν i u t h *
        Real.exp (if armPullCount i h < u ∧ z.1 = i then
          t * (z.2 - banditArmMean ν i) - t ^ 2 / 8 else 0) := by
  rw [armStoppedExpScoreAst, armStoppedExpScoreAst,
    armStoppedCenteredSum_snoc_ast, min_armPullCount_snoc_ast, Nat.cast_add]
  by_cases hlt : armPullCount i h < u
  · by_cases hi : z.1 = i
    · simp only [hlt, hi, and_self, if_pos, Nat.cast_one]
      rw [← Real.exp_add]
      congr 1
      ring
    · simp [hlt, hi]
  · simp [hlt]

private theorem integrable_compProd_armStoppedExpScoreAst_factor
    {k : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) {π : BanditPolicy k}
    {m : ℕ} (μ : Measure (BanditHistory k m)) [IsProbabilityMeasure μ]
    (i : Fin k) (u : ℕ) (t : ℝ)
    (hold : Integrable
      (armStoppedExpScoreAst ν i u t : BanditHistory k m → ℝ) μ) :
    Integrable (fun p : BanditHistory k m × (Fin k × ℝ) ↦
      armStoppedExpScoreAst ν i u t p.1 * Real.exp
        (if armPullCount i p.1 < u ∧ p.2.1 = i then
          t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 8 else 0))
      (μ.compProd (banditStepKernel ν π m)) := by
  let G : BanditHistory k m × (Fin k × ℝ) → ℝ := fun p ↦
    armStoppedExpScoreAst ν i u t p.1 * Real.exp
      (if armPullCount i p.1 < u ∧ p.2.1 = i then
        t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)
  have hG : StronglyMeasurable G :=
    (((measurable_armStoppedExpScoreAst ν i u t).comp measurable_fst).mul
      (measurable_stoppedScoreFactor_ast ν i u t)).stronglyMeasurable
  rw [Measure.integrable_compProd_iff hG.aestronglyMeasurable]
  constructor
  · exact Filter.Eventually.of_forall fun h ↦
      (integrable_banditStepKernel_stoppedScoreFactor_ast
        ν hν π h i u t).const_mul
          (armStoppedExpScoreAst ν i u t h)
  · apply Integrable.mono hold
      hG.norm.integral_kernel_prod_right'.aestronglyMeasurable
    filter_upwards [] with h
    have hscore : 0 ≤ armStoppedExpScoreAst ν i u t h :=
      Real.exp_nonneg _
    have hcond :=
      banditStepKernel_integral_stoppedScoreFactor_le_one_ast
        ν hν π h i u t
    have hinner_nonneg :
        0 ≤ ∫ z, ‖G (h, z)‖ ∂banditStepKernel ν π m h :=
      integral_nonneg fun _ ↦ norm_nonneg _
    rw [Real.norm_of_nonneg hinner_nonneg]
    change (∫ z, ‖armStoppedExpScoreAst ν i u t h * Real.exp
      (if armPullCount i h < u ∧ z.1 = i then
        t * (z.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)‖
      ∂banditStepKernel ν π m h) ≤ ‖armStoppedExpScoreAst ν i u t h‖
    simp_rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hscore,
      abs_of_nonneg (Real.exp_nonneg _)]
    rw [integral_const_mul]
    exact mul_le_of_le_one_right hscore hcond

private theorem armStoppedExpScoreAst_integrable_and_integral_le_one
    {k : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) {π : BanditPolicy k}
    (i : Fin k) (u : ℕ) (t : ℝ) : ∀ m : ℕ,
    Integrable
      (armStoppedExpScoreAst ν i u t : BanditHistory k m → ℝ)
      (banditMeasure ν π m) ∧
    ∫ h, armStoppedExpScoreAst ν i u t h ∂banditMeasure ν π m ≤ 1 := by
  intro m
  induction m with
  | zero =>
      constructor <;>
        simp [banditMeasure, armStoppedExpScoreAst,
          armStoppedCenteredSum, armPullCount]
  | succ m ih =>
      let μ := banditMeasure ν π m
      let κ := banditStepKernel ν π m
      let snoc :
          BanditHistory k m × (Fin k × ℝ) → BanditHistory k (m + 1) :=
        fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2
      let F : BanditHistory k m × (Fin k × ℝ) → ℝ := fun p ↦
        armStoppedExpScoreAst ν i u t p.1 * Real.exp
          (if armPullCount i p.1 < u ∧ p.2.1 = i then
            t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)
      have hrewrite :
          (fun p ↦ armStoppedExpScoreAst ν i u t (snoc p)) = F := by
        funext p
        exact armStoppedExpScoreAst_snoc ν i u t p.1 p.2
      have hcomp : Integrable F (μ.compProd κ) :=
        integrable_compProd_armStoppedExpScoreAst_factor
          ν hν μ i u t ih.1
      constructor
      · rw [banditMeasure]
        apply (integrable_map_measure
          (measurable_armStoppedExpScoreAst
            (m := m + 1) ν i u t).aestronglyMeasurable
          measurable_banditHistorySnoc.aemeasurable).2
        change Integrable
          (fun p ↦ armStoppedExpScoreAst ν i u t (snoc p))
          (μ.compProd κ)
        rw [hrewrite]
        exact hcomp
      · rw [banditMeasure,
          integral_map measurable_banditHistorySnoc.aemeasurable
            (measurable_armStoppedExpScoreAst
              (m := m + 1) ν i u t).aestronglyMeasurable]
        change (∫ p, armStoppedExpScoreAst ν i u t (snoc p)
          ∂(μ.compProd κ)) ≤ 1
        rw [hrewrite, Measure.integral_compProd hcomp]
        calc
          (∫ h, ∫ z, F (h, z) ∂κ h ∂μ) ≤
              ∫ h, armStoppedExpScoreAst ν i u t h ∂μ := by
            apply integral_mono_ae hcomp.integral_compProd ih.1
            filter_upwards [] with h
            change (∫ z, armStoppedExpScoreAst ν i u t h * Real.exp
              (if armPullCount i h < u ∧ z.1 = i then
                t * (z.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)
              ∂κ h) ≤ armStoppedExpScoreAst ν i u t h
            rw [integral_const_mul]
            exact mul_le_of_le_one_right (Real.exp_nonneg _)
              (banditStepKernel_integral_stoppedScoreFactor_le_one_ast
                ν hν π h i u t)
          _ ≤ 1 := ih.2

theorem adaptive_armStoppedCenteredSum_upper_tail_half
    {k n : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) {π : BanditPolicy k}
    (i : Fin k) (u : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          (u : ℝ) * t ≤ armStoppedCenteredSum ν i u n h} ≤
      Real.exp (-2 * (u : ℝ) * t ^ 2) := by
  let μ := banditMeasure ν π n
  let X : BanditHistory k n → ℝ := fun h ↦
    armStoppedCenteredSum ν i u n h -
      t / 2 * ((min (armPullCount i h) u : ℕ) : ℝ)
  have hscore :=
    armStoppedExpScoreAst_integrable_and_integral_le_one
      ν hν (π := π) i u (4 * t) n
  have hexp : (fun h : BanditHistory k n ↦ Real.exp ((4 * t) * X h)) =
      armStoppedExpScoreAst ν i u (4 * t) := by
    funext h
    rw [armStoppedExpScoreAst]
    dsimp [X]
    congr 1
    ring
  have hint : Integrable
      (fun h : BanditHistory k n ↦ Real.exp ((4 * t) * X h)) μ := by
    rw [hexp]
    exact hscore.1
  have h4t : 0 ≤ 4 * t := mul_nonneg (by norm_num) ht
  have hchern := measure_ge_le_exp_mul_mgf (μ := μ) (X := X)
    ((u : ℝ) * t / 2) h4t hint
  calc
    μ.real {h : BanditHistory k n |
        (u : ℝ) * t ≤ armStoppedCenteredSum ν i u n h} ≤
        μ.real {h | (u : ℝ) * t / 2 ≤ X h} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro h hh
      have hmin : ((min (armPullCount i h) u : ℕ) : ℝ) ≤ u := by
        exact_mod_cast Nat.min_le_right (armPullCount i h) u
      have hmul : 0 ≤ t *
          ((u : ℝ) - ((min (armPullCount i h) u : ℕ) : ℝ)) :=
        mul_nonneg ht (sub_nonneg.mpr hmin)
      dsimp [X]
      have hbase : (u : ℝ) * t / 2 ≤ (u : ℝ) * t -
          t / 2 * ((min (armPullCount i h) u : ℕ) : ℝ) := by
        nlinarith [hmul]
      exact hbase.trans (sub_le_sub_right hh _)
    _ ≤ Real.exp (-(4 * t) * ((u : ℝ) * t / 2)) *
          mgf X μ (4 * t) := hchern
    _ ≤ Real.exp (-(4 * t) * ((u : ℝ) * t / 2)) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · rw [mgf, hexp]
        exact hscore.2
      · positivity
    _ = Real.exp (-2 * (u : ℝ) * t ^ 2) := by
      congr 1
      ring

theorem adaptive_armStoppedCenteredSum_lower_tail_half
    {k n : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) {π : BanditPolicy k}
    (i : Fin k) (u : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          armStoppedCenteredSum ν i u n h ≤ -(u : ℝ) * t} ≤
      Real.exp (-2 * (u : ℝ) * t ^ 2) := by
  let μ := banditMeasure ν π n
  let X : BanditHistory k n → ℝ := fun h ↦
    -armStoppedCenteredSum ν i u n h -
      t / 2 * ((min (armPullCount i h) u : ℕ) : ℝ)
  have hscore :=
    armStoppedExpScoreAst_integrable_and_integral_le_one
      ν hν (π := π) i u (-(4 * t)) n
  have hexp : (fun h : BanditHistory k n ↦ Real.exp ((4 * t) * X h)) =
      armStoppedExpScoreAst ν i u (-(4 * t)) := by
    funext h
    rw [armStoppedExpScoreAst]
    dsimp [X]
    congr 1
    ring
  have hint : Integrable
      (fun h : BanditHistory k n ↦ Real.exp ((4 * t) * X h)) μ := by
    rw [hexp]
    exact hscore.1
  have h4t : 0 ≤ 4 * t := mul_nonneg (by norm_num) ht
  have hchern := measure_ge_le_exp_mul_mgf (μ := μ) (X := X)
    ((u : ℝ) * t / 2) h4t hint
  calc
    μ.real {h : BanditHistory k n |
        armStoppedCenteredSum ν i u n h ≤ -(u : ℝ) * t} ≤
        μ.real {h | (u : ℝ) * t / 2 ≤ X h} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro h hh
      have hmin : ((min (armPullCount i h) u : ℕ) : ℝ) ≤ u := by
        exact_mod_cast Nat.min_le_right (armPullCount i h) u
      have hmul : 0 ≤ t *
          ((u : ℝ) - ((min (armPullCount i h) u : ℕ) : ℝ)) :=
        mul_nonneg ht (sub_nonneg.mpr hmin)
      dsimp [X]
      change armStoppedCenteredSum ν i u n h ≤ -(u : ℝ) * t at hh
      have hh' : (u : ℝ) * t ≤
          -armStoppedCenteredSum ν i u n h := by
        linarith
      have hbase : (u : ℝ) * t / 2 ≤ (u : ℝ) * t -
          t / 2 * ((min (armPullCount i h) u : ℕ) : ℝ) := by
        nlinarith [hmul]
      exact hbase.trans (sub_le_sub_right hh' _)
    _ ≤ Real.exp (-(4 * t) * ((u : ℝ) * t / 2)) *
          mgf X μ (4 * t) := hchern
    _ ≤ Real.exp (-(4 * t) * ((u : ℝ) * t / 2)) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · rw [mgf, hexp]
        exact hscore.2
      · positivity
    _ = Real.exp (-2 * (u : ℝ) * t ^ 2) := by
      congr 1
      ring

private noncomputable def armCenteredSumAst {k n : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (h : BanditHistory k n) : ℝ :=
  ∑ t, if (h t).1 = i then (h t).2 - banditArmMean ν i else 0

private theorem armCenteredSumAst_snoc {k n : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (h : BanditHistory k n)
    (z : Fin k × ℝ) :
    armCenteredSumAst ν i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armCenteredSumAst ν i h +
        if z.1 = i then z.2 - banditArmMean ν i else 0 := by
  simp only [armCenteredSumAst, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

theorem armStoppedCenteredSum_eq_pullCount_mul_empirical_sub_mean
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (hcount : armPullCount i h ≤ u) :
    armStoppedCenteredSum ν i u m h =
      (armPullCount i h : ℝ) *
        (armEmpiricalMean i h - banditArmMean ν i) := by
  have hstop :
      armStoppedCenteredSum ν i u m h = armCenteredSumAst ν i h := by
    induction m with
    | zero => simp [armStoppedCenteredSum, armCenteredSumAst]
    | succ m ih =>
        rw [← Fin.snoc_init_self h] at hcount ⊢
        rw [armPullCount_snoc_ast] at hcount
        rw [armStoppedCenteredSum_snoc_ast, armCenteredSumAst_snoc]
        by_cases hi : (h (Fin.last m)).1 = i
        · have hprev : armPullCount i (Fin.init h) < u := by
            simp [hi] at hcount
            omega
          rw [if_pos ⟨hprev, hi⟩, if_pos hi,
            ih (Fin.init h) (Nat.le_of_lt hprev)]
        · have hprev : armPullCount i (Fin.init h) ≤ u := by
            simpa [hi] using hcount
          rw [if_neg (fun hc ↦ hi hc.2), if_neg hi,
            ih (Fin.init h) hprev]
  rw [hstop]
  let S : Finset (Fin m) := {t | (h t).1 = i}.toFinset
  have hsum : (∑ t, if (h t).1 = i then
      (h t).2 - banditArmMean ν i else 0) =
      ∑ t ∈ S, ((h t).2 - banditArmMean ν i) := by
    have hS : S = Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp [S]
    rw [hS, Finset.sum_filter]
  rw [armCenteredSumAst, hsum]
  change (∑ t ∈ S, ((h t).2 - banditArmMean ν i)) =
    (S.card : ℝ) *
      ((∑ t ∈ S, (h t).2) / (S.card : ℝ) - banditArmMean ν i)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  by_cases hc : S.card = 0
  · have hS0 : S = ∅ := Finset.card_eq_zero.mp hc
    simp [hS0]
  · have hcast : (S.card : ℝ) ≠ 0 := by exact_mod_cast hc
    field_simp

private theorem measurable_banditHistoryPrefixAt_ast {k n : ℕ}
    (r : Fin n) :
    Measurable
      (fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r) := by
  rw [measurable_pi_iff]
  intro s
  exact measurable_pi_apply
    (⟨s.val, lt_trans s.isLt r.isLt⟩ : Fin n)

private theorem prefixAt_snoc_castSucc_ast {k n : ℕ}
    (h : BanditHistory k n) (z : Fin k × ℝ) (r : Fin n) :
    banditHistoryPrefixAt
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) r.castSucc =
      banditHistoryPrefixAt h r := by
  funext s
  unfold banditHistoryPrefixAt
  have hsr : s.val < r.val := by simpa using s.isLt
  have hsn : s.val < n := lt_trans hsr r.isLt
  rw [Fin.snoc]
  rw [dif_pos hsn]
  simp

private theorem prefixAt_snoc_last_ast {k n : ℕ}
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    banditHistoryPrefixAt
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) (Fin.last n) = h := by
  funext s
  simp [banditHistoryPrefixAt, Fin.snoc]

private theorem banditMeasure_map_init_ast {k m : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) :
    (banditMeasure ν π (m + 1)).map
        (fun h : BanditHistory k (m + 1) ↦ Fin.init h) =
      banditMeasure ν π m := by
  rw [banditMeasure]
  rw [MeasureTheory.Measure.map_map
    (by fun_prop :
      Measurable (fun h : BanditHistory k (m + 1) ↦ Fin.init h))
    measurable_banditHistorySnoc]
  have hfun :
      ((fun h : BanditHistory k (m + 1) ↦ Fin.init h) ∘
        (fun h : BanditHistory k m × (Fin k × ℝ) ↦
          Fin.snoc (α := fun _ ↦ Fin k × ℝ) h.1 h.2)) =
        Prod.fst := by
    funext p
    simp
  rw [hfun]
  change Measure.fst
      ((banditMeasure ν π m).compProd (banditStepKernel ν π m)) =
    banditMeasure ν π m
  exact MeasureTheory.Measure.fst_compProd
    (banditMeasure ν π m) (banditStepKernel ν π m)

theorem banditMeasure_map_historyPrefixAt
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (r : Fin n) :
    (banditMeasure ν π n).map
        (fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r) =
      banditMeasure ν π r.val := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
      refine Fin.lastCases ?_ (fun s ↦ ?_) r
      · change
          (banditMeasure ν π (n + 1)).map
              (fun h : BanditHistory k (n + 1) ↦
                banditHistoryPrefixAt h (Fin.last n)) =
            banditMeasure ν π n
        rw [show
          (fun h : BanditHistory k (n + 1) ↦
            banditHistoryPrefixAt h (Fin.last n)) =
          (fun h ↦ Fin.init h) by
            funext h
            rw [← Fin.snoc_init_self h]
            simpa using
              prefixAt_snoc_last_ast (Fin.init h) (h (Fin.last n))]
        exact banditMeasure_map_init_ast ν π
      · change
          (banditMeasure ν π (n + 1)).map
              (fun h : BanditHistory k (n + 1) ↦
                banditHistoryPrefixAt h s.castSucc) =
            banditMeasure ν π s.val
        rw [show
          (fun h : BanditHistory k (n + 1) ↦
            banditHistoryPrefixAt h s.castSucc) =
          (fun g : BanditHistory k n ↦ banditHistoryPrefixAt g s) ∘
            (fun h : BanditHistory k (n + 1) ↦ Fin.init h) by
            funext h
            rw [← Fin.snoc_init_self h]
            simpa [Function.comp_apply] using
              prefixAt_snoc_castSucc_ast
                (Fin.init h) (h (Fin.last n)) s]
        calc
          (banditMeasure ν π (n + 1)).map
              ((fun g : BanditHistory k n ↦ banditHistoryPrefixAt g s) ∘
                (fun h : BanditHistory k (n + 1) ↦ Fin.init h)) =
              ((banditMeasure ν π (n + 1)).map
                (fun h : BanditHistory k (n + 1) ↦ Fin.init h)).map
                (fun g : BanditHistory k n ↦
                  banditHistoryPrefixAt g s) := by
            symm
            exact MeasureTheory.Measure.map_map
              (measurable_banditHistoryPrefixAt_ast s)
              (by fun_prop :
                Measurable
                  (fun h : BanditHistory k (n + 1) ↦ Fin.init h))
          _ = banditMeasure ν π s.val := by
            rw [banditMeasure_map_init_ast ν π, ih s]

end BanditAlgorithm

theorem checked
    {k n : ℕ} (ν : BanditAlgorithm.StochasticBandit k)
    (hν : BanditAlgorithm.IsSubgaussianBandit (1 / 2) ν)
    {π : BanditAlgorithm.BanditPolicy k}
    (i : Fin k) (u : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (BanditAlgorithm.banditMeasure ν π n).real
        {h : BanditAlgorithm.BanditHistory k n |
          (u : ℝ) * t ≤
            BanditAlgorithm.armStoppedCenteredSum ν i u n h} ≤
        Real.exp (-2 * (u : ℝ) * t ^ 2) ∧
      (BanditAlgorithm.banditMeasure ν π n).real
        {h : BanditAlgorithm.BanditHistory k n |
          BanditAlgorithm.armStoppedCenteredSum ν i u n h ≤
            -(u : ℝ) * t} ≤
        Real.exp (-2 * (u : ℝ) * t ^ 2) := by
  exact ⟨
    BanditAlgorithm.adaptive_armStoppedCenteredSum_upper_tail_half
      ν hν i u ht,
    BanditAlgorithm.adaptive_armStoppedCenteredSum_lower_tail_half
      ν hν i u ht⟩

end OvershootDependency0

section OvershootInterface0

open MeasureTheory ProbabilityTheory
theorem BanditAlgorithm.bandit_adaptive_stopped_centered_sum_tail_half
    {k n : ℕ} (ν : BanditAlgorithm.StochasticBandit k)
    (hν : BanditAlgorithm.IsSubgaussianBandit (1 / 2) ν)
    {π : BanditAlgorithm.BanditPolicy k}
    (i : Fin k) (u : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (BanditAlgorithm.banditMeasure ν π n).real
        {h : BanditAlgorithm.BanditHistory k n |
          (u : ℝ) * t ≤
            BanditAlgorithm.armStoppedCenteredSum ν i u n h} ≤
        Real.exp (-2 * (u : ℝ) * t ^ 2) ∧
      (BanditAlgorithm.banditMeasure ν π n).real
        {h : BanditAlgorithm.BanditHistory k n |
          BanditAlgorithm.armStoppedCenteredSum ν i u n h ≤
            -(u : ℝ) * t} ≤
        Real.exp (-2 * (u : ℝ) * t ^ 2) := by
  apply OvershootDependency0.checked <;> assumption

end OvershootInterface0

/- Complete accepted source by Harry_Xu, submission b77c6c79-9f2a-4027-9ab2-4289d9f113e0. -/
namespace OvershootDependency1
open _root_.BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private theorem bernoulliBandit_ae_mem_Icc_half
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) (i : Fin k) :
    ∀ᵐ x ∂(bernoulliBandit μvec hμ).P i, x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [bernoulliBandit, MeasureTheory.ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure (by simp) _
  · exact Measure.ae_smul_measure (by simp) _

end BanditAlgorithm

theorem checked
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) :
    BanditAlgorithm.IsSubgaussianBandit (1 / 2)
      (BanditAlgorithm.bernoulliBandit μvec hμ) := by
  constructor
  · intro i
    exact Integrable.of_mem_Icc 0 1 measurable_id.aemeasurable
      (BanditAlgorithm.bernoulliBandit_ae_mem_Icc_half μvec hμ i)
  · intro i
    have hsg :=
      ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
        (μ := (BanditAlgorithm.bernoulliBandit μvec hμ).P i)
        (X := id) measurable_id.aemeasurable
        (BanditAlgorithm.bernoulliBandit_ae_mem_Icc_half μvec hμ i)
    simpa [BanditAlgorithm.banditArmMean] using hsg

end OvershootDependency1

section OvershootInterface1

open MeasureTheory ProbabilityTheory
theorem BanditAlgorithm.bernoulliBandit_isSubgaussian_half
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) :
    BanditAlgorithm.IsSubgaussianBandit (1 / 2)
      (BanditAlgorithm.bernoulliBandit μvec hμ) := by
  apply OvershootDependency1.checked <;> assumption

end OvershootInterface1

/- Complete accepted source by Harry_Xu, submission 08f692eb-5bcb-44e0-978b-053c8f8a2fad. -/
namespace OvershootDependency2
open _root_.BanditAlgorithm

open Set Filter Topology

namespace BanditAlgorithm

private noncomputable def klFstExpanded (q p : ℝ) : ℝ :=
  p * Real.log p + (1 - p) * Real.log (1 - p) -
    p * Real.log q - (1 - p) * Real.log (1 - q)

private lemma klFstExpanded_eq
    {p q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    klFstExpanded q p = bernoulliRelativeEntropy p q := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [klFstExpanded, bernoulliRelativeEntropy]
  rcases eq_or_ne p 1 with rfl | hp1
  · simp [klFstExpanded, bernoulliRelativeEntropy]
  rw [klFstExpanded, bernoulliRelativeEntropy,
    Real.log_div hp0 (ne_of_gt hq.1),
    Real.log_div (sub_ne_zero.mpr hp1.symm)
      (sub_ne_zero.mpr (ne_of_lt hq.2).symm)]
  ring

private lemma continuous_klFstExpanded (q : ℝ) :
    Continuous (klFstExpanded q) := by
  unfold klFstExpanded
  have h1 : Continuous (fun p : ℝ ↦ p * Real.log p) :=
    Real.continuous_mul_log
  have h2 : Continuous (fun p : ℝ ↦
      (1 - p) * Real.log (1 - p)) :=
    Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  fun_prop

private lemma hasDerivAt_klFstExpanded
    {p q : ℝ} (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    HasDerivAt (klFstExpanded q)
      (Real.log p - Real.log (1 - p) -
        Real.log q + Real.log (1 - q)) p := by
  unfold klFstExpanded
  have hfirst := Real.hasDerivAt_mul_log hp0
  have honeSub : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) p := by
    convert (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p) using 1 <;> first | rfl | simp only [Pi.sub_apply, id_eq, zero_sub]
  have hsecond :
      HasDerivAt (fun x : ℝ ↦ (1 - x) * Real.log (1 - x))
        (-(Real.log (1 - p) + 1)) p := by
    convert (Real.hasDerivAt_mul_log
      (sub_ne_zero.mpr hp1.symm)).comp p honeSub using 1 <;> (try rfl)
    ring
  have hthird :
      HasDerivAt (fun x : ℝ ↦ x * Real.log q) (Real.log q) p := by
    convert (hasDerivAt_id p).mul_const (Real.log q) using 1 <;> (try rfl) <;> ring
  have hfourth :
      HasDerivAt (fun x : ℝ ↦ (1 - x) * Real.log (1 - q))
        (-Real.log (1 - q)) p := by
    convert honeSub.mul_const (Real.log (1 - q)) using 1 <;> (try rfl) <;> ring
  convert ((hfirst.add hsecond).sub hthird).sub hfourth using 1 <;> (try rfl) <;> ring

private lemma klFstExpanded_deriv_nonpos
    {p q : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpq : p ≤ q) (hq : q ∈ Ioo (0 : ℝ) 1) :
    deriv (klFstExpanded q) p ≤ 0 := by
  rw [(hasDerivAt_klFstExpanded
    (ne_of_gt hp.1) (ne_of_lt hp.2)).deriv]
  have hratio :
      p / (1 - p) ≤ q / (1 - q) := by
    rw [div_le_div_iff₀ (sub_pos.mpr hp.2) (sub_pos.mpr hq.2)]
    nlinarith
  have hlog :
      Real.log (p / (1 - p)) ≤ Real.log (q / (1 - q)) :=
    Real.strictMonoOn_log.monotoneOn
      (div_pos hp.1 (sub_pos.mpr hp.2))
      (div_pos hq.1 (sub_pos.mpr hq.2)) hratio
  rw [Real.log_div (ne_of_gt hp.1)
      (sub_ne_zero.mpr (ne_of_lt hp.2).symm),
    Real.log_div (ne_of_gt hq.1)
      (sub_ne_zero.mpr (ne_of_lt hq.2).symm)] at hlog
  linarith

end BanditAlgorithm

open BanditAlgorithm

theorem checked
    {x y q : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hxy : x ≤ y) (hyq : y ≤ q) (hq : q ∈ Ioo (0 : ℝ) 1) :
    BanditAlgorithm.bernoulliRelativeEntropy y q ≤
      BanditAlgorithm.bernoulliRelativeEntropy x q := by
  rw [← klFstExpanded_eq hq, ← klFstExpanded_eq hq]
  have hcont : ContinuousOn (klFstExpanded q) (Icc x y) :=
    (continuous_klFstExpanded q).continuousOn
  have hdiff : DifferentiableOn ℝ (klFstExpanded q)
      (interior (Icc x y)) := by
    intro z hz
    have hz' : z ∈ Ioo x y := by
      simpa [interior_Icc, hxy] using hz
    rcases hz' with ⟨hzx, hzy⟩
    have hx0 : 0 ≤ x := hx.1
    have hy1 : y < 1 := hyq.trans_lt hq.2
    exact (hasDerivAt_klFstExpanded
      (by linarith) (by linarith))
        |>.differentiableAt.differentiableWithinAt
  have hderiv : ∀ z ∈ interior (Icc x y),
      deriv (klFstExpanded q) z ≤ 0 := by
    intro z hz
    have hz' : z ∈ Ioo x y := by
      simpa [interior_Icc, hxy] using hz
    rcases hz' with ⟨hzx, hzy⟩
    have hx0 : 0 ≤ x := hx.1
    have hy1 : y < 1 := hyq.trans_lt hq.2
    apply klFstExpanded_deriv_nonpos
    · exact ⟨by linarith, by linarith⟩
    · linarith
    · exact hq
  exact (antitoneOn_of_deriv_nonpos (convex_Icc x y)
      hcont hdiff hderiv)
    (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy

end OvershootDependency2

section OvershootInterface2

open Set
theorem BanditAlgorithm.bernoulliRelativeEntropy_antitone_fst
    {x y q : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hxy : x ≤ y) (hyq : y ≤ q) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    BanditAlgorithm.bernoulliRelativeEntropy y q ≤
      BanditAlgorithm.bernoulliRelativeEntropy x q := by
  apply OvershootDependency2.checked <;> assumption

end OvershootInterface2

/- Complete accepted source by Harry_Xu, submission 06afb99a-0019-40f6-a8ae-f9e90cd89fb7. -/
namespace OvershootDependency3
open _root_.BanditAlgorithm

open Set

namespace BanditAlgorithm

/-!
Lattimore--Szepesvári, *Bandit Algorithms*, Lemma 10.2(b), printed p. 134,
and Exercise 10.1, printed p. 141.  The exercise fixes `p` and studies
`g(x) = d(p,x) - 2(p-x)^2`; its derivative has the sign of `x-p`.
-/

private noncomputable def bernoulliPinskerAux (p x : ℝ) : ℝ :=
  p * (Real.log p - Real.log x) +
    (1 - p) * (Real.log (1 - p) - Real.log (1 - x)) -
      2 * (p - x) ^ 2

private lemma hasDerivAt_bernoulliPinskerAux
    {p x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt (bernoulliPinskerAux p)
      ((x - p) / (x * (1 - x)) - 4 * (x - p)) x := by
  have hlogx : HasDerivAt Real.log x⁻¹ x :=
    Real.hasDerivAt_log hx0
  have honeSub : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x :=
    by
      convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1 <;> first | rfl | simp only [Pi.sub_apply, id_eq, zero_sub]
  have hlogOneSub :
      HasDerivAt (fun y : ℝ ↦ Real.log (1 - y))
        ((1 - x)⁻¹ * (-1)) x :=
    (Real.hasDerivAt_log (sub_ne_zero.mpr hx1.symm)).comp x honeSub
  have hfirst :
      HasDerivAt
        (fun y : ℝ ↦ p * (Real.log p - Real.log y))
        (p * (0 - x⁻¹)) x :=
    ((hasDerivAt_const x (Real.log p)).sub hlogx).const_mul p
  have hsecond :
      HasDerivAt
        (fun y : ℝ ↦
          (1 - p) * (Real.log (1 - p) - Real.log (1 - y)))
        ((1 - p) * (0 - (1 - x)⁻¹ * (-1))) x :=
    ((hasDerivAt_const x (Real.log (1 - p))).sub hlogOneSub).const_mul
      (1 - p)
  have hsquare :
      HasDerivAt (fun y : ℝ ↦ -2 * (p - y) ^ 2)
        (-2 * (2 * (p - x) * (-1))) x :=
    by
      convert
        (((hasDerivAt_const x p).sub (hasDerivAt_id x)).pow 2).const_mul (-2)
        using 1 <;> (try rfl)
      simp only [Pi.sub_apply, id_eq]
      ring
  unfold bernoulliPinskerAux
  convert (hfirst.add hsecond).add hsquare using 1 <;> (try rfl)
  · funext y
    simp only [Pi.add_apply]
    ring
  · field_simp [hx0, sub_ne_zero.mpr hx1.symm]
    ring

private lemma bernoulliPinskerAux_continuousAt
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (bernoulliPinskerAux p) p := by
  rcases eq_or_ne p 0 with rfl | hp0
  · have h :
        ContinuousAt (fun x : ℝ ↦ -Real.log (1 - x) - 2 * x ^ 2) 0 := by
      fun_prop (disch := norm_num)
    have heq :
        bernoulliPinskerAux 0 =
          (fun x : ℝ ↦ -Real.log (1 - x) - 2 * x ^ 2) := by
      funext x
      simp [bernoulliPinskerAux]
    rw [heq]
    exact h
  rcases eq_or_ne p 1 with rfl | hp1
  · have h :
        ContinuousAt (fun x : ℝ ↦ -Real.log x - 2 * (1 - x) ^ 2) 1 := by
      fun_prop (disch := norm_num)
    have heq :
        bernoulliPinskerAux 1 =
          (fun x : ℝ ↦ -Real.log x - 2 * (1 - x) ^ 2) := by
      funext x
      simp [bernoulliPinskerAux]
    rw [heq]
    exact h
  · unfold bernoulliPinskerAux
    have hpOne : 1 - p ≠ 0 := sub_ne_zero.mpr hp1.symm
    fun_prop

private lemma bernoulliPinskerAux_eq_entropy_sub
    {p q : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hq : q ∈ Ioo (0 : ℝ) 1) :
    bernoulliPinskerAux p q =
      bernoulliRelativeEntropy p q - 2 * (p - q) ^ 2 := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [bernoulliPinskerAux, bernoulliRelativeEntropy]
  rcases eq_or_ne p 1 with rfl | hp1
  · simp [bernoulliPinskerAux, bernoulliRelativeEntropy]
  have hq0 : q ≠ 0 := ne_of_gt hq.1
  have hq1 : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq.2)
  have hpOne : 1 - p ≠ 0 := sub_ne_zero.mpr hp1.symm
  rw [bernoulliPinskerAux, bernoulliRelativeEntropy,
    Real.log_div hp0 hq0, Real.log_div hpOne hq1]

private lemma bernoulliPinskerAux_deriv_nonpos
    {p x : ℝ} (hxp : x < p) (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (bernoulliPinskerAux p) x ≤ 0 := by
  have hden : 0 < x * (1 - x) := mul_pos hx.1 (sub_pos.mpr hx.2)
  have hcoef : 0 ≤ 1 / (x * (1 - x)) - 4 := by
    rw [sub_nonneg, le_div_iff₀ hden]
    nlinarith [sq_nonneg (2 * x - 1)]
  rw [(hasDerivAt_bernoulliPinskerAux
    (ne_of_gt hx.1) (ne_of_lt hx.2)).deriv]
  have heq :
      (x - p) / (x * (1 - x)) - 4 * (x - p) =
        (x - p) * (1 / (x * (1 - x)) - 4) := by
    field_simp [ne_of_gt hden]
  rw [heq]
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxp.le) hcoef

private lemma bernoulliPinskerAux_deriv_nonneg
    {p x : ℝ} (hpx : p < x) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ deriv (bernoulliPinskerAux p) x := by
  have hden : 0 < x * (1 - x) := mul_pos hx.1 (sub_pos.mpr hx.2)
  have hcoef : 0 ≤ 1 / (x * (1 - x)) - 4 := by
    rw [sub_nonneg, le_div_iff₀ hden]
    nlinarith [sq_nonneg (2 * x - 1)]
  rw [(hasDerivAt_bernoulliPinskerAux
    (ne_of_gt hx.1) (ne_of_lt hx.2)).deriv]
  have heq :
      (x - p) / (x * (1 - x)) - 4 * (x - p) =
        (x - p) * (1 / (x * (1 - x)) - 4) := by
    field_simp [ne_of_gt hden]
  rw [heq]
  exact mul_nonneg (sub_nonneg.mpr hpx.le) hcoef

end BanditAlgorithm

open BanditAlgorithm

theorem checked (p q : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    2 * (p - q) ^ 2 ≤ BanditAlgorithm.bernoulliRelativeEntropy p q := by
  have hdiffLeft :
      DifferentiableOn ℝ (bernoulliPinskerAux p) (Ioo 0 p) := by
    intro x hx
    exact (hasDerivAt_bernoulliPinskerAux
      (ne_of_gt hx.1)
      (ne_of_lt (hx.2.trans_le hp.2))).differentiableAt.differentiableWithinAt
  have hdiffRight :
      DifferentiableOn ℝ (bernoulliPinskerAux p) (Ioo p 1) := by
    intro x hx
    exact (hasDerivAt_bernoulliPinskerAux
      (ne_of_gt (hp.1.trans_lt hx.1))
      (ne_of_lt hx.2)).differentiableAt.differentiableWithinAt
  have hmin :
      IsMinOn (bernoulliPinskerAux p) (Ioo 0 1) p :=
    isMinOn_Ioo_of_deriv
      (bernoulliPinskerAux_continuousAt hp)
      hdiffLeft hdiffRight
      (fun x hx ↦ bernoulliPinskerAux_deriv_nonpos
        hx.2 ⟨hx.1, hx.2.trans_le hp.2⟩)
      (fun x hx ↦ bernoulliPinskerAux_deriv_nonneg
        hx.1 ⟨hp.1.trans_lt hx.1, hx.2⟩)
  have haux : bernoulliPinskerAux p p ≤ bernoulliPinskerAux p q :=
    hmin hq
  have hself : bernoulliPinskerAux p p = 0 := by
    simp [bernoulliPinskerAux]
  rw [hself, bernoulliPinskerAux_eq_entropy_sub hp hq] at haux
  linarith

end OvershootDependency3

section OvershootInterface3

theorem BanditAlgorithm.bernoulli_relative_entropy_pinsker (p q : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    2 * (p - q) ^ 2 ≤ bernoulliRelativeEntropy p q := by
  apply OvershootDependency3.checked <;> assumption

end OvershootInterface3

/- Complete accepted source by Harry_Xu, submission 9d421ea9-81de-485b-9485-5548f3aec3d7. -/
namespace OvershootDependency4
open _root_.BanditAlgorithm

open Set Filter Topology

namespace BanditAlgorithm

private lemma hasDerivAt_bernoulliRelativeEntropy_snd
    {p x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt (fun q ↦ bernoulliRelativeEntropy p q)
      ((x - p) / (x * (1 - x))) x := by
  have honeSub : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1 <;> first | rfl | simp only [Pi.sub_apply, id_eq, zero_sub]
  rcases eq_or_ne p 0 with rfl | hp0
  · have hbase : HasDerivAt (fun y : ℝ ↦ -Real.log (1 - y))
        (1 / (1 - x)) x := by
      convert
        ((Real.hasDerivAt_log (sub_ne_zero.mpr hx1.symm)).comp x honeSub).neg
        using 1 <;> (try rfl) <;> field_simp [sub_ne_zero.mpr hx1.symm]
    have heq : (fun y : ℝ ↦ bernoulliRelativeEntropy 0 y) =ᶠ[𝓝 x]
        fun y ↦ -Real.log (1 - y) := by
      filter_upwards [eventually_ne_nhds hx1] with y hy
      simp [bernoulliRelativeEntropy, Real.log_inv,
        sub_ne_zero.mpr hy.symm]
    convert hbase.congr_of_eventuallyEq heq using 1 <;> (try rfl)
    field_simp [hx0, sub_ne_zero.mpr hx1.symm]
    ring
  rcases eq_or_ne p 1 with rfl | hp1
  · have hbase : HasDerivAt (fun y : ℝ ↦ -Real.log y) (-x⁻¹) x :=
      (Real.hasDerivAt_log hx0).neg
    have heq : (fun y : ℝ ↦ bernoulliRelativeEntropy 1 y) =ᶠ[𝓝 x]
        fun y ↦ -Real.log y := by
      filter_upwards [eventually_ne_nhds hx0] with y hy
      simp [bernoulliRelativeEntropy, Real.log_inv, hy]
    convert hbase.congr_of_eventuallyEq heq using 1 <;> (try rfl)
    field_simp [hx0, sub_ne_zero.mpr hx1.symm]
    ring
  · have hlogx : HasDerivAt Real.log x⁻¹ x :=
      Real.hasDerivAt_log hx0
    have hlogOneSub :
        HasDerivAt (fun y : ℝ ↦ Real.log (1 - y))
          ((1 - x)⁻¹ * (-1)) x :=
      (Real.hasDerivAt_log (sub_ne_zero.mpr hx1.symm)).comp x honeSub
    have hfirst :
        HasDerivAt (fun y : ℝ ↦ p * (Real.log p - Real.log y))
          (p * (0 - x⁻¹)) x :=
      ((hasDerivAt_const x (Real.log p)).sub hlogx).const_mul p
    have hsecond :
        HasDerivAt
          (fun y : ℝ ↦
            (1 - p) * (Real.log (1 - p) - Real.log (1 - y)))
          ((1 - p) * (0 - (1 - x)⁻¹ * (-1))) x :=
      ((hasDerivAt_const x (Real.log (1 - p))).sub hlogOneSub).const_mul
        (1 - p)
    have hbase := hfirst.add hsecond
    have heq :
        (fun y : ℝ ↦ bernoulliRelativeEntropy p y) =ᶠ[𝓝 x]
          fun y ↦ p * (Real.log p - Real.log y) +
            (1 - p) * (Real.log (1 - p) - Real.log (1 - y)) := by
      filter_upwards [eventually_ne_nhds hx0,
        eventually_ne_nhds hx1] with y hy0 hy1
      rw [bernoulliRelativeEntropy,
        Real.log_div hp0 hy0,
        Real.log_div (sub_ne_zero.mpr hp1.symm)
          (sub_ne_zero.mpr hy1.symm)]
    convert hbase.congr_of_eventuallyEq heq using 1 <;> (try rfl)
    field_simp [hx0, sub_ne_zero.mpr hx1.symm]
    ring

lemma bernoulliRelativeEntropy_mono_snd
    {p x y : ℝ} (hpx : p ≤ x) (hx0 : 0 < x)
    (hxy : x ≤ y) (hy1 : y < 1) :
    bernoulliRelativeEntropy p x ≤ bernoulliRelativeEntropy p y := by
  have hcont : ContinuousOn (fun q ↦ bernoulliRelativeEntropy p q) (Icc x y) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      have : 0 < z := lt_of_lt_of_le hx0 hz.1
      exact ne_of_gt this
    have hz1 : z ≠ 1 := by
      have : z < 1 := lt_of_le_of_lt hz.2 hy1
      exact ne_of_lt this
    exact (hasDerivAt_bernoulliRelativeEntropy_snd hz0 hz1).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ
      (fun q ↦ bernoulliRelativeEntropy p q) (interior (Icc x y)) := by
    intro z hz
    have hz' : z ∈ Ioo x y := by simpa [interior_Icc, hxy] using hz
    rcases hz' with ⟨hzx, hzy⟩
    exact (hasDerivAt_bernoulliRelativeEntropy_snd
      (by linarith) (by linarith)).differentiableAt.differentiableWithinAt
  have hderiv : ∀ z ∈ interior (Icc x y),
      0 ≤ deriv (fun q ↦ bernoulliRelativeEntropy p q) z := by
    intro z hz
    have hz' : z ∈ Ioo x y := by simpa [interior_Icc, hxy] using hz
    rcases hz' with ⟨hzx, hzy⟩
    rw [(hasDerivAt_bernoulliRelativeEntropy_snd
      (by linarith) (by linarith)).deriv]
    exact div_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  exact (monotoneOn_of_deriv_nonneg (convex_Icc x y) hcont hdiff hderiv)
    (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy

lemma bernoulliRelativeEntropy_self_index
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    bernoulliRelativeEntropy p p = 0 := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [bernoulliRelativeEntropy]
  rcases eq_or_ne p 1 with rfl | hp1
  · simp [bernoulliRelativeEntropy]
  simp [bernoulliRelativeEntropy, div_self hp0,
    div_self (sub_ne_zero.mpr hp1.symm)]

lemma klucb_threshold_feasible_of_le_sSup
    {p β q : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hβ : 0 ≤ β) (hq : q ∈ Ioo (0 : ℝ) 1) (hpq : p ≤ q)
    (hindex : q ≤ sSup {x ∈ Icc (0 : ℝ) 1 |
      bernoulliRelativeEntropy p x ≤ β ∧
        (x = 0 → p = 0) ∧ (x = 1 → p = 1)}) :
    bernoulliRelativeEntropy p q ≤ β := by
  let F : Set ℝ := {x ∈ Icc (0 : ℝ) 1 |
    bernoulliRelativeEntropy p x ≤ β ∧
      (x = 0 → p = 0) ∧ (x = 1 → p = 1)}
  have hpF : p ∈ F := by
    refine ⟨hp, ?_, ?_, ?_⟩
    · rw [bernoulliRelativeEntropy_self_index hp]
      exact hβ
    · exact fun h ↦ h
    · exact fun h ↦ h
  have hFne : F.Nonempty := ⟨p, hpF⟩
  by_contra hnot
  have hbad : β < bernoulliRelativeEntropy p q := lt_of_not_ge hnot
  by_cases hpqeq : p = q
  · subst q
    rw [bernoulliRelativeEntropy_self_index hp] at hbad
    linarith
  have hpqlt : p < q := lt_of_le_of_ne hpq hpqeq
  have hcont :
      ContinuousAt (fun x ↦ bernoulliRelativeEntropy p x) q :=
    (hasDerivAt_bernoulliRelativeEntropy_snd
      (ne_of_gt hq.1) (ne_of_lt hq.2)).continuousAt
  have hev : {x : ℝ | β < bernoulliRelativeEntropy p x} ∈ 𝓝 q :=
    hcont (isOpen_Ioi.mem_nhds hbad)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hev
  let η := min δ (q - p)
  let r := q - η / 2
  have hηpos : 0 < η := lt_min hδ (sub_pos.mpr hpqlt)
  have hηδ : η ≤ δ := min_le_left _ _
  have hηgap : η ≤ q - p := min_le_right _ _
  have hrq : r < q := by dsimp [r]; linarith
  have hpr : p < r := by dsimp [r]; linarith
  have hr0 : 0 < r := lt_of_le_of_lt hp.1 hpr
  have hrbad : β < bernoulliRelativeEntropy p r := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [r]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hupper : ∀ x ∈ F, x ≤ r := by
    intro x hxF
    by_contra hxr
    have hrx : r < x := lt_of_not_ge hxr
    have hx1 : x < 1 := by
      have hxle := hxF.1.2
      exact lt_of_le_of_ne hxle (fun hxone ↦ by
        have hpone := hxF.2.2.2 hxone
        linarith [hpqlt, hq.2])
    have hmono :
        bernoulliRelativeEntropy p r ≤
          bernoulliRelativeEntropy p x :=
      bernoulliRelativeEntropy_mono_snd hpr.le hr0 hrx.le hx1
    linarith [hxF.2.1]
  have hsup : sSup F ≤ r := csSup_le hFne hupper
  have hseteq : F = {x ∈ Icc (0 : ℝ) 1 |
      bernoulliRelativeEntropy p x ≤ β ∧
        (x = 0 → p = 0) ∧ (x = 1 → p = 1)} := by
    rfl
  have hqle : q ≤ sSup F := by
    rw [hseteq]
    exact hindex
  linarith

lemma le_klucb_sSup_of_threshold_feasible
    {p β q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hfeas : bernoulliRelativeEntropy p q ≤ β) :
    q ≤ sSup {x ∈ Icc (0 : ℝ) 1 |
      bernoulliRelativeEntropy p x ≤ β ∧
        (x = 0 → p = 0) ∧ (x = 1 → p = 1)} := by
  apply le_csSup
  · refine ⟨1, ?_⟩
    intro x hx
    exact hx.1.2
  · exact ⟨⟨hq.1.le, hq.2.le⟩, hfeas,
      (fun h ↦ (hq.1.ne' h).elim),
      (fun h ↦ (hq.2.ne h).elim)⟩

end BanditAlgorithm

theorem checked
    {k n : ℕ} (i : Fin k) (h : BanditAlgorithm.BanditHistory k n)
    (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hp : BanditAlgorithm.armEmpiricalMean i h ∈ Set.Icc (0 : ℝ) 1) :
    q ≤ BanditAlgorithm.klucbIndex i h ↔
      BanditAlgorithm.klucbTruncatedRelativeEntropy
          (BanditAlgorithm.armEmpiricalMean i h) q ≤
        Real.log (BanditAlgorithm.klucbExploration (n + 1)) /
          BanditAlgorithm.armPullCount i h := by
  let p := BanditAlgorithm.armEmpiricalMean i h
  let β := Real.log (BanditAlgorithm.klucbExploration (n + 1)) /
    BanditAlgorithm.armPullCount i h
  have hf : 1 ≤ BanditAlgorithm.klucbExploration (n + 1) := by
    rw [BanditAlgorithm.klucbExploration]
    exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hβ : 0 ≤ β :=
    div_nonneg (Real.log_nonneg hf) (Nat.cast_nonneg _)
  constructor
  · intro hindex
    by_cases hpq : p ≤ q
    · rw [BanditAlgorithm.klucbTruncatedRelativeEntropy, if_pos hpq]
      apply BanditAlgorithm.klucb_threshold_feasible_of_le_sSup
        hp hβ hq hpq
      simpa [BanditAlgorithm.klucbIndex, p, β] using hindex
    · rw [BanditAlgorithm.klucbTruncatedRelativeEntropy, if_neg hpq]
      exact hβ
  · intro hfeas
    by_cases hpq : p ≤ q
    · rw [BanditAlgorithm.klucbTruncatedRelativeEntropy, if_pos hpq] at hfeas
      have hle := BanditAlgorithm.le_klucb_sSup_of_threshold_feasible hq hfeas
      simpa [BanditAlgorithm.klucbIndex, p, β] using hle
    · have hqp : q ≤ p := le_of_not_ge hpq
      apply hqp.trans
      rw [BanditAlgorithm.klucbIndex]
      apply le_csSup
      · refine ⟨1, ?_⟩
        intro x hx
        exact hx.1.2
      · refine ⟨hp, ?_, ?_, ?_⟩
        · rw [BanditAlgorithm.bernoulliRelativeEntropy_self_index hp]
          exact hβ
        · exact fun h0 ↦ h0
        · exact fun h1 ↦ h1

end OvershootDependency4

section OvershootInterface4

open MeasureTheory ProbabilityTheory
theorem BanditAlgorithm.klucb_index_threshold_feasible
    {k n : ℕ} (i : Fin k) (h : BanditAlgorithm.BanditHistory k n)
    (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hp : BanditAlgorithm.armEmpiricalMean i h ∈ Set.Icc (0 : ℝ) 1) :
    q ≤ BanditAlgorithm.klucbIndex i h ↔
      BanditAlgorithm.klucbTruncatedRelativeEntropy
          (BanditAlgorithm.armEmpiricalMean i h) q ≤
        Real.log (BanditAlgorithm.klucbExploration (n + 1)) /
          BanditAlgorithm.armPullCount i h := by
  apply OvershootDependency4.checked <;> assumption
end OvershootInterface4


/-
The closed helper block below is reproduced unchanged from Harry_Xu's accepted
Prove2Me submission 1ebc4461-4a9e-4996-b6fb-fa7ac2175878 for theorem
d3ba2b23-aaff-45f3-aebc-080e1d80ddd7. It supplies adaptive Bernoulli rank
counting and the feasibility-count estimate. The new proof below connects the
registered KL-index count to that estimate; no private imported helper is used.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BanditAlgorithm

private theorem pullCount_cast_eq_sum_indicator_over {k n : ℕ}
    (i : Fin k) (h : BanditHistory k n) :
    (armPullCount i h : ℝ) =
      ∑ t, if (h t).1 = i then 1 else 0 := by
  classical
  rw [armPullCount]
  have hs : {t | (h t).1 = i}.toFinset =
      Finset.univ.filter (fun t ↦ (h t).1 = i) := by
    ext t
    simp
  rw [hs]
  simpa using
    (Finset.sum_boole (R := ℝ)
      (fun t : Fin n ↦ (h t).1 = i) Finset.univ).symm

private theorem measurable_armPullCount_over {k n : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) := by
  simp_rw [pullCount_cast_eq_sum_indicator_over]
  apply Finset.measurable_sum
  intro t ht
  have hcoord : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact Measurable.ite
    ((measurableSet_singleton i).preimage hcoord)
    measurable_const measurable_const

private theorem armPullCount_snoc_over {k n : ℕ}
    (i : Fin k) (h : BanditHistory k n) (z : Fin k × ℝ) :
    armPullCount i (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armPullCount i h + if z.1 = i then 1 else 0 := by
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_add, pullCount_cast_eq_sum_indicator_over,
    pullCount_cast_eq_sum_indicator_over i h, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

private theorem armPullCount_le_horizon_over {k n : ℕ}
    (i : Fin k) (h : BanditHistory k n) :
    armPullCount i h ≤ n := by
  rw [armPullCount]
  calc
    {t | (h t).1 = i}.toFinset.card ≤ Finset.univ.card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = n := Fintype.card_fin n

private theorem measurable_armEmpiricalMean_over {k m : ℕ} (i : Fin k) :
    Measurable (armEmpiricalMean (n := m) i) := by
  have hsum :
      (fun h : BanditHistory k m ↦
        ∑ t ∈ {t | (h t).1 = i}.toFinset, (h t).2) =
      fun h ↦ ∑ t, if (h t).1 = i then (h t).2 else 0 := by
    funext h
    have hs : {t | (h t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp
    rw [hs, Finset.sum_filter]
  have hnum : Measurable
      (fun h : BanditHistory k m ↦
        ∑ t ∈ {t | (h t).1 = i}.toFinset, (h t).2) := by
    rw [hsum]
    apply Finset.measurable_sum
    intro t ht
    have ha : Measurable (fun h : BanditHistory k m ↦ (h t).1) :=
      measurable_fst.comp (measurable_pi_apply t)
    have hx : Measurable (fun h : BanditHistory k m ↦ (h t).2) :=
      measurable_snd.comp (measurable_pi_apply t)
    exact Measurable.ite ((measurableSet_singleton i).preimage ha)
      hx measurable_const
  unfold armEmpiricalMean
  exact hnum.div (measurable_armPullCount_over i)

private theorem measurable_banditHistoryPrefixAt_over
    {k n : ℕ} (r : Fin n) :
    Measurable
      (fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r) := by
  rw [measurable_pi_iff]
  intro s
  exact measurable_pi_apply
    (⟨s.val, lt_trans s.isLt r.isLt⟩ : Fin n)

private theorem measurable_armStoppedCenteredSum_over {k : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ) (m : ℕ) :
    Measurable (armStoppedCenteredSum ν i u m) := by
  induction m with
  | zero => simp [armStoppedCenteredSum]
  | succ m ih =>
      have hinit : Measurable
          (fun h : BanditHistory k (m + 1) ↦ Fin.init h) := by
        rw [measurable_pi_iff]
        intro t
        exact measurable_pi_apply (Fin.castSucc t)
      have hlast : Measurable
          (fun h : BanditHistory k (m + 1) ↦ h (Fin.last m)) :=
        measurable_pi_apply (Fin.last m)
      have hcount : Measurable (fun h : BanditHistory k (m + 1) ↦
          (armPullCount i (Fin.init h) : ℝ)) :=
        (measurable_armPullCount_over i).comp hinit
      have hlt : MeasurableSet {h : BanditHistory k (m + 1) |
          armPullCount i (Fin.init h) < u} := by
        simpa only [Nat.cast_lt] using
          measurableSet_lt hcount
            (measurable_const : Measurable
              (fun _ : BanditHistory k (m + 1) ↦ (u : ℝ)))
      have heq : MeasurableSet {h : BanditHistory k (m + 1) |
          (h (Fin.last m)).1 = i} :=
        (measurableSet_singleton i).preimage hlast.fst
      change Measurable (fun h : BanditHistory k (m + 1) ↦
        armStoppedCenteredSum ν i u m (Fin.init h) +
          if armPullCount i (Fin.init h) < u ∧
              (h (Fin.last m)).1 = i then
            (h (Fin.last m)).2 - banditArmMean ν i else 0)
      exact (ih.comp hinit).add
        (Measurable.ite (hlt.inter heq)
          (hlast.snd.sub measurable_const) measurable_const)

private theorem prefixAt_snoc_castSucc_over {k n : ℕ}
    (h : BanditHistory k n) (z : Fin k × ℝ) (r : Fin n) :
    banditHistoryPrefixAt
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) r.castSucc =
      banditHistoryPrefixAt h r := by
  funext s
  unfold banditHistoryPrefixAt
  have hsr : s.val < r.val := by simpa using s.isLt
  have hsn : s.val < n := lt_trans hsr r.isLt
  rw [Fin.snoc]
  rw [dif_pos hsn]
  simp

private theorem prefixAt_snoc_last_over {k n : ℕ}
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    banditHistoryPrefixAt
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) (Fin.last n) = h := by
  funext s
  simp [banditHistoryPrefixAt, Fin.snoc]

private theorem armStoppedCenteredSum_snoc_over {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    armStoppedCenteredSum ν i u (m + 1)
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armStoppedCenteredSum ν i u m h +
        if armPullCount i h < u ∧ z.1 = i then
          z.2 - banditArmMean ν i
        else 0 := by
  simp [armStoppedCenteredSum]

private noncomputable def armCenteredSumOver {k n : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (h : BanditHistory k n) : ℝ :=
  ∑ t, if (h t).1 = i then (h t).2 - banditArmMean ν i else 0

private theorem armCenteredSumOver_snoc {k n : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (h : BanditHistory k n)
    (z : Fin k × ℝ) :
    armCenteredSumOver ν i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armCenteredSumOver ν i h +
        if z.1 = i then z.2 - banditArmMean ν i else 0 := by
  simp only [armCenteredSumOver, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

private theorem armStoppedCenteredSum_eq_pullCount_mul_over
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (hcount : armPullCount i h ≤ u) :
    armStoppedCenteredSum ν i u m h =
      (armPullCount i h : ℝ) *
        (armEmpiricalMean i h - banditArmMean ν i) := by
  classical
  have hstop :
      armStoppedCenteredSum ν i u m h = armCenteredSumOver ν i h := by
    induction m with
    | zero => simp [armStoppedCenteredSum, armCenteredSumOver]
    | succ m ih =>
        rw [← Fin.snoc_init_self h] at hcount ⊢
        rw [armPullCount_snoc_over] at hcount
        rw [armStoppedCenteredSum_snoc_over, armCenteredSumOver_snoc]
        by_cases hi : (h (Fin.last m)).1 = i
        · have hprev : armPullCount i (Fin.init h) < u := by
            simp [hi] at hcount
            omega
          rw [if_pos ⟨hprev, hi⟩, if_pos hi,
            ih (Fin.init h) (Nat.le_of_lt hprev)]
        · have hprev : armPullCount i (Fin.init h) ≤ u := by
            simpa [hi] using hcount
          rw [if_neg (fun hc ↦ hi hc.2), if_neg hi,
            ih (Fin.init h) hprev]
  rw [hstop]
  let S : Finset (Fin m) := {t | (h t).1 = i}.toFinset
  have hsum : (∑ t, if (h t).1 = i then
      (h t).2 - banditArmMean ν i else 0) =
      ∑ t ∈ S, ((h t).2 - banditArmMean ν i) := by
    have hS : S = Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp [S]
    rw [hS, Finset.sum_filter]
  rw [armCenteredSumOver, hsum]
  change (∑ t ∈ S, ((h t).2 - banditArmMean ν i)) =
    (S.card : ℝ) *
      ((∑ t ∈ S, (h t).2) / (S.card : ℝ) - banditArmMean ν i)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  by_cases hc : S.card = 0
  · have hS0 : S = ∅ := Finset.card_eq_zero.mp hc
    simp [hS0]
  · have hcast : (S.card : ℝ) ≠ 0 := by exact_mod_cast hc
    field_simp

private theorem armPullCount_prefix_le_over
    {k n : ℕ} (i : Fin k) (h : BanditHistory k n) (r : Fin n) :
    armPullCount i (banditHistoryPrefixAt h r) ≤ armPullCount i h := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
      rw [← Fin.snoc_init_self h]
      refine Fin.lastCases ?_ (fun s ↦ ?_) r
      · rw [prefixAt_snoc_last_over, armPullCount_snoc_over]
        by_cases hz : (h (Fin.last n)).1 = i <;> simp [hz]
      · rw [prefixAt_snoc_castSucc_over, armPullCount_snoc_over]
        exact (ih (Fin.init h) s).trans
          (Nat.le_add_right _ _)

private theorem armStoppedCenteredSum_stable_after_prefix_over
    {k n : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (h : BanditHistory k n) (r : Fin n) (u : ℕ)
    (hcount : armPullCount i (banditHistoryPrefixAt h r) = u) :
    armStoppedCenteredSum ν i u n h =
      armStoppedCenteredSum ν i u r.val (banditHistoryPrefixAt h r) := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
      rw [← Fin.snoc_init_self h] at hcount ⊢
      revert hcount
      refine Fin.lastCases ?_ (fun s hcount ↦ ?_) r
      · intro hcount
        rw [prefixAt_snoc_last_over] at hcount ⊢
        rw [armStoppedCenteredSum_snoc_over]
        rw [if_neg (by
          intro hc
          exact Nat.ne_of_lt hc.1 hcount)]
        simp
      · rw [prefixAt_snoc_castSucc_over] at hcount ⊢
        rw [armStoppedCenteredSum_snoc_over]
        have hprefix_le :
            u ≤ armPullCount i (Fin.init h) := by
          rw [← hcount]
          exact armPullCount_prefix_le_over i (Fin.init h) s
        rw [if_neg (by
          intro hc
          omega)]
        simpa using ih (Fin.init h) s hcount

private theorem prefixAt_prefixAt_over
    {k n : ℕ} (h : BanditHistory k n) (s : Fin n)
    (r : Fin s.val) :
    banditHistoryPrefixAt (banditHistoryPrefixAt h s) r =
      banditHistoryPrefixAt h
        (⟨r.val, lt_trans r.isLt s.isLt⟩ : Fin n) := by
  funext q
  rfl

private theorem selected_prefix_count_lt_total_over
    {k n : ℕ} (i : Fin k) (h : BanditHistory k n) (r : Fin n)
    (hselected : (h r).1 = i) :
    armPullCount i (banditHistoryPrefixAt h r) < armPullCount i h := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
      rw [← Fin.snoc_init_self h] at hselected ⊢
      revert hselected
      refine Fin.lastCases ?_ (fun s hselected ↦ ?_) r
      · intro hselected
        rw [prefixAt_snoc_last_over, armPullCount_snoc_over]
        simp only [Fin.snoc_last] at hselected
        simp [hselected]
      · rw [prefixAt_snoc_castSucc_over, armPullCount_snoc_over]
        have hselected' : ((Fin.init h) s).1 = i := by
          simpa using hselected
        exact (ih (Fin.init h) s hselected').trans_le (by omega)

private theorem selected_prefix_count_strict_over
    {k n : ℕ} (i : Fin k) (h : BanditHistory k n)
    (r s : Fin n) (hrs : r.val < s.val)
    (hselected : (h r).1 = i) :
    armPullCount i (banditHistoryPrefixAt h r) <
      armPullCount i (banditHistoryPrefixAt h s) := by
  let r' : Fin s.val := ⟨r.val, hrs⟩
  have hsel' : ((banditHistoryPrefixAt h s) r').1 = i := by
    exact hselected
  have hlt :=
    selected_prefix_count_lt_total_over i (banditHistoryPrefixAt h s) r' hsel'
  simpa [r', prefixAt_prefixAt_over] using hlt

private theorem selected_prefix_count_injOn_over
    {k n : ℕ} (i : Fin k) (h : BanditHistory k n)
    (R : Finset (Fin n))
    (hR : ∀ r ∈ R, (h r).1 = i) :
    Set.InjOn
      (fun r : Fin n ↦ armPullCount i (banditHistoryPrefixAt h r)) R := by
  intro r hr s hs heq
  rcases lt_trichotomy r.val s.val with hrs | hrs | hrs
  · have hlt := selected_prefix_count_strict_over i h r s hrs (hR r hr)
    exact (Nat.ne_of_lt hlt heq).elim
  · exact Fin.ext hrs
  · have hlt := selected_prefix_count_strict_over i h s r hrs (hR s hs)
    exact (Nat.ne_of_lt hlt heq.symm).elim

private theorem banditArmMean_bernoulli_over
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (j : Fin k) :
    banditArmMean ν j = μvec j := by
  rw [hν, banditArmMean, bernoulliBandit]
  change (∫ x : ℝ, x ∂(ENNReal.ofReal (μvec j) • Measure.dirac (1 : ℝ) +
    ENNReal.ofReal (1 - μvec j) • Measure.dirac (0 : ℝ))) = μvec j
  rw [integral_add_measure
    ((integrable_dirac (by finiteness) :
      Integrable (fun x : ℝ ↦ x) (Measure.dirac (1 : ℝ))).smul_measure
        ENNReal.ofReal_ne_top)
    ((integrable_dirac (by finiteness) :
      Integrable (fun x : ℝ ↦ x) (Measure.dirac (0 : ℝ))).smul_measure
        ENNReal.ofReal_ne_top)]
  rcases hμ j with ⟨h0, h1⟩
  simp [ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (show 0 ≤ 1 - μvec j by linarith)]

private def HistoryRewardsBernoulliOver {k n : ℕ}
    (h : BanditHistory k n) : Prop :=
  ∀ t, (h t).2 = 0 ∨ (h t).2 = 1

private theorem empiricalMean_mem_Icc_over
    {k n : ℕ} (j : Fin k) (h : BanditHistory k n)
    (hh : HistoryRewardsBernoulliOver h) :
    armEmpiricalMean j h ∈ Set.Icc (0 : ℝ) 1 := by
  let S : Finset (Fin n) := {t | (h t).1 = j}.toFinset
  have hreward (t : Fin n) : 0 ≤ (h t).2 ∧ (h t).2 ≤ 1 := by
    rcases hh t with ht | ht <;> simp [ht]
  have hnum0 : 0 ≤ ∑ t ∈ S, (h t).2 :=
    Finset.sum_nonneg fun t _ ↦ (hreward t).1
  have hnumle : (∑ t ∈ S, (h t).2) ≤ (S.card : ℝ) := by
    calc
      (∑ t ∈ S, (h t).2) ≤ ∑ _t ∈ S, (1 : ℝ) :=
        Finset.sum_le_sum fun t _ ↦ (hreward t).2
      _ = (S.card : ℝ) := by simp
  unfold armEmpiricalMean
  change (∑ t ∈ S, (h t).2) / (S.card : ℝ) ∈ Set.Icc (0 : ℝ) 1
  by_cases hc : S.card = 0
  · simp [hc]
  · have hcpos : 0 < (S.card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hc
    exact ⟨div_nonneg hnum0 hcpos.le, (div_le_one hcpos).2 hnumle⟩

private theorem historyRewardsBernoulliOver_prefix
    {k n : ℕ} (h : BanditHistory k n)
    (hh : HistoryRewardsBernoulliOver h) (r : Fin n) :
    HistoryRewardsBernoulliOver (banditHistoryPrefixAt h r) := by
  intro t
  exact hh ⟨t.val, lt_trans t.isLt r.isLt⟩

private theorem bernoulli_arm_ae_reward_over
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (j : Fin k) :
    ∀ᵐ x ∂ν.P j, x = 0 ∨ x = 1 := by
  rw [hν, bernoulliBandit]
  change ∀ᵐ x ∂(ENNReal.ofReal (μvec j) • Measure.dirac (1 : ℝ) +
      ENNReal.ofReal (1 - μvec j) • Measure.dirac (0 : ℝ)),
    x = 0 ∨ x = 1
  rw [MeasureTheory.ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure (by simp) _
  · exact Measure.ae_smul_measure (by simp) _

private theorem banditStepKernel_ae_reward_bernoulli_over
    {k m : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (h : BanditHistory k m) :
    ∀ᵐ z ∂banditStepKernel ν π m h, z.2 = 0 ∨ z.2 = 1 := by
  rw [banditStepKernel]
  apply Kernel.ae_compProd_of_ae_ae
  · exact (measurableSet_eq_fun measurable_snd measurable_const).union
      (measurableSet_eq_fun measurable_snd measurable_const)
  · filter_upwards with j
    rw [Kernel.comap_apply]
    exact bernoulli_arm_ae_reward_over μvec hμ ν hν j

private theorem measurableSet_historyRewardsBernoulliOver
    {k n : ℕ} :
    MeasurableSet {h : BanditHistory k n |
      HistoryRewardsBernoulliOver h} := by
  classical
  unfold HistoryRewardsBernoulliOver
  convert MeasurableSet.iInter (fun t : Fin n ↦
    (measurableSet_eq_fun
      (measurable_snd.comp (measurable_pi_apply t))
      (measurable_const :
        Measurable (fun _ : BanditHistory k n ↦ (0 : ℝ)))).union
    (measurableSet_eq_fun
      (measurable_snd.comp (measurable_pi_apply t))
      (measurable_const :
        Measurable (fun _ : BanditHistory k n ↦ (1 : ℝ))))) using 1
  ext h
  simp

private theorem banditMeasure_ae_historyRewardsBernoulliOver
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) :
    ∀ n : ℕ, ∀ᵐ h ∂banditMeasure ν π n,
      HistoryRewardsBernoulliOver h := by
  intro n
  induction n with
  | zero => simp [banditMeasure, HistoryRewardsBernoulliOver]
  | succ n ih =>
      rw [banditMeasure]
      apply (ae_map_iff measurable_banditHistorySnoc.aemeasurable
        (measurableSet_historyRewardsBernoulliOver
          (k := k) (n := n + 1))).2
      apply Measure.ae_compProd_of_ae_ae
      · exact measurable_banditHistorySnoc
          (measurableSet_historyRewardsBernoulliOver
            (k := k) (n := n + 1))
      filter_upwards [ih] with h hh
      filter_upwards
        [banditStepKernel_ae_reward_bernoulli_over
          μvec hμ ν hν π h] with z hz
      intro t
      refine Fin.lastCases ?_ (fun s ↦ ?_) t
      · simpa using hz
      · simpa using hh s

private theorem klucbExploration_pos_over (t : ℕ) :
    0 < klucbExploration t := by
  rw [klucbExploration]
  nlinarith [mul_nonneg (Nat.cast_nonneg t)
    (sq_nonneg (Real.log t))]

private theorem klucbExploration_mono_over
    {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) :
    klucbExploration s ≤ klucbExploration t := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have htR : (1 : ℝ) ≤ t := hsR.trans (by exact_mod_cast hst)
  have hstR : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hlog :
      Real.log (s : ℝ) ≤ Real.log (t : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (lt_of_lt_of_le zero_lt_one hsR)
      (lt_of_lt_of_le zero_lt_one htR) hstR
  have hlogs : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg hsR
  have hlogt : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg htR
  have hsq :
      Real.log (s : ℝ) ^ 2 ≤ Real.log (t : ℝ) ^ 2 := by
    nlinarith
  have hprod :
      (s : ℝ) * Real.log (s : ℝ) ^ 2 ≤
        (t : ℝ) * Real.log (t : ℝ) ^ 2 :=
    mul_le_mul hstR hsq (sq_nonneg _) (Nat.cast_nonneg _)
  simpa only [klucbExploration, add_comm] using add_le_add_left hprod 1

private theorem log_klucbExploration_mono_over
    {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) :
    Real.log (klucbExploration s) ≤ Real.log (klucbExploration t) :=
  Real.strictMonoOn_log.monotoneOn
    (klucbExploration_pos_over s)
    (klucbExploration_pos_over t)
    (klucbExploration_mono_over hs hst)

private noncomputable def klOvershootTailIndicatorOver
    {k n : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (ε : ℝ) (u : ℕ) (h : BanditHistory k n) : ℝ :=
  if (u : ℝ) * ε ≤ armStoppedCenteredSum ν i u n h then 1 else 0

private theorem measurable_klOvershootTailIndicator_over
    {k n : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (ε : ℝ) (u : ℕ) :
    Measurable (klOvershootTailIndicatorOver ν i ε u :
      BanditHistory k n → ℝ) := by
  unfold klOvershootTailIndicatorOver
  exact Measurable.ite
    (measurableSet_le measurable_const
      (measurable_armStoppedCenteredSum_over ν i u n))
    measurable_const measurable_const

private theorem integrable_klOvershootTailIndicator_over
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (i : Fin k) (ε : ℝ) (u : ℕ) :
    Integrable (klOvershootTailIndicatorOver ν i ε u)
      (banditMeasure ν π n) := by
  apply Integrable.of_bound
    (measurable_klOvershootTailIndicator_over ν i ε u).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun h ↦ by
    unfold klOvershootTailIndicatorOver
    split <;> norm_num

private theorem integral_klOvershootTailIndicator_eq_probability_over
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (i : Fin k) (ε : ℝ) (u : ℕ) :
    (∫ h, klOvershootTailIndicatorOver ν i ε u h
        ∂banditMeasure ν π n) =
      (banditMeasure ν π n).real
        {h : BanditHistory k n |
          (u : ℝ) * ε ≤ armStoppedCenteredSum ν i u n h} := by
  let E : Set (BanditHistory k n) :=
    {h | (u : ℝ) * ε ≤ armStoppedCenteredSum ν i u n h}
  have hE : MeasurableSet E :=
    measurableSet_le measurable_const
      (measurable_armStoppedCenteredSum_over ν i u n)
  have hfun :
      (klOvershootTailIndicatorOver ν i ε u :
        BanditHistory k n → ℝ) =
        E.indicator (fun _ ↦ (1 : ℝ)) := by
    funext h
    unfold klOvershootTailIndicatorOver
    change (if h ∈ E then (1 : ℝ) else 0) =
      E.indicator (fun _ ↦ (1 : ℝ)) h
    by_cases hh : h ∈ E <;> simp [Set.indicator, hh]
  rw [hfun]
  exact integral_indicator_one hE

private theorem integral_klOvershootTailIndicator_le_over
    {k n : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν)
    (π : BanditPolicy k) (i : Fin k) (ε : ℝ) (u : ℕ)
    (hε : 0 < ε) :
    (∫ h, klOvershootTailIndicatorOver ν i ε u h
        ∂banditMeasure ν π n) ≤
      Real.exp (-2 * (u : ℝ) * ε ^ 2) := by
  rw [integral_klOvershootTailIndicator_eq_probability_over]
  exact
    (bandit_adaptive_stopped_centered_sum_tail_half
      (n := n) (π := π) ν hν i u hε.le).1

private theorem feasible_event_implies_small_or_empirical_over
    {k n : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (q p₀ A D : ℝ)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hp₀ : p₀ ∈ Set.Icc (0 : ℝ) 1)
    (hp₀q : p₀ < q)
    (hD : D = bernoulliRelativeEntropy p₀ q)
    (hDpos : 0 < D)
    (h : BanditHistory k n) (hh : HistoryRewardsBernoulliOver h)
    (r : Fin n)
    (hinit :
      ∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0)
    (hfeas :
      klucbTruncatedRelativeEntropy
          (armEmpiricalMean i (banditHistoryPrefixAt h r)) q ≤
        Real.log (klucbExploration (r.val + 1)) /
          armPullCount i (banditHistoryPrefixAt h r))
    (hAmono : Real.log (klucbExploration (r.val + 1)) ≤ A) :
    (armPullCount i (banditHistoryPrefixAt h r) : ℝ) ≤ A / D ∨
      p₀ ≤ armEmpiricalMean i (banditHistoryPrefixAt h r) := by
  let u : ℕ := armPullCount i (banditHistoryPrefixAt h r)
  let p : ℝ := armEmpiricalMean i (banditHistoryPrefixAt h r)
  have hu0 : 0 < (u : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (hinit i)
  by_cases hsmall : (u : ℝ) ≤ A / D
  · exact Or.inl hsmall
  · right
    have hlarge : A / D < (u : ℝ) := lt_of_not_ge hsmall
    have hpIcc : p ∈ Set.Icc (0 : ℝ) 1 :=
      empiricalMean_mem_Icc_over i (banditHistoryPrefixAt h r)
        (historyRewardsBernoulliOver_prefix h hh r)
    by_cases hpq : p ≤ q
    · by_contra hnot
      have hpp₀ : p < p₀ := lt_of_not_ge hnot
      have hmono :
          D ≤ bernoulliRelativeEntropy p q := by
        rw [hD]
        exact bernoulliRelativeEntropy_antitone_fst
          hpIcc hpp₀.le hp₀q.le hq
      have htrunc :
          klucbTruncatedRelativeEntropy p q =
            bernoulliRelativeEntropy p q := by
        rw [klucbTruncatedRelativeEntropy, if_pos hpq]
      have hdle :
          bernoulliRelativeEntropy p q ≤
            Real.log (klucbExploration (r.val + 1)) / (u : ℝ) := by
        simpa [p, u, htrunc] using hfeas
      have hbudget :
          Real.log (klucbExploration (r.val + 1)) / (u : ℝ) ≤
            A / (u : ℝ) :=
        div_le_div_of_nonneg_right hAmono hu0.le
      have huD : (u : ℝ) * D ≤ A := by
        have hDA : D ≤ A / (u : ℝ) :=
          hmono.trans (hdle.trans hbudget)
        have := (le_div_iff₀ hu0).mp hDA
        simpa [mul_comm] using this
      have hAD : A < (u : ℝ) * D := by
        rwa [div_lt_iff₀ hDpos] at hlarge
      linarith
    · exact hp₀q.le.trans (lt_of_not_ge hpq).le

private theorem sum_small_or_tail_le_over
    (n : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (tail : ℕ → ℝ) (htail : ∀ u, 0 ≤ tail u) :
    (∑ u ∈ Finset.Icc 1 n,
        if (u : ℝ) ≤ x then (1 : ℝ) else tail u) ≤
      x + ∑ u ∈ Finset.Icc 1 n, tail u := by
  classical
  let S : Finset ℕ :=
    (Finset.Icc 1 n).filter fun u ↦ (u : ℝ) ≤ x
  have hSsubset : S ⊆ Finset.Icc 1 ⌊x⌋₊ := by
    intro u hu
    have hu' := Finset.mem_filter.mp hu
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hu'.1).1, Nat.le_floor hu'.2⟩
  have hcardNat : S.card ≤ ⌊x⌋₊ := by
    calc
      S.card ≤ (Finset.Icc 1 ⌊x⌋₊).card :=
        Finset.card_le_card hSsubset
      _ = ⌊x⌋₊ := by simp [Nat.card_Icc]
  have hcard : (S.card : ℝ) ≤ x := by
    have hcast : (S.card : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      exact_mod_cast hcardNat
    exact hcast.trans (Nat.floor_le hx)
  calc
    (∑ u ∈ Finset.Icc 1 n,
        if (u : ℝ) ≤ x then (1 : ℝ) else tail u) ≤
      (∑ u ∈ Finset.Icc 1 n,
        if (u : ℝ) ≤ x then (1 : ℝ) else 0) +
        ∑ u ∈ Finset.Icc 1 n, tail u := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro u hu
      by_cases hux : (u : ℝ) ≤ x
      · simp [hux, htail u]
      · simp [hux, htail u]
    _ = (S.card : ℝ) + ∑ u ∈ Finset.Icc 1 n, tail u := by
      rw [Finset.sum_boole]
    _ ≤ x + ∑ u ∈ Finset.Icc 1 n, tail u := by
      gcongr

private theorem feasibilityCount_snd_le_budget_add_tail_over
    {k n : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (a i : Fin k) (ε₁ ε₂ : ℝ)
    (ha : banditArmMean ν a = banditOptimalMean ν)
    (hgap : 0 < banditGap ν i)
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (hεsum : ε₁ + ε₂ < banditGap ν i)
    (h : BanditHistory k n) (hh : HistoryRewardsBernoulliOver h) :
    (klucbFeasibilityFailureCount ν a i ε₂ h).2 ≤
      Real.log (klucbExploration n) /
          bernoulliRelativeEntropy
            (banditArmMean ν i + ε₁)
            (banditOptimalMean ν - ε₂) +
        ∑ u ∈ Finset.Icc 1 n,
          klOvershootTailIndicatorOver ν i ε₁ u h := by
  classical
  let q : ℝ := banditOptimalMean ν - ε₂
  let p₀ : ℝ := banditArmMean ν i + ε₁
  let A : ℝ := Real.log (klucbExploration n)
  let D : ℝ := bernoulliRelativeEntropy p₀ q
  have hmi : banditArmMean ν i ∈ Set.Icc (0 : ℝ) 1 := by
    rw [banditArmMean_bernoulli_over μvec hμ ν hν i]
    exact hμ i
  have hma : banditArmMean ν a ∈ Set.Icc (0 : ℝ) 1 := by
    rw [banditArmMean_bernoulli_over μvec hμ ν hν a]
    exact hμ a
  have hp₀q : p₀ < q := by
    dsimp [p₀, q]
    unfold banditGap at hεsum
    linarith
  have hp₀pos : 0 < p₀ := by
    dsimp [p₀]
    linarith [hmi.1]
  have hq : q ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact lt_of_lt_of_le hp₀pos hp₀q.le
    · dsimp [q]
      rw [← ha]
      linarith [hma.2]
  have hp₀ : p₀ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hp₀pos.le, hp₀q.le.trans hq.2.le⟩
  have hDpos : 0 < D := by
    have hpinsker :=
      bernoulli_relative_entropy_pinsker p₀ q hp₀ hq
    dsimp [D]
    have hne : p₀ - q ≠ 0 := sub_ne_zero.mpr (ne_of_lt hp₀q)
    nlinarith [sq_pos_of_ne_zero hne]
  have hA : 0 ≤ A := by
    dsimp [A]
    apply Real.log_nonneg
    rw [klucbExploration]
    nlinarith [mul_nonneg (Nat.cast_nonneg n)
      (sq_nonneg (Real.log n))]
  let R : Finset (Fin n) :=
    Finset.univ.filter fun r ↦
      (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
        (h r).1 = i ∧
          klucbTruncatedRelativeEntropy
              (armEmpiricalMean i (banditHistoryPrefixAt h r)) q ≤
            Real.log (klucbExploration (r.val + 1)) /
              armPullCount i (banditHistoryPrefixAt h r)
  let f : Fin n → ℕ :=
    fun r ↦ armPullCount i (banditHistoryPrefixAt h r)
  have hR_selected :
      ∀ r ∈ R, (h r).1 = i := by
    intro r hr
    exact (Finset.mem_filter.mp hr).2.2.1
  have himage : R.image f ⊆ Finset.Icc 1 n := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨r, hrR, rfl⟩
    have hr := (Finset.mem_filter.mp hrR).2
    exact Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr (hr.1 i),
        (armPullCount_le_horizon_over i
          (banditHistoryPrefixAt h r)).trans (Nat.le_of_lt r.isLt)⟩
  have hcharge (u : ℕ) (hu : u ∈ R.image f) :
      (if (u : ℝ) ≤ A / D then (1 : ℝ)
        else klOvershootTailIndicatorOver ν i ε₁ u h) = 1 := by
    rcases Finset.mem_image.mp hu with ⟨r, hrR, rfl⟩
    have hr := (Finset.mem_filter.mp hrR).2
    by_cases hsmall :
        (armPullCount i (banditHistoryPrefixAt h r) : ℝ) ≤ A / D
    · rw [if_pos hsmall]
    · rw [if_neg hsmall]
      have hAmono :
          Real.log (klucbExploration (r.val + 1)) ≤ A := by
        dsimp [A]
        exact log_klucbExploration_mono_over
          (by omega) (by omega)
      have hemp :
          p₀ ≤ armEmpiricalMean i (banditHistoryPrefixAt h r) :=
        (feasible_event_implies_small_or_empirical_over
          ν i q p₀ A D hq hp₀ hp₀q rfl hDpos h hh r
          hr.1 hr.2.2 hAmono).resolve_left hsmall
      have hcenter :
          ε₁ ≤ armEmpiricalMean i (banditHistoryPrefixAt h r) -
            banditArmMean ν i := by
        dsimp [p₀] at hemp
        linarith
      have hu_nonneg :
          (0 : ℝ) ≤ armPullCount i (banditHistoryPrefixAt h r) :=
        Nat.cast_nonneg _
      have htail :
          (armPullCount i (banditHistoryPrefixAt h r) : ℝ) * ε₁ ≤
            armStoppedCenteredSum ν i
              (armPullCount i (banditHistoryPrefixAt h r)) n h := by
        rw [armStoppedCenteredSum_stable_after_prefix_over
          ν i h r (armPullCount i (banditHistoryPrefixAt h r)) rfl]
        rw [armStoppedCenteredSum_eq_pullCount_mul_over
          ν i (armPullCount i (banditHistoryPrefixAt h r))
          (banditHistoryPrefixAt h r) le_rfl]
        exact mul_le_mul_of_nonneg_left hcenter hu_nonneg
      unfold klOvershootTailIndicatorOver
      rw [if_pos htail]
  have hcount :
      (klucbFeasibilityFailureCount ν a i ε₂ h).2 =
        (R.card : ℝ) := by
    simp only [klucbFeasibilityFailureCount]
    rw [show R = Finset.univ.filter fun r ↦
      (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
        (h r).1 = i ∧
          klucbTruncatedRelativeEntropy
              (armEmpiricalMean i (banditHistoryPrefixAt h r)) q ≤
            Real.log (klucbExploration (r.val + 1)) /
              armPullCount i (banditHistoryPrefixAt h r) by rfl]
    exact Finset.sum_boole _ _
  rw [hcount]
  have hcardImage :
      (R.image f).card = R.card :=
    Finset.card_image_of_injOn
      (selected_prefix_count_injOn_over i h R hR_selected)
  calc
    (R.card : ℝ) =
        ∑ u ∈ R.image f,
          (if (u : ℝ) ≤ A / D then (1 : ℝ)
            else klOvershootTailIndicatorOver ν i ε₁ u h) := by
      rw [← hcardImage]
      symm
      calc
        (∑ u ∈ R.image f,
            if (u : ℝ) ≤ A / D then (1 : ℝ)
              else klOvershootTailIndicatorOver ν i ε₁ u h) =
            ∑ _u ∈ R.image f, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro u hu
          exact hcharge u hu
        _ = ((R.image f).card : ℝ) := by simp
    _ ≤ ∑ u ∈ Finset.Icc 1 n,
          (if (u : ℝ) ≤ A / D then (1 : ℝ)
            else klOvershootTailIndicatorOver ν i ε₁ u h) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro u huI huNot
      split
      · norm_num
      · unfold klOvershootTailIndicatorOver
        split <;> norm_num
    _ ≤ A / D + ∑ u ∈ Finset.Icc 1 n,
          klOvershootTailIndicatorOver ν i ε₁ u h := by
      apply sum_small_or_tail_le_over n (A / D)
      · exact div_nonneg hA hDpos.le
      · intro u
        unfold klOvershootTailIndicatorOver
        split <;> norm_num
    _ = Real.log (klucbExploration n) /
          bernoulliRelativeEntropy
            (banditArmMean ν i + ε₁)
            (banditOptimalMean ν - ε₂) +
        ∑ u ∈ Finset.Icc 1 n,
          klOvershootTailIndicatorOver ν i ε₁ u h := by
      rfl

private theorem measurableSet_initialized_prefix_over
    {k n : ℕ} (r : Fin n) :
    MeasurableSet {h : BanditHistory k n |
      ∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0} := by
  classical
  convert MeasurableSet.iInter (fun j : Fin k ↦
    (measurableSet_eq_fun
      ((measurable_armPullCount_over j).comp
        (measurable_banditHistoryPrefixAt_over r))
      (measurable_const :
        Measurable (fun _ : BanditHistory k n ↦ (0 : ℝ)))).compl) using 1
  ext h
  simp

private theorem measurable_truncatedEntropy_empirical_over
    {k m : ℕ} (j : Fin k) (q : ℝ) :
    Measurable (fun h : BanditHistory k m ↦
      klucbTruncatedRelativeEntropy (armEmpiricalMean j h) q) := by
  have hemp := measurable_armEmpiricalMean_over (m := m) j
  unfold klucbTruncatedRelativeEntropy bernoulliRelativeEntropy
  apply Measurable.ite (measurableSet_le hemp measurable_const)
  · exact
      (hemp.mul ((hemp.div_const q).log)).add
        ((measurable_const.sub hemp).mul
          (((measurable_const.sub hemp).div_const (1 - q)).log))
  · exact measurable_const

private theorem measurable_feasibilityCount_snd_over
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ) :
    Measurable (fun h : BanditHistory k n ↦
      (klucbFeasibilityFailureCount ν a i ε h).2) := by
  classical
  simp only [klucbFeasibilityFailureCount]
  apply Finset.measurable_sum
  intro r hr
  apply Measurable.ite
  · have hsel : MeasurableSet
        {h : BanditHistory k n | (h r).1 = i} :=
      measurableSet_eq_fun
        (measurable_fst.comp (measurable_pi_apply r))
        (measurable_const :
          Measurable (fun _ : BanditHistory k n ↦ i))
    have hbudget : Measurable
        (fun h : BanditHistory k n ↦
          Real.log (klucbExploration (r.val + 1)) /
            armPullCount i (banditHistoryPrefixAt h r)) :=
      measurable_const.div
        ((measurable_armPullCount_over i).comp
          (measurable_banditHistoryPrefixAt_over r))
    have hd : Measurable
        (fun h : BanditHistory k n ↦
          klucbTruncatedRelativeEntropy
            (armEmpiricalMean i (banditHistoryPrefixAt h r))
            (banditOptimalMean ν - ε)) :=
      (measurable_truncatedEntropy_empirical_over i
        (banditOptimalMean ν - ε)).comp
          (measurable_banditHistoryPrefixAt_over r)
    convert ((measurableSet_initialized_prefix_over r).inter hsel).inter
      (measurableSet_le hd hbudget) using 1
    ext h
    simp [and_assoc]
  · exact measurable_const
  · exact measurable_const

private theorem feasibilityCount_snd_nonneg_over
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) :
    0 ≤ (klucbFeasibilityFailureCount ν a i ε h).2 := by
  classical
  simp only [klucbFeasibilityFailureCount]
  positivity

private theorem feasibilityCount_snd_le_horizon_over
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) :
    (klucbFeasibilityFailureCount ν a i ε h).2 ≤ n := by
  classical
  unfold klucbFeasibilityFailureCount
  calc
    (∑ r : Fin n,
        if (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
            (h r).1 = i ∧
              klucbTruncatedRelativeEntropy
                  (armEmpiricalMean i (banditHistoryPrefixAt h r))
                  (banditOptimalMean ν - ε) ≤
                Real.log (klucbExploration (r.val + 1)) /
                  armPullCount i (banditHistoryPrefixAt h r)
          then (1 : ℝ) else 0) ≤
        ∑ _r : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      split <;> norm_num
    _ = n := by simp

private theorem integrable_feasibilityCount_snd_over
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (a i : Fin k) (ε : ℝ) :
    Integrable (fun h : BanditHistory k n ↦
      (klucbFeasibilityFailureCount ν a i ε h).2)
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact
      (measurable_feasibilityCount_snd_over ν a i ε).aemeasurable
  · exact Filter.Eventually.of_forall fun h ↦
      ⟨feasibilityCount_snd_nonneg_over ν a i ε h,
        feasibilityCount_snd_le_horizon_over ν a i ε h⟩

private theorem exp_neg_two_mul_sum_Icc_le_over
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∑ u ∈ Finset.Icc 1 n,
        Real.exp (-2 * (u : ℝ) * ε ^ 2) ≤
      1 / (2 * ε ^ 2) := by
  let q : ℝ := Real.exp (-(2 * ε ^ 2))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith [sq_pos_of_pos hε]
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext u
    simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_add_one_iff]
  have hsum : ∑ u ∈ Finset.Icc 1 n, q ^ u ≤ q / (1 - q) := by
    rw [le_div_iff₀ hden]
    rw [hIcc, geom_sum_Ico_mul_neg q (by omega : 1 ≤ n + 1)]
    have hpow : 0 ≤ q ^ (n + 1) := pow_nonneg hq0 _
    simp only [pow_one]
    linarith
  have ha : 0 < 2 * ε ^ 2 := by positivity
  have hqa : q / (1 - q) ≤ 1 / (2 * ε ^ 2) := by
    have hqpos : 0 < q := Real.exp_pos _
    have hexp : 1 + 2 * ε ^ 2 ≤ Real.exp (2 * ε ^ 2) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * ε ^ 2)
    have hmain : (2 * ε ^ 2) * q ≤ 1 - q := by
      have := mul_le_mul_of_nonneg_right hexp hqpos.le
      dsimp [q] at this ⊢
      rw [← Real.exp_add] at this
      norm_num at this
      linarith
    rw [div_le_div_iff₀ hden ha]
    nlinarith
  calc
    ∑ u ∈ Finset.Icc 1 n,
        Real.exp (-2 * (u : ℝ) * ε ^ 2) =
        ∑ u ∈ Finset.Icc 1 n, q ^ u := by
      apply Finset.sum_congr rfl
      intro u hu
      dsimp [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ q / (1 - q) := hsum
    _ ≤ 1 / (2 * ε ^ 2) := hqa

end BanditAlgorithm

namespace BanditAlgorithm

private theorem indexCount_eq_feasibilityCount_on_support
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (hq : banditOptimalMean ν - ε ∈ Set.Ioo (0 : ℝ) 1)
    (h : BanditHistory k n) (hh : HistoryRewardsBernoulliOver h) :
    (klucbFailureCount ν a i ε h).2 =
      (klucbFeasibilityFailureCount ν a i ε h).2 := by
  classical
  simp only [klucbFailureCount, klucbFeasibilityFailureCount]
  apply Finset.sum_congr rfl
  intro r hr
  have hthreshold := klucb_index_threshold_feasible i
    (banditHistoryPrefixAt h r) (banditOptimalMean ν - ε) hq
    (empiricalMean_mem_Icc_over i (banditHistoryPrefixAt h r)
      (historyRewardsBernoulliOver_prefix h hh r))
  simp only [hthreshold, and_comm, and_assoc]

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k)
    (hν : ν = bernoulliBandit μvec hμ)
    {π : BanditPolicy k}
    (n : ℕ) (a i : Fin k) (ε₁ ε₂ : ℝ)
    (ha : banditArmMean ν a = banditOptimalMean ν)
    (hgap : 0 < banditGap ν i)
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (hεsum : ε₁ + ε₂ < banditGap ν i) :
    integral (banditMeasure ν π n)
        (fun h ↦ (klucbFailureCount ν a i ε₂ h).2) ≤
      Real.log (klucbExploration n) /
          bernoulliRelativeEntropy
            (banditArmMean ν i + ε₁)
            (banditOptimalMean ν - ε₂) +
        1 / (2 * ε₁ ^ 2) := by
  have hmi := hμ i
  have hma := hμ a
  rw [← banditArmMean_bernoulli_over μvec hμ ν hν i] at hmi
  rw [← banditArmMean_bernoulli_over μvec hμ ν hν a, ha] at hma
  have hq : banditOptimalMean ν - ε₂ ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [banditGap] at hεsum
    constructor <;> linarith [hmi.1, hma.2]
  have hsupport := banditMeasure_ae_historyRewardsBernoulliOver μvec hμ ν hν π n
  have heq : (fun h : BanditHistory k n ↦ (klucbFailureCount ν a i ε₂ h).2)
      =ᵐ[banditMeasure ν π n]
        (fun h ↦ (klucbFeasibilityFailureCount ν a i ε₂ h).2) := by
    filter_upwards [hsupport] with h hh
    exact indexCount_eq_feasibilityCount_on_support ν a i ε₂ hq h hh
  have hleft : Integrable
      (fun h : BanditHistory k n ↦ (klucbFailureCount ν a i ε₂ h).2)
      (banditMeasure ν π n) :=
    (integrable_feasibilityCount_snd_over ν π a i ε₂).congr heq.symm
  let B := Real.log (klucbExploration n) /
    bernoulliRelativeEntropy (banditArmMean ν i + ε₁) (banditOptimalMean ν - ε₂)
  have htail (u : ℕ) :=
    integrable_klOvershootTailIndicator_over (n := n) ν π i ε₁ u
  have hsum : Integrable
      (fun h : BanditHistory k n ↦
        ∑ u ∈ Finset.Icc 1 n, klOvershootTailIndicatorOver ν i ε₁ u h)
      (banditMeasure ν π n) :=
    integrable_finsetSum _ (fun u _ ↦ htail u)
  have hsg : IsSubgaussianBandit (1 / 2) ν := by
    rw [hν]
    exact bernoulliBandit_isSubgaussian_half μvec hμ
  calc
    integral (banditMeasure ν π n)
        (fun h ↦ (klucbFailureCount ν a i ε₂ h).2) ≤
      ∫ h, B + ∑ u ∈ Finset.Icc 1 n, klOvershootTailIndicatorOver ν i ε₁ u h
        ∂banditMeasure ν π n := by
      apply integral_mono_ae hleft ((integrable_const B).add hsum)
      filter_upwards [hsupport, heq] with h hh heq'
      rw [heq']
      exact feasibilityCount_snd_le_budget_add_tail_over
        μvec hμ ν hν a i ε₁ ε₂ ha hgap hε₁ hε₂ hεsum h hh
    _ = B + ∑ u ∈ Finset.Icc 1 n,
        ∫ h, klOvershootTailIndicatorOver ν i ε₁ u h ∂banditMeasure ν π n := by
      rw [integral_add (integrable_const B) hsum,
        integral_finsetSum _ (fun u _ ↦ htail u)]
      simp
    _ ≤ B + ∑ u ∈ Finset.Icc 1 n, Real.exp (-2 * (u : ℝ) * ε₁ ^ 2) := by
      apply add_le_add (le_refl B)
      exact Finset.sum_le_sum fun u _ ↦
        integral_klOvershootTailIndicator_le_over ν hsg π i ε₁ u hε₁
    _ ≤ B + 1 / (2 * ε₁ ^ 2) :=
      add_le_add (le_refl B) (exp_neg_two_mul_sum_Icc_le_over n hε₁)


#print axioms solution
