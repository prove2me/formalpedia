-- Prove2me | solution 2 for CalibeatBandit.Supplement.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T17:32:27.457372+00:00
-- url     : https://prove2.me/submissions/d0316d06-cc2a-43ce-8fba-d7d5b31a7735

import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Tactic
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_CalibeatBandit_rewardLoss
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_Supplement_robustPolicy
import Definitions.Def_CalibeatBandit_pseudoRewardLoss
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Definitions.Def_CalibeatBandit_etaStar
import Definitions.Def_CalibeatBandit_rT
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Mul
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_algState
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CalibeatBandit_HSRof
import Definitions.Def_CalibeatBandit_HRecOf
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Definitions.Def_CalibeatBandit_IsCalibeating
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_CalibeatBandit_Supplement_IsRobust
import Theorems.Thm_CalibeatBandit_theorem_3_2

section

set_option autoImplicit false

open Matrix
open Filter
open scoped BigOperators Topology

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false
set_option maxHeartbeats 150000

open Matrix MeasureTheory
open scoped BigOperators

namespace CalibeatBandit


section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}

theorem measurable_select {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {a : Ω → α} (ha : Measurable a)
    {f : α → Ω → ℝ} (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => f (a ω) ω) := by
  classical
  have heq : (fun ω => f (a ω) ω) =
      fun ω => ∑ i, if a ω = i then f i ω else 0 := by
    funext ω
    simp
  rw [heq]
  exact Finset.measurable_sum _ fun i _ => Measurable.ite (ha (measurableSet_singleton i)) (hf i) measurable_const


end Measurability


namespace ProtocolRun

variable {K T : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {policy : Policy K}


end ProtocolRun

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory

/-- The part of a bandit interaction needed to analyze a single draw per round.
The recommendation may have any label type and is included in the pre-draw
information. -/
structure DrawRun (K T : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) where
  info : ℕ → MeasurableSpace Ω
  preDraw : ℕ → MeasurableSpace Ω
  y : ℕ → Ω → Fin K → ℝ
  I : ℕ → Ω → Fin K
  played : ℕ → Ω → Fin K → ℝ
  info_le : ∀ t ≤ T, info t ≤ mΩ
  info_le_preDraw : ∀ t < T, info t ≤ preDraw t
  preDraw_le_succ : ∀ t < T, preDraw t ≤ info (t + 1)
  y_measurable : ∀ t < T, Measurable[preDraw t] (y t)
  I_measurable : ∀ t < T, Measurable[info (t + 1)] (I t)
  y_mem : ∀ t < T, ∀ ω i, y t ω i ∈ Set.Icc (0 : ℝ) 1
  I_law : ∀ t < T, ∀ i : Fin K,
    condExp (preDraw t) P ((I t ⁻¹' {i}).indicator (fun _ => (1 : ℝ))) =ᵐ[P]
      fun ω => played t ω i

namespace DrawRun

variable {K T : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

def obs (run : DrawRun K T P) (t : ℕ) (ω : Ω) : ℝ :=
  run.y t ω (run.I t ω)

theorem info_le_info (run : DrawRun K T P) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ T) :
    run.info a ≤ run.info b := by
  induction hab with
  | refl => exact le_rfl
  | step _ ih =>
    exact (ih (by omega)).trans ((run.info_le_preDraw _ (by omega)).trans (run.preDraw_le_succ _ (by omega)))

theorem preDraw_le_ambient (run : DrawRun K T P) {t : ℕ} (ht : t < T) :
    run.preDraw t ≤ mΩ :=
  (run.preDraw_le_succ t ht).trans (run.info_le _ (Nat.succ_le_of_lt ht))

theorem obs_measurable (run : DrawRun K T P) {t : ℕ} (ht : t < T) :
    Measurable[run.info (t + 1)] (run.obs t) :=
  @measurable_select Ω (run.info (t + 1)) (Fin K) _ _ _ _ (run.I_measurable t ht)
    (fun j ω => run.y t ω j) fun j => (measurable_pi_apply j).comp
      ((run.y_measurable t ht).mono (run.preDraw_le_succ t ht) le_rfl)

end DrawRun


end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

open MeasureTheory

/-- The recommendation is already available when the learner draws its action. -/
abbrev QProtocolRun.preDraw {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {policy : QPolicy K} (run : QProtocolRun K T P policy)
    (t : ℕ) : MeasurableSpace Ω :=
  run.info t ⊔ MeasurableSpace.comap (run.J t) inferInstance

/-- Use the learner draw in the protocol with explicitly observed mixed recommendations. -/
def QProtocolRun.toDrawRun {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {policy : QPolicy K} (run : QProtocolRun K T P policy) :
    DrawRun K T P where
  info := run.info
  preDraw := run.preDraw
  y := run.y
  I := run.I
  played t ω := policy t (fun s => run.q s ω) (fun s => run.J s ω)
    (fun s => run.I s ω) (fun s => run.y s ω (run.I s ω))
  info_le := run.info_le
  info_le_preDraw := fun _ _ => le_sup_left
  preDraw_le_succ := fun t ht => sup_le (run.info_mono t ht) (run.J_measurable t ht).comap_le
  y_measurable := fun t ht => (run.y_measurable t ht).mono le_sup_left le_rfl
  I_measurable := run.I_measurable
  y_mem := run.y_mem
  I_law := run.I_law

theorem robustHhat_congr_prefix {K T s : ℕ} {ζ : ℝ}
    {q q' : ℕ → Fin K → ℝ} {I I' : ℕ → Fin K} {r r' : ℕ → ℝ}
    (hq : ∀ v < s, q v = q' v) (hI : ∀ v < s, I v = I' v)
    (hr : ∀ v < s, r v = r' v) :
    robustHhat T ζ q I r s = robustHhat T ζ q' I' r' s := by
  unfold robustHhat
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  unfold robustGhat
  apply Finset.sum_congr rfl
  intro v hv
  have hv' := Finset.mem_range.mp hv
  rw [hq v hv', hI v hv', hr v hv']

private theorem robustCrossed_extend_iff {K T t s : ℕ} {ζ : ℝ} (hs : s ≤ t)
    (q : ℕ → Fin K → ℝ) (I : ℕ → Fin K) (r : ℕ → ℝ) (d : Fin K) :
    robustCrossed T ζ (extendFin 0 (fun v : Fin (t + 1) => q v))
      (extendFin d (fun v : Fin t => I v)) (extendFin 0 (fun v : Fin t => r v)) s
      ↔ robustCrossed T ζ q I r s := by
  unfold robustCrossed
  rw [robustHhat_congr_prefix (q' := q) (I' := I) (r' := r)
    (fun v hv => by simp [extendFin, show v < t + 1 by omega])
    (fun v hv => by simp [extendFin, hv.trans_le hs])
    (fun v hv => by simp [extendFin, hv.trans_le hs])]

/-- Until the first crossing, the learner follows the current recommendation with
probability one minus the exploration rate and otherwise samples uniformly. -/
theorem robustPolicy_eq_follow {K T : ℕ} (ζ : ℝ) (t : ℕ)
    (q : ℕ → Fin K → ℝ) (J I : ℕ → Fin K) (r : ℕ → ℝ)
    (h : ∀ u < t, ¬ robustCrossed T ζ q I r (u + 1)) :
    robustPolicy K T ζ t (fun v => q v) (fun v => J v) (fun v => I v) (fun v => r v) =
      fun i => (1 - robustEps T ζ) * (if J t = i then 1 else 0) + robustEps T ζ / K := by
  classical
  unfold robustPolicy
  dsimp only
  rw [dif_neg]
  · rfl
  · rintro ⟨u, hu, hcross⟩
    exact h u hu ((robustCrossed_extend_iff (Nat.succ_le_of_lt hu) q I r (J 0)).mp hcross)

private theorem calibeatPolicy_congr_prefix {K t : ℕ} (η μ : ℝ)
    {J J' I I' : ℕ → Fin K} {r r' : ℕ → ℝ}
    (hJ : ∀ v ≤ t, J v = J' v) (hI : ∀ v < t, I v = I' v)
    (hr : ∀ v < t, r v = r' v) :
    calibeatPolicy K η μ t J I r = calibeatPolicy K η μ t J' I' r' := by
  have hs (v : ℕ) (hv : v ≤ t) : algState η μ J I r v = algState η μ J' I' r' v := by
    induction v with
    | zero => rfl
    | succ v ih =>
      have hlt := Nat.lt_of_succ_le hv
      simp only [algState, ih hlt.le, hJ v hlt.le, hI v hlt, hr v hlt]
  simp only [calibeatPolicy, algP, algX, hs t le_rfl, hJ t le_rfl]

/-- Once a test has crossed the threshold, the policy uses a fresh copy of
calibeating on the history after the crossing round. -/
theorem robustPolicy_eq_restart {K T : ℕ} (ζ : ℝ) {t u : ℕ}
    (q : ℕ → Fin K → ℝ) (J I : ℕ → Fin K) (r : ℕ → ℝ) (hu : u < t)
    (hc : robustCrossed T ζ q I r (u + 1))
    (hfirst : ∀ v < u, ¬ robustCrossed T ζ q I r (v + 1)) :
    robustPolicy K T ζ t (fun v => q v) (fun v => J v) (fun v => I v) (fun v => r v) =
      calibeatPolicy K (etaStar K T) (muStar K T) (t - (u + 1))
        (fun v => J (u + 1 + v)) (fun v => I (u + 1 + v)) (fun v => r (u + 1 + v)) := by
  classical
  let Q := extendFin 0 (fun v : Fin (t + 1) => q v)
  let A := extendFin (J 0) (fun v : Fin t => I v)
  let R := extendFin 0 (fun v : Fin t => r v)
  have he : ∃ v, v < t ∧ robustCrossed T ζ Q A R (v + 1) :=
    ⟨u, hu, (robustCrossed_extend_iff (Nat.succ_le_of_lt hu) q I r (J 0)).mpr hc⟩
  have hfind : Nat.find he = u := by
    apply le_antisymm (Nat.find_min' he ⟨hu,
      (robustCrossed_extend_iff (Nat.succ_le_of_lt hu) q I r (J 0)).mpr hc⟩)
    apply le_of_not_gt
    intro hlt
    have hf := Nat.find_spec he
    exact hfirst _ hlt ((robustCrossed_extend_iff (Nat.succ_le_of_lt hf.1) q I r (J 0)).mp hf.2)
  dsimp only [Q, A, R] at he hfind
  unfold robustPolicy
  dsimp only
  split
  · rename_i hyes
    have hfind' : Nat.find hyes = u := hfind
    rw [hfind']
    apply calibeatPolicy_congr_prefix
    · intro v hv
      simp [extendFin, show u + 1 + v < t + 1 by omega]
    · intro v hv
      simp [extendFin, show u + 1 + v < t by omega]
    · intro v hv
      simp [extendFin, show u + 1 + v < t by omega]
  · rename_i hno
    exact (hno he).elim

/-- During the follow phase, each disagreement with the recommendation
can cost at most two units of swap regret and one unit of reward loss. -/
theorem regret_le_of_disagreements {K T : ℕ} (y : ℕ → Fin K → ℝ)
    (I J : ℕ → Fin K) (hy : ∀ t < T, ∀ i, y t i ∈ Set.Icc (0 : ℝ) 1) :
    let D : ℝ := ∑ t ∈ Finset.range T, if I t = J t then 0 else 1
    swapRegret T y I ≤ swapRegret T y J + 2 * D ∧
      rewardLoss T y J I ≤ swapRegret T y J + D := by
  classical
  intro D
  have hbase (f : Fin K → Fin K) :
      ∑ t ∈ Finset.range T, (y t (f (J t)) - y t (J t)) ≤ swapRegret T y J := by
    unfold swapRegret
    exact Finset.le_sup' (fun σ : Fin K → Fin K =>
      ∑ t ∈ Finset.range T, (y t (σ (J t)) - y t (J t))) (Finset.mem_univ f)
  constructor
  · unfold swapRegret
    apply Finset.sup'_le
    intro f _
    have h := Finset.sum_le_sum (s := Finset.range T) (fun t ht => show
        y t (f (I t)) - y t (I t) ≤ y t (f (J t)) - y t (J t) +
          2 * (if I t = J t then 0 else 1) by
      by_cases he : I t = J t
      · simp [he]
      · have ht' := Finset.mem_range.mp ht
        simp only [he, if_false, mul_one]
        linarith [(hy t ht' (f (I t))).2, (hy t ht' (I t)).1,
          (hy t ht' (f (J t))).1, (hy t ht' (J t)).2])
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    exact h.trans (add_le_add (hbase f) le_rfl)
  · unfold rewardLoss
    apply Finset.sup'_le
    intro f _
    have h := Finset.sum_le_sum (s := Finset.range T) (fun t ht => show
        y t (f (J t)) - y t (I t) ≤ y t (f (J t)) - y t (J t) +
          (if I t = J t then 0 else 1) by
      by_cases he : I t = J t
      · simp [he]
      · have ht' := Finset.mem_range.mp ht
        simp only [he, if_false]
        linarith [(hy t ht' (I t)).1, (hy t ht' (J t)).2])
    rw [Finset.sum_add_distrib] at h
    exact h.trans (add_le_add (hbase f) le_rfl)

/-- On the event where the recommendation and the two estimation errors
satisfy their prefix bounds, the switching test never fires. -/
theorem robust_never_crosses {K T : ℕ} (ζ : ℝ)
    (q y : ℕ → Fin K → ℝ) (J I : ℕ → Fin K) (r : ℕ → ℝ)
    (hRec : ∀ s, 1 ≤ s → s ≤ T → swapRegret s y J ≤ s * robustC K T ζ s)
    (hRealized : ∀ s, 1 ≤ s → s ≤ T →
      pseudoSwapRegret s q y ≤ swapRegret s y J + s * robustC K T ζ s)
    (hEstimate : ∀ u < T, (∀ v < u, ¬ robustCrossed T ζ q I r (v + 1)) →
      robustHhat T ζ q I r (u + 1) ≤
        pseudoSwapRegret (u + 1) q y + (u + 1 : ℕ) * robustC K T ζ (u + 1)) :
    ∀ u < T, ¬ robustCrossed T ζ q I r (u + 1) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hc
    have hfirst : ∀ v < u, ¬ robustCrossed T ζ q I r (v + 1) :=
      fun v hv => ih v hv (hv.trans hu)
    have h₁ := hEstimate u hu hfirst
    have h₂ := hRealized (u + 1) (by omega) (by omega)
    have h₃ := hRec (u + 1) (by omega) (by omega)
    unfold robustCrossed at hc
    push_cast at h₁ h₂ h₃ hc
    linarith

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

open Filter MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

/-- Conditional expectation of a bounded function evaluated at the played action. -/
theorem DrawRun.condExp_select_played {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (run : DrawRun K T P) {t : ℕ} (ht : t < T)
    (g : Fin K → Ω → ℝ) (hg : ∀ j, Measurable[run.preDraw t] (g j))
    (B : ℝ) (hb : ∀ j ω, |g j ω| ≤ B) :
    Integrable (fun ω => g (run.I t ω) ω) P ∧
    condExp (run.preDraw t) P (fun ω => g (run.I t ω) ω) =ᵐ[P]
      fun ω => ∑ j, run.played t ω j * g j ω := by
  classical
  let ind (j : Fin K) : Ω → ℝ := (run.I t ⁻¹' {j}).indicator (fun _ => 1)
  have hm := run.preDraw_le_ambient ht
  have im (j : Fin K) : Measurable (ind j) :=
    measurable_const.indicator ((run.I_measurable t ht).mono
      (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl (measurableSet_singleton j))
  have ib (j : Fin K) (ω : Ω) : ind j ω ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases h : run.I t ω = j <;> simp [ind, h]
  have ii (j : Fin K) : Integrable (ind j) P :=
    (integrable_const (1 : ℝ)).mono' (im j).aestronglyMeasurable (ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (ib j ω).1] using (ib j ω).2)
  have gi (j : Fin K) : Integrable (g j * ind j) P :=
    (integrable_const B).mono' (((hg j).mono hm le_rfl).mul (im j)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        change ‖g j ω * ind j ω‖ ≤ B
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ib j ω).1]
        exact (mul_le_of_le_one_right (abs_nonneg _) (ib j ω).2).trans (hb j ω))
  have heq : (fun ω => g (run.I t ω) ω) = ∑ j, g j * ind j := by
    ext ω
    simp only [Finset.sum_apply, Pi.mul_apply, ind, Set.indicator_apply,
      Set.mem_preimage, Set.mem_singleton_iff, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  rw [heq]
  refine ⟨integrable_finsetSum' _ (fun j _ => gi j), (condExp_finsetSum (fun j _ => gi j) _).trans ?_⟩
  have hcoord (j : Fin K) :
      condExp (run.preDraw t) P (g j * ind j) =ᵐ[P] fun ω => g j ω * run.played t ω j := by
    refine (condExp_mul_of_stronglyMeasurable_left (hg j).stronglyMeasurable (gi j) (ii j)).trans ?_
    filter_upwards [run.I_law t ht j] with ω hω
    change condExp (run.preDraw t) P (ind j) ω = run.played t ω j at hω
    change g j ω * condExp (run.preDraw t) P (ind j) ω = _
    rw [hω]
  filter_upwards [ae_all_iff.mpr hcoord] with ω hω
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => (hω j).trans (mul_comm _ _)


end CalibeatBandit

end

section

set_option autoImplicit false

open MeasureTheory Filter

namespace CalibeatBandit.Supplement.QProtocolRun

variable {K T : ℕ} {ζ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} (run : QProtocolRun K T P (robustPolicy K T ζ))

/-- The rounds strictly before `t` have all passed the switching test. -/
def robustFollowing (t : ℕ) : Set Ω :=
  {ω | ∀ u < t, ¬ robustCrossed T ζ (fun s => run.q s ω)
    (fun s => run.I s ω) (fun s => run.y s ω (run.I s ω)) (u + 1)}

theorem measurable_robustHhat {s t : ℕ} (hst : s ≤ t) (ht : t ≤ T) :
    Measurable[run.info t] (fun ω => robustHhat T ζ (fun u => run.q u ω)
      (fun u => run.I u ω) (fun u => run.y u ω (run.I u ω)) s) := by
  let q := run.q
  let I := run.I
  let r := run.toDrawRun.obs
  have past {u : ℕ} (hu : u < s) : run.info (u + 1) ≤ run.info t :=
    run.toDrawRun.info_le_info ((Nat.succ_le_of_lt hu).trans hst) ht
  have mq (u : ℕ) (hu : u < s) : Measurable[run.info t] (q u) :=
    (run.q_measurable u (hu.trans_le (hst.trans ht))).mono
      ((run.info_mono u (hu.trans_le (hst.trans ht))).trans (past hu)) le_rfl
  have mI (u : ℕ) (hu : u < s) : Measurable[run.info t] (I u) :=
    (run.I_measurable u (hu.trans_le (hst.trans ht))).mono (past hu) le_rfl
  have mr (u : ℕ) (hu : u < s) : Measurable[run.info t] (r u) :=
    (run.toDrawRun.obs_measurable (hu.trans_le (hst.trans ht))).mono (past hu) le_rfl
  change Measurable[run.info t] (fun ω => robustHhat T ζ (fun u => q u ω)
      (fun u => I u ω) (fun u => r u ω) s)
  classical
  let : MeasurableSpace Ω := run.info t
  unfold robustHhat robustGhat
  refine Finset.measurable_sum _ (fun i _ => Measurable.iSup fun j => ?_)
  refine Finset.measurable_sum _ fun u hu => ?_
  have hu' := Finset.mem_range.mp hu
  have hq (k : Fin K) : Measurable (fun ω => q u ω k) := (measurable_pi_apply k).comp (mq u hu')
  have hy (k : Fin K) :
      Measurable (fun ω => robustYhat (followMix (robustEps T ζ) (q u ω)) (I u ω) (r u ω) k) := by
    unfold robustYhat followMix
    exact Measurable.ite ((mI u hu') (measurableSet_singleton k))
      ((mr u hu').div (((hq k).const_mul _).add measurable_const)) measurable_const
  exact (hq i).mul ((hy j).sub (hy i))

theorem measurableSet_robustFollowing {t : ℕ} (ht : t ≤ T) :
    MeasurableSet[run.info t] (run.robustFollowing t) := by
  change MeasurableSet[run.info t]
    {ω | ∀ u < t, ¬ robustCrossed T ζ (fun s => run.q s ω)
      (fun s => run.I s ω) (fun s => run.y s ω (run.I s ω)) (u + 1)}
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun u => MeasurableSet.iInter fun hu => ?_
  unfold robustCrossed
  exact (measurableSet_lt measurable_const (run.measurable_robustHhat (Nat.succ_le_of_lt hu) ht)).compl

variable [IsProbabilityMeasure P]

theorem condExp_robustFollowing_action {t : ℕ} (ht : t < T) (j : Fin K) :
    condExp (run.info t) P ((run.robustFollowing t ∩ (run.I t ⁻¹' {j})).indicator
      (fun _ => (1 : ℝ))) =ᵐ[P]
      (run.robustFollowing t).indicator (fun ω => followMix (robustEps T ζ) (run.q t ω) j) := by
  classical
  let F := run.robustFollowing t
  let yI : Ω → ℝ := (run.I t ⁻¹' {j}).indicator (fun _ => 1)
  let yJ : Ω → ℝ := (run.J t ⁻¹' {j}).indicator (fun _ => 1)
  let a : ℝ := 1 - robustEps T ζ
  let b : ℝ := robustEps T ζ / K
  let g : Ω → ℝ := F.indicator (a • yJ + fun _ => b)
  have hF := run.measurableSet_robustFollowing ht.le
  have hFpre : MeasurableSet[run.preDraw t] F := (show run.info t ≤ run.preDraw t from le_sup_left) F hF
  have hIint : Integrable yI P := (integrable_const _).indicator
    ((run.I_measurable t ht).mono (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl (measurableSet_singleton j))
  have hJint : Integrable yJ P := (integrable_const _).indicator
    ((run.J_measurable t ht).mono (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl (measurableSet_singleton j))
  have hm : run.preDraw t ≤ mΩ := run.toDrawRun.preDraw_le_ambient ht
  let : IsFiniteMeasure (P.trim hm) := isFiniteMeasure_trim hm
  have hg : condExp (run.preDraw t) P (F.indicator yI) =ᵐ[P] g := by
    refine (condExp_indicator hIint hFpre).trans ?_
    filter_upwards [run.I_law t ht j] with ω hw
    by_cases hω : ω ∈ F
    · have h := congrFun (robustPolicy_eq_follow ζ t (fun s => run.q s ω)
        (fun s => run.J s ω) (fun s => run.I s ω)
        (fun s => run.y s ω (run.I s ω)) hω) j
      simp only [g, Set.indicator_of_mem hω, Pi.add_apply, Pi.smul_apply, smul_eq_mul, a, b]
      change condExp (run.preDraw t) P yI ω = _
      rw [hw, h]
      simp [yJ, Set.indicator_apply]
    · simp [g, Set.indicator_of_notMem hω]
  rw [← Set.indicator_indicator]
  refine (condExp_condExp_of_le (μ := P) (f := F.indicator yI) le_sup_left hm).symm.trans
    ((condExp_congr_ae (m := run.info t) hg).trans ?_)
  refine (condExp_indicator ((hJint.smul a).add (integrable_const b)) hF).trans ?_
  filter_upwards [condExp_add (hJint.smul a) (integrable_const b) (run.info t),
    condExp_smul (μ := P) a yJ (run.info t), run.J_law t ht j] with ω hsum hmul hJ
  by_cases hω : ω ∈ run.robustFollowing t
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
    simp only [Pi.add_apply] at hsum
    rw [hsum, hmul, condExp_const (run.info_le _ ht.le), Pi.smul_apply, smul_eq_mul, hJ] <;> rfl
  · simp only [Set.indicator_of_notMem hω]

end CalibeatBandit.Supplement.QProtocolRun

end

section

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

theorem integrable_of_abs_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hm : Measurable f) {B : ℝ}
    (hb : ∀ ω, |f ω| ≤ B) : Integrable f P :=
  (integrable_const B).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hb ω)

theorem integral_exp_sum_le_one {T : ℕ} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (info preDraw : ℕ → MeasurableSpace Ω)
    (hinfo : ∀ a b, a ≤ b → b ≤ T → info a ≤ info b)
    (hinfo_le : ∀ n ≤ T, info n ≤ mΩ)
    (hpre : ∀ n < T, preDraw n ≤ mΩ)
    (hprev : ∀ n < T, info n ≤ preDraw n)
    (d : ℕ → Ω → ℝ) {B : ℝ}
    (hm : ∀ t < T, Measurable[info (t + 1)] (d t))
    (hb : ∀ t < T, ∀ ω, |d t ω| ≤ B)
    (hc : ∀ t < T, condExp (preDraw t) P (fun ω => Real.exp (d t ω)) ≤ᵐ[P] fun _ => 1) :
    ∫ ω, Real.exp (∑ t ∈ Finset.range T, d t ω) ∂P ≤ 1 := by
  let F (n : ℕ) (ω : Ω) := Real.exp (∑ t ∈ Finset.range n, d t ω)
  have hF (n : ℕ) (hn : n ≤ T) : Measurable[info n] (F n) := by
    refine Real.continuous_exp.measurable.comp (Finset.measurable_sum _ fun t ht => ?_)
    have hs := Nat.succ_le_of_lt (Finset.mem_range.mp ht)
    exact (hm t (lt_of_lt_of_le (Finset.mem_range.mp ht) hn)).mono
      (hinfo _ _ hs hn) le_rfl
  have hi (n : ℕ) (hn : n ≤ T) : Integrable (F n) P := by
    apply integrable_of_abs_bound ((hF n hn).mono (hinfo_le n hn) le_rfl)
    intro ω
    rw [show F n ω = Real.exp (∑ t ∈ Finset.range n, d t ω) from rfl,
      abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ∑ _ ∈ Finset.range n, B := Finset.sum_le_sum fun t ht =>
        (le_abs_self _).trans (hb t ((Finset.mem_range.mp ht).trans_le hn) ω)
      _ = (n : ℝ) * B := by simp
  have step (n : ℕ) (hn : n < T) : (∫ ω, F (n + 1) ω ∂P) ≤ ∫ ω, F n ω ∂P := by
    let G : Ω → ℝ := fun ω => Real.exp (d n ω)
    have hG : Integrable G P := by
      refine integrable_of_abs_bound (B := Real.exp B) (Real.continuous_exp.measurable.comp
        ((hm n hn).mono (hinfo_le _ (Nat.succ_le_of_lt hn)) le_rfl)) ?_
      intro ω
      change |Real.exp (d n ω)| ≤ Real.exp B
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hb n hn ω))
    have heq : F (n + 1) = F n * G := by
      funext ω
      simp [F, G, Finset.sum_range_succ, Real.exp_add]
    have hprod : Integrable (F n * G) P := heq ▸ hi (n + 1) (Nat.succ_le_of_lt hn)
    have hpull := condExp_mul_of_stronglyMeasurable_left
      ((hF n hn.le).mono (hprev n hn) le_rfl).stronglyMeasurable
      hprod hG
    rw [heq, ← integral_condExp (m := preDraw n) (hpre n hn)]
    apply integral_mono_ae integrable_condExp (hi n hn.le)
    filter_upwards [hpull, hc n hn] with ω hw hcω
    rw [hw]
    exact mul_le_of_le_one_right (Real.exp_nonneg _) hcω
  have hbound (n : ℕ) (hn : n ≤ T) : (∫ ω, F n ω ∂P) ≤ 1 := by
    induction n with
    | zero => simp [F]
    | succ n ih =>
      have hh : n < T := Nat.lt_of_succ_le hn
      exact (step n hh).trans (ih hh.le)
  exact hbound T le_rfl


theorem integrable_finset_max {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsFiniteMeasure P] (hne : (Finset.univ : Finset ι).Nonempty)
    (F : ι → Ω → ℝ) {B : ℝ} (hm : ∀ i, Measurable (F i)) (hb : ∀ i ω, |F i ω| ≤ B) :
    Integrable (fun ω => Finset.univ.sup' hne (fun i => F i ω)) P := by
  let _ : Nonempty ι := hne.to_subtype.map Subtype.val
  apply integrable_of_abs_bound
  · simp_rw [Finset.sup'_univ_eq_ciSup]
    exact Measurable.iSup hm
  · intro ω
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (fun i => F i ω)
    exact hi.symm ▸ hb i ω


end CalibeatBandit

end

section

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal

namespace CalibeatBandit.Supplement

theorem robustEps_pos_of_pos {T : ℕ} (hT : 0 < T) (ζ : ℝ) :
    0 < robustEps T ζ :=
  Real.rpow_pos_of_pos (by exact_mod_cast hT) _


namespace QProtocolRun

variable {K T : ℕ} {ζ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  (run : QProtocolRun K T P (robustPolicy K T ζ))

/-- Count disagreements on rounds played in follow mode. -/
noncomputable def followDisagreements (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range T, (run.robustFollowing t).indicator
    (fun ω => if run.I t ω = run.J t ω then (0 : ℝ) else 1) ω

omit [IsProbabilityMeasure P] in
theorem followDisagreements_nonneg (ω : Ω) : 0 ≤ run.followDisagreements ω := by
  unfold followDisagreements
  exact Finset.sum_nonneg fun t _ => Set.indicator_nonneg (fun _ _ => by split <;> norm_num) _

set_option maxHeartbeats 1000000 in
theorem integrable_followDisagreements_and_le (hK : 0 < K) (hT : 0 < T) (_hζ : 0 ≤ ζ) :
    Integrable run.followDisagreements P ∧
      ∫ ω, run.followDisagreements ω ∂P ≤ robustEps T ζ * T := by
  classical
  let ε := robustEps T ζ
  have hε := robustEps_pos_of_pos hT ζ
  have hK' : 0 < (K : ℝ) := by exact_mod_cast hK
  let F (t : ℕ) := run.robustFollowing t
  let D (t : ℕ) (ω : Ω) := (F t).indicator
    (fun ω => if run.I t ω = run.J t ω then (0 : ℝ) else 1) ω
  have hdt (t : ℕ) (ht : t < T) : Integrable (D t) P ∧
      ∫ ω, D t ω ∂P ≤ ε := by
    let g (j : Fin K) : Ω → ℝ := (F t).indicator (fun ω => if j = run.J t ω then 0 else 1)
    have gmeas (j : Fin K) : Measurable[run.toDrawRun.preDraw t] (g j) := by
      have hJ : Measurable[run.preDraw t] (run.J t) :=
        Measurable.of_comap_le le_sup_right
      have hj := (hJ (measurableSet_singleton j))
      have hset : MeasurableSet[run.preDraw t] {ω | j = run.J t ω} := by
        simpa only [Set.preimage, Set.mem_singleton_iff, eq_comm] using hj
      have hF : MeasurableSet[run.preDraw t] (F t) :=
        (show run.info t ≤ run.preDraw t from le_sup_left) _ (run.measurableSet_robustFollowing ht.le)
      exact (Measurable.ite hset measurable_const measurable_const).indicator hF
    have gb (j : Fin K) (ω : Ω) : |g j ω| ≤ 1 := by
      by_cases hf : ω ∈ F t
      · simp only [g, Set.indicator_of_mem hf]; split <;> norm_num
      · simp [g, Set.indicator_of_notMem hf]
    have hc := run.toDrawRun.condExp_select_played P ht g gmeas 1 gb
    change Integrable (D t) P ∧ _ at hc
    refine ⟨hc.1, ?_⟩
    have he : ∫ ω, D t ω ∂P = ∫ ω, ∑ j, run.toDrawRun.played t ω j * g j ω ∂P := by
      rw [← integral_congr_ae hc.2, integral_condExp (run.toDrawRun.preDraw_le_ambient ht)]
      rfl
    rw [he]
    have hs : Integrable (fun ω => ∑ j, run.toDrawRun.played t ω j * g j ω) P :=
      integrable_condExp.congr hc.2
    calc
      _ ≤ ∫ _ : Ω, ε ∂P := integral_mono hs (integrable_const _) fun ω => by
        by_cases hf : ω ∈ F t
        · have h := robustPolicy_eq_follow ζ t (fun s => run.q s ω) (fun s => run.J s ω)
            (fun s => run.I s ω) (fun s => run.y s ω (run.I s ω)) hf
          have hj (j : Fin K) : run.toDrawRun.played t ω j * g j ω ≤ ε / K := by
            have hval : run.toDrawRun.played t ω j =
                (1 - ε) * (if run.J t ω = j then 1 else 0) + ε / K := congrFun h j
            rw [hval]
            simp only [g, Set.indicator_of_mem hf]
            by_cases hEq : j = run.J t ω
            · simp only [hEq, if_true, mul_zero]
              exact div_nonneg hε.le hK'.le
            · simp only [hEq, Ne.symm hEq, if_false, mul_zero, zero_add, mul_one, le_refl]
          calc
            _ ≤ ∑ _j : Fin K, ε / K := Finset.sum_le_sum fun j _ => hj j
            _ = ε := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              field_simp [hK'.ne']
        · simp only [g, Set.indicator_of_notMem hf, mul_zero, Finset.sum_const_zero]
          exact hε.le
      _ = _ := by simp
  have hd : run.followDisagreements = ∑ t ∈ Finset.range T, D t := by
    ext ω
    simp [followDisagreements, D, F]
  rw [hd]
  refine ⟨integrable_finsetSum' _ fun t ht => (hdt t (Finset.mem_range.mp ht)).1, ?_⟩
  simp only [Finset.sum_apply]
  rw [integral_finsetSum _ fun t ht => (hdt t (Finset.mem_range.mp ht)).1]
  calc
    _ ≤ ∑ _t ∈ Finset.range T, ε := Finset.sum_le_sum fun t ht => (hdt t (Finset.mem_range.mp ht)).2
    _ = _ := by simp [ε, mul_comm]

end QProtocolRun

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal

namespace CalibeatBandit.Supplement

theorem rewardLoss_le_rounds {K s : ℕ} (y : ℕ → Fin K → ℝ) (J I : ℕ → Fin K)
    (hy : ∀ t < s, ∀ i, y t i ∈ Icc (0 : ℝ) 1) :
    rewardLoss s y J I ≤ (s : ℝ) := by
  unfold rewardLoss
  apply Finset.sup'_le
  intro f _
  calc
    _ ≤ ∑ _t ∈ Finset.range s, (1 : ℝ) := Finset.sum_le_sum fun t ht =>
      sub_le_iff_le_add.mpr (((hy t (Finset.mem_range.mp ht) (f (J t))).2).trans
        (le_add_of_nonneg_right ((hy t (Finset.mem_range.mp ht) (I t))).1))
    _ = _ := by simp

theorem rewardLoss_abs_le_rounds {K s : ℕ} (y : ℕ → Fin K → ℝ) (J I : ℕ → Fin K)
    (hy : ∀ t < s, ∀ i, y t i ∈ Icc (0 : ℝ) 1) :
    |rewardLoss s y J I| ≤ (s : ℝ) := by
  apply abs_le.mpr
  refine ⟨?_, rewardLoss_le_rounds y J I hy⟩
  unfold rewardLoss
  calc
    _ = ∑ _t ∈ Finset.range s, (-1 : ℝ) := by simp
    _ ≤ ∑ t ∈ Finset.range s, (y t (J t) - y t (I t)) := by
      apply Finset.sum_le_sum
      intro t ht
      have ht' := Finset.mem_range.mp ht
      linarith [(hy t ht' (J t)).1, (hy t ht' (I t)).2]
    _ ≤ _ := Finset.le_sup' (fun f : Fin K → Fin K =>
      ∑ t ∈ Finset.range s, (y t (f (J t)) - y t (I t))) (Finset.mem_univ id)

theorem swapRegret_nonneg_of_id {K s : ℕ} (y : ℕ → Fin K → ℝ) (I : ℕ → Fin K) :
    0 ≤ swapRegret s y I := by
  unfold swapRegret
  simpa using (Finset.le_sup' (fun f : Fin K → Fin K =>
      ∑ t ∈ Finset.range s, (y t (f (I t)) - y t (I t))) (Finset.mem_univ id))

private theorem measurable_rewardLoss_prefix {K s : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (y : ℕ → Ω → Fin K → ℝ) (J I : ℕ → Ω → Fin K)
    (hy : ∀ t < s, Measurable (y t)) (hJ : ∀ t < s, Measurable (J t))
    (hI : ∀ t < s, Measurable (I t)) :
    Measurable (fun ω => rewardLoss s (fun t => y t ω) (fun t => J t ω) (fun t => I t ω)) := by
  classical
  let _ : Nonempty (Fin K → Fin K) := ⟨id⟩
  change Measurable (fun ω => Finset.univ.sup' ⟨id, Finset.mem_univ _⟩
    (fun f : Fin K → Fin K => ∑ t ∈ Finset.range s, (y t ω (f (J t ω)) - y t ω (I t ω))))
  simp_rw [Finset.sup'_univ_eq_ciSup]
  refine Measurable.iSup fun f => Finset.measurable_sum _ fun t ht => ?_
  have ht' := Finset.mem_range.mp ht
  exact (measurable_select (hJ t ht') (fun i => (measurable_pi_apply (f i)).comp (hy t ht'))).sub
    (measurable_select (hI t ht') (fun i => (measurable_pi_apply i).comp (hy t ht')))

namespace QProtocolRun

variable {K T : ℕ} {ζ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  (run : QProtocolRun K T P (robustPolicy K T ζ))

theorem measurable_qRunRewardLoss {s : ℕ} (hs : s ≤ T) (bJ bI : Bool) :
    Measurable (fun ω => rewardLoss s (fun t => run.y t ω)
      (fun t => if bJ then run.J t ω else run.I t ω)
      (fun t => if bI then run.J t ω else run.I t ω)) := by
  apply measurable_rewardLoss_prefix
  · intro t ht
    have ht' := ht.trans_le hs
    exact (run.y_measurable t ht').mono (run.info_le t ht'.le) le_rfl
  all_goals
    intro t ht
    have ht' := ht.trans_le hs
    have jm := (run.J_measurable t ht').mono (run.info_le _ (Nat.succ_le_of_lt ht')) le_rfl
    have im := (run.I_measurable t ht').mono (run.info_le _ (Nat.succ_le_of_lt ht')) le_rfl
    split <;> assumption

def recommendationCapEvent : Set Ω :=
  {ω | ∀ s : ℕ, 1 ≤ s → s ≤ T →
    swapRegret s (fun t => run.y t ω) (fun t => run.J t ω) ≤ s * robustC K T ζ s}

theorem measurableSet_recommendationCapEvent :
    MeasurableSet run.recommendationCapEvent := by
  unfold recommendationCapEvent
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun hs => ?_
  exact measurableSet_le (run.measurable_qRunRewardLoss hs true true) measurable_const

set_option maxHeartbeats 1200000 in
/-- The consistency argument only needs a measurable event with the probability
from the prefix concentration bounds and on which the learner keeps following. -/
theorem robust_consistency_of_event (hK : 0 < K) (hT : 0 < T) (hζ : 0 ≤ ζ)
    (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (E : Set Ω) (hE : MeasurableSet E) (hbad : P Eᶜ ≤ ENNReal.ofReal ((T : ℝ) ^ (-2 : ℝ)))
    (hfollow : E ∩ run.recommendationCapEvent ⊆ run.robustFollowing T)
    (hcap : ENNReal.ofReal (1 - ρ) ≤ P run.recommendationCapEvent) :
    ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P
        ≤ ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.J t ω) ∂P +
          (ρ + (2 * robustEps T ζ + (T : ℝ) ^ (-2 : ℝ))) * T ∧
    ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P
        ≤ ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.J t ω) ∂P +
          (ρ + (2 * robustEps T ζ + (T : ℝ) ^ (-2 : ℝ))) * T := by
  classical
  let F := run.recommendationCapEvent
  let B := (E ∩ F)ᶜ
  let Y (ω : Ω) := swapRegret T (fun t => run.y t ω) (fun t => run.J t ω)
  let D := run.followDisagreements
  let H (ω : Ω) : ℝ := B.indicator (fun _ => (T : ℝ)) ω
  have hF := run.measurableSet_recommendationCapEvent
  have hB : MeasurableSet B := (hE.inter hF).compl
  have hρ : P Fᶜ ≤ ENNReal.ofReal ρ := by
    rw [prob_compl_eq_one_sub₀ hF.nullMeasurableSet]
    refine (tsub_le_tsub_left hcap (1 : ℝ≥0∞)).trans_eq ?_
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (1 : ℝ) (sub_nonneg.mpr hρ₁)]
    congr 1
    ring
  have hpos : 0 ≤ (T : ℝ) ^ (-2 : ℝ) := by positivity
  have hBM : P B ≤ ENNReal.ofReal (ρ + (T : ℝ) ^ (-2 : ℝ)) := by
    unfold B
    rw [compl_inter, ENNReal.ofReal_add hρ₀ hpos, add_comm]
    exact (measure_union_le _ _).trans (add_le_add hbad hρ)
  have hdε := run.integrable_followDisagreements_and_le hK hT hζ
  have hd : Integrable D P := hdε.1
  have heD : ∫ ω, D ω ∂P ≤ robustEps T ζ * T := hdε.2
  have hH : Integrable H P := (integrable_const _).indicator hB
  have hEH : ∫ ω, H ω ∂P ≤ (ρ + (T : ℝ) ^ (-2 : ℝ)) * T := by
    change ∫ ω, B.indicator (fun _ => (T : ℝ)) ω ∂P ≤ _
    rw [integral_indicator_const _ hB, smul_eq_mul]
    apply mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg T)
    change (P B).toReal ≤ _
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hBM).trans_eq
      (ENNReal.toReal_ofReal (add_nonneg hρ₀ hpos))
  have hYm : Measurable Y := run.measurable_qRunRewardLoss le_rfl true true
  have hYi : Integrable Y P := integrable_of_abs_bound hYm (fun ω =>
    rewardLoss_abs_le_rounds _ _ _ (fun t ht i => run.y_mem t ht ω i))
  have hYnonneg (ω : Ω) : 0 ≤ Y ω := swapRegret_nonneg_of_id _ _
  have hAt (ω : Ω) (hω : ω ∈ E ∩ F) :
      swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ≤ Y ω + 2 * D ω ∧
      rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω)
        ≤ Y ω + D ω := by
    have hw (t : ℕ) (ht : t < T) : ω ∈ run.robustFollowing t :=
      fun u hu => hfollow hω u (hu.trans ht)
    have hD : D ω = ∑ t ∈ Finset.range T, if run.I t ω = run.J t ω then (0 : ℝ) else 1 := by
      unfold D followDisagreements
      exact Finset.sum_congr rfl fun t ht => Set.indicator_of_mem (hw t (Finset.mem_range.mp ht)) _
    rw [hD]
    exact regret_le_of_disagreements _ _ _ (fun t ht i => run.y_mem t ht ω i)
  have estimate (X : Ω → ℝ) (hX : Integrable X P) (hb : ∀ ω, X ω ≤ (T : ℝ))
      (hgood : ∀ ω ∈ E ∩ F, X ω ≤ Y ω + 2 * D ω) :
      ∫ ω, X ω ∂P ≤ ∫ ω, Y ω ∂P +
        (ρ + (2 * robustEps T ζ + (T : ℝ) ^ (-2 : ℝ))) * T := by
    have hD2 : Integrable (fun ω => 2 * D ω) P := hd.const_mul (2 : ℝ)
    have hsum : Integrable (fun ω => Y ω + 2 * D ω) P := hYi.add hD2
    have h : (∫ ω, X ω ∂P) ≤ ∫ ω, (Y ω + 2 * D ω) + H ω ∂P :=
      integral_mono hX (hsum.add hH) (fun ω => by
        by_cases hω : ω ∈ E ∩ F
        · have hz : H ω = 0 := Set.indicator_of_notMem (not_not_intro hω) _
          change X ω ≤ Y ω + 2 * D ω + H ω
          rw [hz, add_zero]
          exact hgood ω hω
        · have ht : H ω = (T : ℝ) := Set.indicator_of_mem hω _
          change X ω ≤ Y ω + 2 * D ω + H ω
          rw [ht]
          linarith [hb ω, hYnonneg ω, run.followDisagreements_nonneg ω])
    rw [integral_add hsum hH, integral_add hYi hD2, integral_const_mul] at h
    refine h.trans ?_
    nlinarith only [heD, hEH]
  constructor
  · refine estimate _ ?_ (fun ω => rewardLoss_le_rounds _ _ _
      (fun t ht i => run.y_mem t ht ω i)) (fun ω hω => (hAt ω hω).1)
    exact integrable_of_abs_bound (run.measurable_qRunRewardLoss le_rfl false false)
      (fun ω => rewardLoss_abs_le_rounds _ _ _ (fun t ht i => run.y_mem t ht ω i))
  · refine estimate _ ?_ (fun ω => rewardLoss_le_rounds _ _ _
      (fun t ht i => run.y_mem t ht ω i)) ?_
    · exact integrable_of_abs_bound (run.measurable_qRunRewardLoss le_rfl true false)
        (fun ω => rewardLoss_abs_le_rounds _ _ _ (fun t ht i => run.y_mem t ht ω i))
    · intro ω hω
      linarith [(hAt ω hω).2, run.followDisagreements_nonneg ω]

set_option maxHeartbeats 1200000 in
/-- If the allowed excess regret is at least one per round, the consistency
guarantee holds directly from the reward range. -/
theorem robust_consistency_of_gamma_ge_one (ρ γ : ℝ) (hρ : 0 ≤ ρ) (hγ : 1 ≤ γ) :
    ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P
        ≤ ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.J t ω) ∂P + (ρ + γ) * T ∧
    ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P
        ≤ ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.J t ω) ∂P + (ρ + γ) * T := by
  have hbase : 0 ≤ ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.J t ω) ∂P :=
    integral_nonneg (fun ω => swapRegret_nonneg_of_id _ _)
  have hgap : (T : ℝ) ≤ (ρ + γ) * T :=
    le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith)
  have req (b : Bool) :
      ∫ ω, rewardLoss T (fun t => run.y t ω)
          (fun t => if b then run.J t ω else run.I t ω) (fun t => run.I t ω) ∂P ≤ (T : ℝ) := by
    have hm := run.measurable_qRunRewardLoss le_rfl b false
    have hi := integrable_of_abs_bound (P := P) hm (B := (T : ℝ)) (fun ω =>
      rewardLoss_abs_le_rounds _ _ _ (fun t ht i => run.y_mem t ht ω i))
    have h := integral_mono hi (integrable_const (T : ℝ)) (fun ω =>
      rewardLoss_le_rounds _ _ _ (fun t ht i => run.y_mem t ht ω i))
    simpa using h
  exact ⟨(req false).trans (by linarith), (req true).trans (by linarith)⟩

end QProtocolRun

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

namespace CalibeatBandit

/-- At the stated horizon the tuned parameters are admissible and the explicit
swap-regret bound is at most \(\varepsilon T\). -/
theorem etaStar_spec {K T : ℕ} {ε : ℝ} (hK : 2 ≤ K) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hT : 1024 * (K : ℝ) ^ 2 * Real.log K / ε ^ 2 ≤ T) :
    0 < etaStar K T ∧ 0 < muStar K T ∧ muStar K T ≤ 1 / 2 ∧
    rT K T (etaStar K T) (muStar K T) + Real.sqrt (2 * T * K * Real.log K) ≤ ε * T := by
  let k : ℝ := K
  let t : ℝ := T
  let d : ℝ := k * Real.log k
  let b : ℝ := 2 * d + Real.log 2
  let a := Real.sqrt (b / (14 * k * t))
  let q := k * a
  have hk : 2 ≤ k := by dsimp [k]; exact_mod_cast hK
  have hk₀ : 0 < k := by linarith
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hk
  have hd : 0 < d := mul_pos hk₀ (hlog₂.trans_le hlog)
  have hb : 0 < b := by dsimp [b]; linarith
  have hb_le : b ≤ 3 * d := by
    have h := mul_nonneg (show 0 ≤ k - 1 by linarith) (hlog₂.trans_le hlog).le
    dsimp [b, d]
    linarith
  have hlog_pos : 0 < Real.log k := hlog₂.trans_le hlog
  have ht : 0 < t := lt_of_lt_of_le (by change 0 < 1024 * k ^ 2 * Real.log k / ε ^ 2; positivity) hT
  have htd : 1024 * k * d ≤ t * ε ^ 2 := by
    have h := (div_le_iff₀ (sq_pos_of_pos hε)).mp hT
    dsimp [d, k, t]
    nlinarith only [h]
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have haq : a ^ 2 * (14 * k * t) = b := by
    have h : a ^ 2 = b / (14 * k * t) := Real.sq_sqrt (by positivity)
    exact (eq_div_iff (by positivity)).mp h
  have hq : 0 < q := mul_pos hk₀ ha
  have hqt : 14 * q ^ 2 * t = k * b := by
    dsimp [q]
    linear_combination k * haq
  have hq_le : q ≤ ε / 32 := by
    have h₁ := mul_le_mul_of_nonneg_left hb_le hk₀.le
    have h₂ : 1024 * q ^ 2 * t ≤ ε ^ 2 * t := by
      nlinarith only [hqt, h₁, htd, mul_nonneg hk₀.le hd.le]
    have h₃ := le_of_mul_le_mul_right (show (32 * q) ^ 2 * t ≤ ε ^ 2 * t by
      nlinarith only [h₂]) ht
    by_contra! h
    have hprod := mul_pos (sub_pos.mpr (show ε < 32 * q by linarith))
      (show 0 < 32 * q + ε by positivity)
    nlinarith only [hprod, h₃]
  have hη : etaStar K T = a := by
    unfold etaStar
    have hsqrt : Real.sqrt ((2 * (K : ℝ) * Real.log K + Real.log 2) / (14 * K * T)) = a := by
      dsimp [a, b, d, k, t]
      congr 2
      ring
    rw [hsqrt]
    apply min_eq_right
    apply (le_div_iff₀ (by positivity)).mpr
    change a * (8 * k) ≤ 1
    dsimp [q] at hq_le
    nlinarith only [hq_le, hε₁]
  have hμ : muStar K T = 4 * q := by unfold muStar; rw [hη]; dsimp [q, k]; ring
  have hμ_le : 4 * q ≤ 1 / 2 := by linarith
  have hrec : rT K T (etaStar K T) (muStar K T) ≤ 28 * q * t := by
    rw [hη, hμ]
    have hba : b / a = 14 * q * t := by
      apply (div_eq_iff ha.ne').mpr
      dsimp [q]
      nlinarith only [haq]
    have hden : 0 < 1 - 4 * q := by linarith
    have hterm : 5 * q * t / (1 - 4 * q) ≤ 10 * q * t := by
      apply (div_le_iff₀ hden).mpr
      nlinarith only [mul_nonneg (show 0 ≤ q * t by positivity)
        (show 0 ≤ 1 / 2 - 4 * q by linarith)]
    unfold rT
    have hcoeff : 2 * (K : ℝ) * Real.log K + Real.log 2 = b := by dsimp [b, d, k]; ring
    rw [hcoeff]
    change 4 * q * t + b / a + (5 * a * k * t) / (1 - 4 * q) ≤ _
    rw [hba, show 5 * a * k * t = 5 * q * t by dsimp [q]; ring]
    linarith
  have hs : Real.sqrt (2 * t * k * Real.log k) ≤ ε * t / 8 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have h₁ : 128 * d ≤ t * ε ^ 2 := by
      have h₂ := mul_nonneg (show 0 ≤ 1024 * k - 128 by linarith) hd.le
      nlinarith only [h₂, htd]
    have h₂ := mul_le_mul_of_nonneg_right h₁ ht.le
    dsimp [d] at h₂
    nlinarith only [h₂]
  refine ⟨hη ▸ ha, hμ ▸ mul_pos (by norm_num) hq, hμ ▸ hμ_le, ?_⟩
  have h₁ := mul_le_mul_of_nonneg_right hq_le ht.le
  change _ + Real.sqrt (2 * t * k * Real.log k) ≤ ε * t
  nlinarith only [hrec, hs, h₁]

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

/-- The cumulative form of the worst-case regret rate, including one log factor. -/
noncomputable def robustRate (K T : ℕ) (ζ : ℝ) : ℝ :=
  (K : ℝ) * (T : ℝ) ^ ((1 + ζ) / 2) * (1 + Real.log ((K : ℝ) * T))

theorem robustRate_normalize {K T : ℕ} (hT : 0 < T) (ζ C : ℝ) :
    C * robustRate K T ζ =
      (C * K * (T : ℝ) ^ (-(1 - ζ) / 2) * (1 + Real.log ((K : ℝ) * T)) ^ (1 : ℕ)) * T := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  unfold robustRate
  rw [pow_one, show (1 + ζ) / 2 = -(1 - ζ) / 2 + 1 by ring,
    Real.rpow_add hT', Real.rpow_one]
  ring

theorem robustRate_ge_one {K T : ℕ} (hK : 1 ≤ K) (hT : 1 ≤ T)
    {ζ : ℝ} (hζ : 0 ≤ ζ) : 1 ≤ robustRate K T ζ := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hm := one_le_mul_of_one_le_of_one_le hK' hT'
  unfold robustRate
  refine one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hK' (Real.one_le_rpow hT' (by positivity))) ?_
  linarith [Real.log_nonneg hm]

theorem robustL_nonneg {K T s : ℕ} (hK : 1 ≤ K) (hT : 1 ≤ T) (hs : 1 ≤ s) :
    0 ≤ robustL K T s := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hall : 1 ≤ 4 * (s : ℝ) * (s + 1) * (T : ℝ) ^ 2 := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num) hs') (by linarith))
      (one_le_pow₀ hT')
  unfold robustL
  exact add_nonneg (mul_nonneg (by positivity) (Real.log_nonneg hK')) (Real.log_nonneg hall)

private theorem robustPrefixThreshold_eq {K T s : ℕ}
    (hK : 1 ≤ K) (hT : 1 ≤ T) (hs : 1 ≤ s) (ζ : ℝ) :
    (s : ℝ) * robustC K T ζ s =
      Real.sqrt (2 * s * (K * (T : ℝ) ^ ζ + 2) * robustL K T s) +
        (K * (T : ℝ) ^ ζ + 1) * robustL K T s / 3 := by
  let x : ℝ := 2 * (K * (T : ℝ) ^ ζ + 2) * robustL K T s
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hx : 0 ≤ x := by
    have hL := robustL_nonneg hK hT hs
    dsimp [x]
    positivity
  have heq : (s : ℝ) * Real.sqrt (x / s) = Real.sqrt (s * x) := by
    symm
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    have hsq := Real.sq_sqrt (show 0 ≤ x / (s : ℝ) by positivity)
    rw [mul_pow, hsq]
    field_simp
  unfold robustC
  change (s : ℝ) * (Real.sqrt (x / s) +
      (K * (T : ℝ) ^ ζ + 1) * robustL K T s / (3 * s)) = _
  rw [mul_add, heq]
  have hx' : (s : ℝ) * x = 2 * s * (K * (T : ℝ) ^ ζ + 2) * robustL K T s := by
    dsimp [x]
    ring
  rw [hx']
  congr 1
  field_simp

theorem robustPrefixThreshold_mono {K T s : ℕ}
    (hK : 1 ≤ K) (hT : 1 ≤ T) (hs : 1 ≤ s) (hst : s ≤ T) (ζ : ℝ) :
    (s : ℝ) * robustC K T ζ s ≤ T * robustC K T ζ T := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hst' : (s : ℝ) ≤ T := by exact_mod_cast hst
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hL : robustL K T s ≤ robustL K T T := by
    unfold robustL
    apply add_le_add_right
    apply Real.log_le_log (by positivity)
    gcongr
  have hLs := robustL_nonneg hK hT hs
  have hLt := robustL_nonneg hK hT hT
  rw [robustPrefixThreshold_eq hK hT hs, robustPrefixThreshold_eq hK hT hT]
  gcongr

theorem robustThreshold_le_rate {K T : ℕ} (hK : 1 ≤ K) (hT : 1 ≤ T)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hsmall : robustRate K T ζ ≤ T) :
    (T : ℝ) * robustC K T ζ T ≤ 20 * robustRate K T ζ := by
  let k : ℝ := K
  let t : ℝ := T
  let L := 1 + Real.log (k * t)
  let a := (1 + ζ) / 2
  have hk : 1 ≤ k := by
    change (1 : ℝ) ≤ (K : ℝ)
    exact_mod_cast hK
  have ht : 1 ≤ t := by
    change (1 : ℝ) ≤ (T : ℝ)
    exact_mod_cast hT
  have hk₀ : 0 < k := by linarith
  have ht₀ : 0 < t := by linarith
  have hkt : 1 ≤ k * t := one_le_mul_of_one_le_of_one_le hk ht
  have hloga : Real.log k ≤ Real.log (k * t) :=
    Real.log_le_log hk₀ (le_mul_of_one_le_right hk₀.le ht)
  have hlogb : Real.log t ≤ Real.log (k * t) :=
    Real.log_le_log ht₀ (le_mul_of_one_le_left ht₀.le hk)
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hkt]
  have hlogprod : Real.log (4 * t * (t + 1) * t ^ 2) ≤ 7 + 4 * Real.log t := by
    have harg : 4 * t * (t + 1) * t ^ 2 ≤ 8 * t ^ 4 := by
      have hle : t + 1 ≤ 2 * t := by linarith
      calc
        _ ≤ 4 * t * (2 * t) * t ^ 2 := by gcongr
        _ = _ := by ring
    refine (Real.log_le_log (by positivity) harg).trans ?_
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (pow_ne_zero _ ht₀.ne'), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_le_sub_one_of_pos (x := 8) (by norm_num)]
  have hLbound : robustL K T T ≤ 12 * k * L := by
    unfold robustL
    change k * Real.log k + Real.log (4 * t * (t + 1) * t ^ 2) ≤ _
    have h1 := mul_le_mul_of_nonneg_left hloga hk₀.le
    have h2 : L ≤ k * L := le_mul_of_one_le_left (by linarith) hk
    have h3 : k * Real.log (k * t) ≤ k * L := by
      gcongr
      dsimp [L]
      linarith
    linarith only [h1, h2, h3, hlogprod, hlogb, hL, show Real.log (k * t) = L - 1 by dsimp [L]; ring]
  have hL₀ := robustL_nonneg hK hT hT
  have hz : 1 ≤ t ^ ζ := Real.one_le_rpow ht hζ
  have ha : 1 ≤ t ^ a := Real.one_le_rpow ht (by dsimp [a]; linarith)
  have hkz : 1 ≤ k * t ^ ζ := one_le_mul_of_one_le_of_one_le hk hz
  have hsq : (t ^ a) ^ 2 = t * t ^ ζ := by
    rw [pow_two, ← Real.rpow_add ht₀,
      show a + a = 1 + ζ by dsimp [a]; ring,
      Real.rpow_add ht₀, Real.rpow_one]
  have hr : robustRate K T ζ = k * (t ^ a) * L := rfl
  have hroot : Real.sqrt (2 * t * (k * t ^ ζ + 2) * robustL K T T) ≤
      9 * (k * (t ^ a) * L) := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    have hA : k * t ^ ζ + 2 ≤ 3 * (k * t ^ ζ) := by linarith
    calc
      _ ≤ 2 * t * (3 * (k * t ^ ζ)) * (12 * k * L) := by gcongr
      _ = 72 * k ^ 2 * (t ^ a) ^ 2 * L := by rw [hsq]; ring
      _ ≤ (9 * (k * t ^ a * L)) ^ 2 := by
        have hLsq : L ≤ L ^ 2 := by nlinarith [mul_nonneg (show 0 ≤ L by linarith) (sub_nonneg.mpr hL)]
        have hh := mul_le_mul_of_nonneg_left hLsq (show 0 ≤ 72 * k ^ 2 * (t ^ a) ^ 2 by positivity)
        have hnon := mul_nonneg (show (0 : ℝ) ≤ 9 by norm_num) (show 0 ≤ k ^ 2 * (t ^ a) ^ 2 * L ^ 2 by positivity)
        nlinarith only [hh, hnon]
  have hterm : (k * t ^ ζ + 1) * robustL K T T / 3 ≤
      8 * (k * t ^ a * L) := by
    have hA : k * t ^ ζ + 1 ≤ 2 * (k * t ^ ζ) := by linarith
    have hsmall' : (k * L) * t ^ a ≤ t := by
      rw [hr] at hsmall
      nlinarith only [hsmall]
    have hs := mul_le_mul_of_nonneg_right hsmall' (show 0 ≤ k * t ^ a by positivity)
    have hrewrite : (k * L * t ^ a) * (k * t ^ a) = (k ^ 2 * t ^ ζ * L) * t := by
      calc
        _ = k ^ 2 * (t ^ a) ^ 2 * L := by ring
        _ = _ := by rw [hsq]; ring
    rw [hrewrite, show t * (k * t ^ a) = (k * t ^ a) * t by ring] at hs
    have hB := le_of_mul_le_mul_right hs ht₀
    calc
      _ ≤ (2 * (k * t ^ ζ)) * (12 * k * L) / 3 := by gcongr
      _ = 8 * (k ^ 2 * t ^ ζ * L) := by ring
      _ ≤ 8 * (k * t ^ a * L) := by
        exact mul_le_mul_of_nonneg_left (hB.trans (le_mul_of_one_le_right (by positivity) hL)) (by norm_num)
  rw [robustPrefixThreshold_eq hK hT hT, hr]
  change Real.sqrt (2 * t * (k * t ^ ζ + 2) * robustL K T T) +
      (k * t ^ ζ + 1) * robustL K T T / 3 ≤ 20 * (k * t ^ a * L)
  linarith only [hroot, hterm, show 0 ≤ k * t ^ a * L by positivity]

theorem robustRate_restart_parameters {K T : ℕ} (hK : 2 ≤ K) (hT : 1 ≤ T)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hsmall : 32 * robustRate K T ζ ≤ T) :
    0 < etaStar K T ∧ 0 < muStar K T ∧ muStar K T ≤ 1 / 2 ∧
    rT K T (etaStar K T) (muStar K T) + Real.sqrt (2 * T * K * Real.log K) ≤
      32 * robustRate K T ζ := by
  let k : ℝ := K
  let t : ℝ := T
  let a := (1 + ζ) / 2
  let L := 1 + Real.log (k * t)
  let B := 32 * robustRate K T ζ
  let e := B / t
  have hk : 1 ≤ k := by
    have hk' : 1 ≤ K := by omega
    change (1 : ℝ) ≤ (K : ℝ)
    exact_mod_cast hk'
  have ht : 1 ≤ t := by
    change (1 : ℝ) ≤ (T : ℝ)
    exact_mod_cast hT
  have ht₀ : 0 < t := by linarith
  have hk₀ : 0 < k := by linarith
  have hkt : 1 ≤ k * t := one_le_mul_of_one_le_of_one_le hk ht
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hkt]
  have hlog : Real.log k ≤ L ^ 2 := by
    have hlog' := Real.log_le_log hk₀ (le_mul_of_one_le_right hk₀.le ht)
    have hL' : L ≤ L ^ 2 := by nlinarith [mul_nonneg (show 0 ≤ L by linarith) (sub_nonneg.mpr hL)]
    dsimp [L] at hL'
    dsimp [L]
    linarith
  have hB : B = 32 * k * (t ^ a) * L := by dsimp [B, robustRate, k, t, a, L]; ring
  have he : 0 < e := by
    dsimp [e]
    rw [hB]
    positivity
  have he₁ : e ≤ 1 := by
    exact (div_le_one ht₀).2 hsmall
  have hLsq : 0 ≤ L ^ 2 := sq_nonneg _
  have htsq : t ≤ (t ^ a) ^ 2 := by
    rw [pow_two, ← Real.rpow_add ht₀]
    simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le ht
      (show 1 ≤ a + a by dsimp [a]; linarith) : t ^ (1 : ℝ) ≤ _)
  have htarget : 1024 * k ^ 2 * Real.log k / e ^ 2 ≤ t := by
    apply (div_le_iff₀ (sq_pos_of_pos he)).2
    have he' : e ^ 2 * t ^ 2 = B ^ 2 := by dsimp [e]; rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ ht₀.ne')]
    have hb' : 1024 * k ^ 2 * Real.log k * t ≤ B ^ 2 := by
      rw [hB]
      calc
        _ ≤ 1024 * k ^ 2 * L ^ 2 * (t ^ a) ^ 2 := by gcongr
        _ = _ := by ring
    apply le_of_mul_le_mul_right _ ht₀
    nlinarith only [hb', he']
  obtain ⟨h1,h2,h3,h4⟩ := etaStar_spec (K := K) (T := T) hK he he₁ htarget
  refine ⟨h1,h2,h3,h4.trans_eq ?_⟩
  change B / t * t = B
  exact div_mul_cancel₀ _ ht₀.ne'

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal

namespace CalibeatBandit.Supplement

private theorem swapRegret_succ_le {K s : ℕ} (y : ℕ → Fin K → ℝ) (J : ℕ → Fin K)
    (hy : ∀ i, y s i ∈ Icc (0 : ℝ) 1) :
    swapRegret (s + 1) y J ≤ swapRegret s y J + 1 := by
  unfold swapRegret
  apply Finset.sup'_le
  intro f _
  rw [Finset.sum_range_succ]
  refine add_le_add (Finset.le_sup' (fun σ : Fin K → Fin K =>
    ∑ t ∈ Finset.range s, (y t (σ (J t)) - y t (J t))) (Finset.mem_univ f)) ?_
  linarith [(hy (f (J s))).2, (hy (J s)).1]

namespace QProtocolRun

variable {K T : ℕ} {ζ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  (run : QProtocolRun K T P (robustPolicy K T ζ))

private theorem measurable_qRunRewardLoss_stopped (n : Ω → ℕ)
    (hn : Measurable n) (hnT : ∀ ω, n ω ≤ T) (bJ bI : Bool) :
    Measurable (fun ω => rewardLoss (n ω) (fun t => run.y t ω)
      (fun t => if bJ then run.J t ω else run.I t ω)
      (fun t => if bI then run.J t ω else run.I t ω)) := by
  let a (ω : Ω) : Fin (T + 1) := ⟨n ω, Nat.lt_succ_of_le (hnT ω)⟩
  have ha : Measurable a := measurable_to_countable' fun i => by
    have h : a ⁻¹' {i} = n ⁻¹' {(i : ℕ)} := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, ← Fin.val_eq_val, a]
    rw [h]
    exact hn (measurableSet_singleton _)
  exact measurable_select ha
    (fun i => run.measurable_qRunRewardLoss (Nat.le_of_lt_succ i.isLt) bJ bI)

set_option maxHeartbeats 1200000 in
/-- The expected regret accrued before the restart is controlled by the
switching threshold, the exploration count, and the concentration failure
probability. The stopping length may include the crossing round. -/
theorem robust_prefix_expected (hK : 1 ≤ K) (hT : 1 ≤ T) (hζ : 0 ≤ ζ)
    (hC : 0 ≤ robustC K T ζ T)
    (n : Ω → ℕ) (hn : Measurable n) (hnT : ∀ ω, n ω ≤ T)
    (hfollowing : ∀ ω t, t < n ω → ω ∈ run.robustFollowing t)
    (E : Set Ω) (hE : MeasurableSet E) (hbad : P Eᶜ ≤ ENNReal.ofReal ((T : ℝ) ^ (-2 : ℝ)))
    (hest : ∀ ω ∈ E, ∀ t < T, ω ∈ run.robustFollowing t →
      |robustHhat T ζ (fun v => run.q v ω) (fun v => run.I v ω)
        (fun v => run.y v ω (run.I v ω)) (t + 1) -
        pseudoSwapRegret (t + 1) (fun v => run.q v ω) (fun v => run.y v ω)|
        ≤ (↑(t + 1) : ℝ) * robustC K T ζ (t + 1))
    (hrec : ∀ ω ∈ E, ∀ t < T,
      |swapRegret (t + 1) (fun v => run.y v ω) (fun v => run.J v ω) -
        pseudoSwapRegret (t + 1) (fun v => run.q v ω) (fun v => run.y v ω)|
        ≤ (↑(t + 1) : ℝ) * robustC K T ζ (t + 1)) :
    let B : ℝ := 5 * T * robustC K T ζ T + 1 + 2 * robustEps T ζ * T + T * (T : ℝ) ^ (-2 : ℝ)
    (∫ ω, swapRegret (n ω) (fun t => run.y t ω) (fun t => run.I t ω) ∂P) ≤ B ∧
    (∫ ω, rewardLoss (n ω) (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P) ≤ B := by
  classical
  intro B
  let C : ℝ := 5 * T * robustC K T ζ T + 1
  let D := run.followDisagreements
  let H (ω : Ω) : ℝ := Eᶜ.indicator (fun _ => (T : ℝ)) ω
  have hC₀ : 0 ≤ 5 * (T : ℝ) * robustC K T ζ T := by positivity
  have hC₁ : 0 ≤ C := by dsimp [C]; positivity
  have hJ (ω : Ω) (hω : ω ∈ E) :
      swapRegret (n ω) (fun t => run.y t ω) (fun t => run.J t ω) ≤ C := by
    by_cases hsmall : n ω ≤ 1
    · have h := rewardLoss_le_rounds (s := n ω) (fun t => run.y t ω)
        (fun t => run.J t ω) (fun t => run.J t ω) (fun t ht i =>
          run.y_mem t (ht.trans_le (hnT ω)) ω i)
      exact h.trans (show (n ω : ℝ) ≤ C by
        have hm : (n ω : ℝ) ≤ 1 := by exact_mod_cast hsmall
        dsimp [C]
        linarith)
    · obtain ⟨s, hs⟩ : ∃ s : ℕ, n ω = s + 2 := ⟨n ω - 2, by omega⟩
      have hprev : s + 1 < n ω := by omega
      have ht : s < T := lt_of_lt_of_le (show s < n ω by omega) (hnT ω)
      have hfp := hfollowing ω (s + 1) hprev
      have hf := hfollowing ω s (by omega)
      have hno := hfp s (Nat.lt_succ_self s)
      unfold robustCrossed at hno
      have hcap := le_of_not_gt hno
      have he := (abs_le.mp (hest ω hω s ht hf)).1
      have hr := (abs_le.mp (hrec ω hω s ht)).2
      have hmono := robustPrefixThreshold_mono hK hT (by omega : 1 ≤ s + 1)
        (by omega : s + 1 ≤ T) ζ
      have hprevR : swapRegret (s + 1) (fun t => run.y t ω) (fun t => run.J t ω)
          ≤ 5 * (T : ℝ) * robustC K T ζ T := by
        push_cast at hcap he hr hmono
        linarith
      have hstep := swapRegret_succ_le (s := s + 1) (fun t => run.y t ω)
        (fun t => run.J t ω) (run.y_mem _ (hprev.trans_le (hnT ω)) ω)
      rw [hs]
      exact hstep.trans (add_le_add hprevR le_rfl)
  have hD (ω : Ω) :
      (∑ t ∈ Finset.range (n ω), if run.I t ω = run.J t ω then (0 : ℝ) else 1) ≤ D ω := by
    unfold D followDisagreements
    calc
      _ = ∑ t ∈ Finset.range (n ω), (run.robustFollowing t).indicator
          (fun ω => if run.I t ω = run.J t ω then (0 : ℝ) else 1) ω := by
        exact Finset.sum_congr rfl fun t ht =>
          (Set.indicator_of_mem (hfollowing ω t (Finset.mem_range.mp ht))
            (fun v => if run.I t v = run.J t v then (0 : ℝ) else 1)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (hnT ω)) fun t _ _ =>
          Set.indicator_nonneg (fun _ _ => by split <;> norm_num) _
  have hf (ω : Ω) (hω : ω ∈ E) :
      swapRegret (n ω) (fun t => run.y t ω) (fun t => run.I t ω) ≤ C + 2 * D ω ∧
      rewardLoss (n ω) (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ≤
        C + 2 * D ω := by
    obtain ⟨hs, hr⟩ := regret_le_of_disagreements (T := n ω)
      (fun t => run.y t ω) (fun t => run.I t ω) (fun t => run.J t ω)
      (fun t ht i => run.y_mem t (ht.trans_le (hnT ω)) ω i)
    exact ⟨hs.trans (by linarith [hJ ω hω, hD ω]),
      hr.trans (by linarith [hJ ω hω, hD ω, run.followDisagreements_nonneg ω])⟩
  have hDX := run.integrable_followDisagreements_and_le (by omega) (by omega) hζ
  have hdi : Integrable D P := hDX.1
  have hhi : Integrable H P := (integrable_const _).indicator hE.compl
  have hEH : ∫ ω, H ω ∂P ≤ (T : ℝ) * (T : ℝ) ^ (-2 : ℝ) := by
    change ∫ ω, Eᶜ.indicator (fun _ => (T : ℝ)) ω ∂P ≤ _
    rw [integral_indicator_const _ hE.compl, smul_eq_mul, mul_comm (T : ℝ)]
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    change (P Eᶜ).toReal ≤ _
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have bound (X : Ω → ℝ) (hXm : Measurable X) (hX : ∀ ω, |X ω| ≤ (T : ℝ))
      (hgood : ∀ ω ∈ E, X ω ≤ C + 2 * D ω) :
      ∫ ω, X ω ∂P ≤ B := by
    have hXi := integrable_of_abs_bound (P := P) hXm hX
    have hD2 : Integrable (fun ω => 2 * D ω) P := hdi.const_mul 2
    have hC2D : Integrable (fun ω => C + 2 * D ω) P :=
      (integrable_const C).add hD2
    have hx : (∫ ω, X ω ∂P) ≤ ∫ ω, (C + 2 * D ω) + H ω ∂P :=
      integral_mono hXi (hC2D.add hhi) (fun ω => by
        change X ω ≤ C + 2 * D ω + H ω
        by_cases hω : ω ∈ E
        · have hz : H ω = 0 := Set.indicator_of_notMem (not_not_intro hω) _
          rw [hz, add_zero]
          exact hgood ω hω
        · have ht : H ω = (T : ℝ) := Set.indicator_of_mem hω _
          rw [ht]
          linarith [(abs_le.mp (hX ω)).2, run.followDisagreements_nonneg ω])
    rw [integral_add hC2D hhi, integral_add (integrable_const C) hD2, integral_const_mul] at hx
    simp only [integral_const, probReal_univ, one_smul] at hx
    have hdle : ∫ ω, D ω ∂P ≤ robustEps T ζ * T := hDX.2
    dsimp [B, C]
    dsimp [C] at hx
    linarith only [hx, hdle, hEH]
  constructor
  · refine bound _ (run.measurable_qRunRewardLoss_stopped n hn hnT false false) ?_
      (fun ω hω => (hf ω hω).1)
    intro ω
    exact (rewardLoss_abs_le_rounds _ _ _ (fun t ht i => run.y_mem t
      (ht.trans_le (hnT ω)) ω i)).trans (by exact_mod_cast hnT ω)
  · refine bound _ (run.measurable_qRunRewardLoss_stopped n hn hnT true false) ?_
      (fun ω hω => (hf ω hω).2)
    intro ω
    exact (rewardLoss_abs_le_rounds _ _ _ (fun t ht i => run.y_mem t
      (ht.trans_le (hnT ω)) ω i)).trans (by exact_mod_cast hnT ω)

end QProtocolRun

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

open Matrix
open scoped BigOperators Nat

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open MeasureTheory Matrix Filter
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open MeasureTheory Matrix Filter
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open Matrix CalibeatBandit
open scoped BigOperators


end

section

set_option autoImplicit false

open MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

universe u

/-- The finite-horizon inequalities in the first conjunct of Theorem 3.2. -/
def HasFiniteHorizonBounds : Prop :=
  ∀ (K T : ℕ) (η μ : ℝ), 0 < K → 0 < η → 0 < μ → μ ≤ 1 / 2 → 4 * K * η ≤ μ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (run : ProtocolRun K T P (calibeatPolicy K η μ)),
      ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P
          ≤ rT K T η μ + Real.sqrt (2 * T * K * Real.log K) ∧
      ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P
          ≤ rT K T η μ


theorem finite_horizon_bounds : HasFiniteHorizonBounds.{u} := CalibeatBandit.theorem_3_2.{u}.1


end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

open Set Filter MeasureTheory
open scoped ENNReal

section Segment

variable {K n m : ℕ}

/-- The best swap over a concatenated history cannot improve on the sum of
the best swaps on the two parts of the history. -/
theorem swapRegret_split_le (y : ℕ → Fin K → ℝ) (I : ℕ → Fin K) :
    swapRegret (n + m) y I ≤ swapRegret n y I +
      swapRegret m (fun t => y (n + t)) (fun t => I (n + t)) := by
  classical
  unfold swapRegret
  apply Finset.sup'_le
  intro f _
  rw [Finset.sum_range_add]
  apply add_le_add
  · exact Finset.le_sup' (fun f : Fin K → Fin K =>
      ∑ t ∈ Finset.range n, (y t (f (I t)) - y t (I t))) (Finset.mem_univ f)
  · exact Finset.le_sup' (fun f : Fin K → Fin K =>
      ∑ t ∈ Finset.range m, (y (n + t) (f (I (n + t))) - y (n + t) (I (n + t))))
      (Finset.mem_univ f)

/-- The analogous splitting bound for reward loss against a recommendation. -/
theorem rewardLoss_split_le (y : ℕ → Fin K → ℝ) (J I : ℕ → Fin K) :
    rewardLoss (n + m) y J I ≤ rewardLoss n y J I +
      rewardLoss m (fun t => y (n + t)) (fun t => J (n + t)) (fun t => I (n + t)) := by
  classical
  unfold rewardLoss
  apply Finset.sup'_le
  intro f _
  rw [Finset.sum_range_add]
  apply add_le_add
  · exact Finset.le_sup' (fun f : Fin K → Fin K =>
      ∑ t ∈ Finset.range n, (y t (f (J t)) - y t (I t))) (Finset.mem_univ f)
  · exact Finset.le_sup' (fun f : Fin K → Fin K =>
      ∑ t ∈ Finset.range m, (y (n + t) (f (J (n + t))) - y (n + t) (I (n + t))))
      (Finset.mem_univ f)

theorem QProtocolRun.info_le_info {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {policy : QPolicy K} (run : QProtocolRun K T P policy)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ T) : run.info a ≤ run.info b :=
  run.toDrawRun.info_le_info hab hb

theorem QProtocolRun.integrable_rewardLoss_segment {K T : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {policy : QPolicy K} (run : QProtocolRun K T P policy)
    (n m : ℕ) (hnm : n + m ≤ T) :
    Integrable (fun ω => rewardLoss m (fun t => run.y (n + t) ω)
      (fun t => run.J (n + t) ω) (fun t => run.I (n + t) ω)) P := by
  classical
  unfold rewardLoss
  apply integrable_finset_max (B := (m : ℝ))
  · intro f
    refine Finset.measurable_sum _ fun t ht => ?_
    have hlt : n + t < T := by
      have := Finset.mem_range.mp ht
      omega
    have hy := (run.y_measurable (n + t) hlt).mono (run.info_le _ hlt.le) le_rfl
    have hj := (run.J_measurable (n + t) hlt).mono (run.info_le _ (by omega)) le_rfl
    have hi := (run.I_measurable (n + t) hlt).mono (run.info_le _ (by omega)) le_rfl
    exact (measurable_select hj (fun i => (measurable_pi_apply (f i)).comp hy)).sub
      (measurable_select hi (fun i => (measurable_pi_apply i).comp hy))
  · intro f ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _t ∈ Finset.range m, (1 : ℝ) := by
        refine Finset.sum_le_sum fun t ht => ?_
        have hlt : n + t < T := by
          have := Finset.mem_range.mp ht
          omega
        have hy₁ := run.y_mem _ hlt ω (f (run.J (n + t) ω))
        have hy₂ := run.y_mem _ hlt ω (run.I (n + t) ω)
        exact abs_le.mpr ⟨by linarith [hy₁.1, hy₂.2], by linarith [hy₁.2, hy₂.1]⟩
      _ = _ := by simp

theorem QProtocolRun.integrable_swapRegret_segment {K T : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {policy : QPolicy K} (run : QProtocolRun K T P policy)
    (n m : ℕ) (hnm : n + m ≤ T) :
    Integrable (fun ω => swapRegret m (fun t => run.y (n + t) ω)
      (fun t => run.I (n + t) ω)) P := by
  classical
  unfold swapRegret
  apply integrable_finset_max (B := (m : ℝ))
  · intro f
    refine Finset.measurable_sum _ fun t ht => ?_
    have hlt : n + t < T := by
      have := Finset.mem_range.mp ht
      omega
    have hy := (run.y_measurable (n + t) hlt).mono (run.info_le _ hlt.le) le_rfl
    have hi := (run.I_measurable (n + t) hlt).mono (run.info_le _ (by omega)) le_rfl
    exact (measurable_select hi (fun i => (measurable_pi_apply (f i)).comp hy)).sub
      (measurable_select hi (fun i => (measurable_pi_apply i).comp hy))
  · intro f ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _t ∈ Finset.range m, (1 : ℝ) := by
        refine Finset.sum_le_sum fun t ht => ?_
        have hlt : n + t < T := by
          have := Finset.mem_range.mp ht
          omega
        have hy₁ := run.y_mem _ hlt ω (f (run.I (n + t) ω))
        have hy₂ := run.y_mem _ hlt ω (run.I (n + t) ω)
        exact abs_le.mpr ⟨by linarith [hy₁.1, hy₂.2], by linarith [hy₁.2, hy₂.1]⟩
      _ = _ := by simp

end Segment

section Condition

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem condExp_smul_measure_ae [IsFiniteMeasure P] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {f : Ω → ℝ} (hf : Integrable f P)
    {c : ℝ≥0∞} (hc : c ≠ ∞) :
    condExp m (c • P) f =ᵐ[c • P] condExp m P f := by
  let : IsFiniteMeasure (c • P) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top P _)⟩
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm (hf.smul_measure hc)
  · intro s _ _
    exact (integrable_condExp.smul_measure hc).integrableOn
  · intro s hs _
    simp only [Measure.restrict_smul, integral_smul_measure]
    rw [setIntegral_condExp hm hf hs]
  · exact stronglyMeasurable_condExp.aestronglyMeasurable

/-- Conditional probability on a measurable event of positive mass. -/
noncomputable def eventProbability (P : Measure Ω) (s : Set Ω) : Measure Ω :=
  (P s)⁻¹ • P.restrict s

theorem eventProbability_isProbabilityMeasure [IsFiniteMeasure P] {s : Set Ω}
    (hs₀ : P s ≠ 0) : IsProbabilityMeasure (eventProbability P s) := by
  constructor
  simp [eventProbability, ENNReal.inv_mul_cancel hs₀ (measure_ne_top P s)]

theorem ae_eventProbability_mem [IsFiniteMeasure P] {s : Set Ω} (hs : MeasurableSet s) :
    ∀ᵐ ω ∂eventProbability P s, ω ∈ s :=
  Measure.ae_smul_measure (ae_restrict_mem hs) _

theorem ae_eventProbability_of_ae {s : Set Ω} {p : Ω → Prop}
    (h : ∀ᵐ ω ∂P, p ω) : ∀ᵐ ω ∂eventProbability P s, p ω :=
  Measure.ae_smul_measure (ae_restrict_of_ae h) _

theorem condExp_eventProbability_ae [IsFiniteMeasure P] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {s : Set Ω} (hs : MeasurableSet[m] s) (hs₀ : P s ≠ 0)
    {f : Ω → ℝ} (hf : Integrable f P) :
    Filter.EventuallyEq (ae (@eventProbability Ω mΩ P s))
      (condExp m (@eventProbability Ω mΩ P s) f) (condExp m P f) := by
  unfold eventProbability
  have h₁ := @condExp_smul_measure_ae Ω mΩ (P.restrict s) _ m hm f
    hf.integrableOn (P s)⁻¹ (ENNReal.inv_ne_top.mpr hs₀)
  have h₂ := condExp_restrict_ae_eq_restrict (μ := P) hm hs hf
  exact h₁.trans (Measure.ae_smul_measure h₂ _)

end Condition

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

open MeasureTheory Filter Set
open scoped ENNReal

/-- A shifted run on the event that the learner has switched at time `n`.
The event is known at time `n`, so conditioning on it leaves the later
conditional action and recommendation laws unchanged. -/
noncomputable def QProtocolRun.restartOn {K T : ℕ} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {qpolicy : QPolicy K} (run : QProtocolRun K T P qpolicy)
    (n : ℕ) (hn : n ≤ T) (s : Set Ω) (hs : MeasurableSet[run.info n] s)
    (hs₀ : P s ≠ 0) (policy : Policy K)
    (hpolicy : ∀ t < T - n, ∀ ω ∈ s,
      run.toDrawRun.played (n + t) ω =
        policy t (fun i => run.J (n + i) ω) (fun i => run.I (n + i) ω)
          (fun i => run.y (n + i) ω (run.I (n + i) ω))) :
    ProtocolRun K (T - n) (eventProbability P s) policy where
  info t := run.info (n + t)
  q t := run.q (n + t)
  y t := run.y (n + t)
  J t := run.J (n + t)
  I t := run.I (n + t)
  info_le t ht := run.info_le _ (by omega)
  info_mono t ht := run.info_mono _ (by omega)
  q_measurable t ht := run.q_measurable _ (by omega)
  y_measurable t ht := run.y_measurable _ (by omega)
  J_measurable t ht := run.J_measurable _ (by omega)
  I_measurable t ht := run.I_measurable _ (by omega)
  q_nonneg t ht := run.q_nonneg _ (by omega)
  q_sum t ht := run.q_sum _ (by omega)
  y_mem t ht := run.y_mem _ (by omega)
  J_law t ht j := by
    have ht' : n + t < T := by omega
    have hs' : MeasurableSet[run.info (n + t)] s :=
      run.info_le_info (by omega) ht'.le _ hs
    have hj := (run.J_measurable _ ht').mono (run.info_le _ (by omega)) le_rfl
    exact (condExp_eventProbability_ae (run.info_le _ ht'.le) hs' hs₀
      ((integrable_const (1 : ℝ)).indicator (hj (measurableSet_singleton j)))).trans
        (ae_eventProbability_of_ae (run.J_law _ ht' j))
  I_law t ht i := by
    have ht' : n + t < T := by omega
    have hsambient : MeasurableSet s := run.info_le _ hn _ hs
    have hs' : MeasurableSet[run.preDraw (n + t)] s :=
      (run.info_le_info (by omega) ht'.le).trans le_sup_left _ hs
    have hi := (run.I_measurable _ ht').mono (run.info_le _ (by omega)) le_rfl
    refine (condExp_eventProbability_ae (run.toDrawRun.preDraw_le_ambient ht')
      hs' hs₀ ((integrable_const (1 : ℝ)).indicator (hi (measurableSet_singleton i)))).trans ?_
    filter_upwards [ae_eventProbability_of_ae (run.I_law _ ht' i),
      ae_eventProbability_mem (P := P) hsambient] with ω hl hω
    exact hl.trans (congrFun (hpolicy t ht ω hω) i)

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement.QProtocolRun

open MeasureTheory Set

variable {K T : ℕ} {ζ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  (run : QProtocolRun K T P (robustPolicy K T ζ))

/-- The crossing round belongs to the follow phase, so the restart begins
one round after the first crossing. If there is no crossing, all rounds follow. -/
noncomputable def robustFollowLength (ω : Ω) : ℕ := by
  classical
  exact if h : ∃ u < T, robustCrossed T ζ (fun s => run.q s ω)
    (fun s => run.I s ω) (fun s => run.y s ω (run.I s ω)) (u + 1) then Nat.find h + 1 else T

theorem robustFollowLength_le (ω : Ω) : run.robustFollowLength ω ≤ T := by
  classical
  unfold robustFollowLength
  split
  · rename_i h
    exact Nat.succ_le_of_lt (Nat.find_spec h).1
  · rfl

theorem lt_robustFollowLength_iff (ω : Ω) (t : ℕ) :
    t < run.robustFollowLength ω ↔ t < T ∧ ω ∈ run.robustFollowing t := by
  classical
  change _ ↔ t < T ∧ ∀ s < t, ¬ robustCrossed T ζ (fun v => run.q v ω)
    (fun v => run.I v ω) (fun v => run.y v ω (run.I v ω)) (s + 1)
  unfold robustFollowLength
  split
  · rename_i h
    have hs := Nat.find_spec h
    constructor
    · intro ht
      refine ⟨by omega, fun s hst hc => ?_⟩
      exact (Nat.find_min h (show s < Nat.find h by omega)) ⟨by omega, hc⟩
    · rintro ⟨_, hnever⟩
      by_contra! hn
      exact hnever _ (by omega) hs.2
  · rename_i h
    exact ⟨fun ht => ⟨ht, fun s hst hc => h ⟨s, hst.trans ht, hc⟩⟩, And.left⟩

theorem robustFollowLength_pos (hT : 0 < T) (ω : Ω) :
    0 < run.robustFollowLength ω :=
  (run.lt_robustFollowLength_iff ω 0).2 ⟨hT, by simp [robustFollowing]⟩

theorem follows_before_length {ω : Ω} {t : ℕ} (ht : t < run.robustFollowLength ω) :
    ω ∈ run.robustFollowing t :=
  ((run.lt_robustFollowLength_iff ω t).1 ht).2

theorem measurableSet_robustFollowLength_eq {n : ℕ} (hn : n ≤ T) :
    MeasurableSet[run.info n] {ω | run.robustFollowLength ω = n} := by
  rcases n with _ | n
  · rcases eq_zero_or_pos T with hT | hT
    · have he : {ω | run.robustFollowLength ω = 0} = univ := by
        ext ω
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        have := run.robustFollowLength_le ω
        omega
      rw [he]
      exact .univ
    · have he : {ω | run.robustFollowLength ω = 0} = ∅ := by
        ext ω
        exact ⟨fun h => False.elim (Nat.ne_of_gt (run.robustFollowLength_pos hT ω) h),
          fun h => False.elim h⟩
      rw [he]
      exact @MeasurableSet.empty Ω (run.info 0)
  · have he : {ω | run.robustFollowLength ω = n + 1} =
        run.robustFollowing n ∩ {ω | ¬ (n + 1 < T ∧ ω ∈ run.robustFollowing (n + 1))} := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff]
      rw [← (run.lt_robustFollowLength_iff ω (n + 1))]
      have h := run.lt_robustFollowLength_iff ω n
      have hn' : n < T := by omega
      constructor
      · intro hlen
        exact ⟨(h.mp (by omega)).2, by omega⟩
      · rintro ⟨hF, hnF⟩
        have hlen := h.mpr ⟨hn', hF⟩
        omega
    rw [he]
    have hF := run.measurableSet_robustFollowing (show n ≤ T by omega)
    refine (run.info_mono n (by omega) _ hF).inter ?_
    by_cases h : n + 1 < T
    · have he : {ω | ¬ (n + 1 < T ∧ ω ∈ run.robustFollowing (n + 1))} =
          (run.robustFollowing (n + 1))ᶜ := by ext ω; simp [h]
      rw [he]
      exact (run.measurableSet_robustFollowing hn).compl
    · simp [h]

theorem measurable_robustFollowLength : Measurable run.robustFollowLength := by
  apply measurable_to_countable'
  intro n
  by_cases hn : n ≤ T
  · exact run.info_le n hn _ (run.measurableSet_robustFollowLength_eq hn)
  · have he : run.robustFollowLength ⁻¹' {n} = ∅ := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      have := run.robustFollowLength_le ω
      omega
    rw [he]
    exact .empty

theorem played_eq_restart_of_length {n t : ℕ} {ω : Ω} (ht : t < T - n)
    (hω : run.robustFollowLength ω = n) :
    run.toDrawRun.played (n + t) ω =
      calibeatPolicy K (etaStar K T) (muStar K T) t
        (fun i => run.J (n + i) ω) (fun i => run.I (n + i) ω)
        (fun i => run.y (n + i) ω (run.I (n + i) ω)) := by
  classical
  have hn : n < T := by omega
  unfold robustFollowLength at hω
  split at hω
  · rename_i h
    let u := Nat.find h
    have hc := Nat.find_spec h
    have hfst (v : ℕ) (hv : v < u) :
        ¬ robustCrossed T ζ (fun s => run.q s ω) (fun s => run.I s ω)
          (fun s => run.y s ω (run.I s ω)) (v + 1) := by
      intro hv'
      exact Nat.find_min h hv ⟨hv.trans hc.1, hv'⟩
    have hnu : u + 1 = n := hω
    have hut : u < n + t := by omega
    have he := robustPolicy_eq_restart (T := T) ζ (fun v => run.q v ω)
      (fun v => run.J v ω) (fun v => run.I v ω) (fun v => run.y v ω (run.I v ω))
      hut hc.2 hfst
    rw [hnu, Nat.add_sub_cancel_left] at he
    exact he
  · omega

end CalibeatBandit.Supplement.QProtocolRun

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement.QProtocolRun

open MeasureTheory Set
open scoped ENNReal

variable {K T : ℕ} {ζ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} (run : QProtocolRun K T P (robustPolicy K T ζ))

private theorem followLength_pick (f : ℕ → Ω → ℝ) :
    (fun ω => f (run.robustFollowLength ω) ω) =
      (fun ω => ∑ n ∈ Finset.range (T + 1),
        ({v | run.robustFollowLength v = n} : Set Ω).indicator (f n) ω) := by
  classical
  funext ω
  rw [Finset.sum_eq_single (run.robustFollowLength ω)]
  · simp
  · intro n _ hn
    simp [Ne.symm hn]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.lt_succ_of_le (run.robustFollowLength_le ω)))).elim

theorem integrable_robustFollowLength_apply (f : ℕ → Ω → ℝ)
    (hf : ∀ n ≤ T, Integrable (f n) P) :
    Integrable (fun ω => f (run.robustFollowLength ω) ω) P := by
  classical
  rw [run.followLength_pick f]
  apply integrable_finsetSum
  intro n hn
  have hn' : n ≤ T := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  exact (hf n hn').indicator (run.info_le n hn' _ (run.measurableSet_robustFollowLength_eq hn'))

theorem integral_robustFollowLength_apply (f : ℕ → Ω → ℝ)
    (hf : ∀ n ≤ T, Integrable (f n) P) :
    (∫ ω, f (run.robustFollowLength ω) ω ∂P) =
      ∑ n ∈ Finset.range (T + 1), ∫ ω in {v | run.robustFollowLength v = n}, f n ω ∂P := by
  classical
  rw [run.followLength_pick f, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    have hn' : n ≤ T := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    exact integral_indicator (run.info_le n hn' _ (run.measurableSet_robustFollowLength_eq hn'))
  · intro n hn
    have hn' : n ≤ T := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    exact (hf n hn').indicator (run.info_le n hn' _ (run.measurableSet_robustFollowLength_eq hn'))

noncomputable def robustPrefixSwapRegret (ω : Ω) : ℝ :=
  swapRegret (run.robustFollowLength ω) (fun t => run.y t ω) (fun t => run.I t ω)

noncomputable def robustPrefixRewardLoss (ω : Ω) : ℝ :=
  rewardLoss (run.robustFollowLength ω) (fun t => run.y t ω)
    (fun t => run.J t ω) (fun t => run.I t ω)

noncomputable def robustSuffixSwapRegret (ω : Ω) : ℝ :=
  let n := run.robustFollowLength ω
  swapRegret (T - n) (fun t => run.y (n + t) ω) (fun t => run.I (n + t) ω)

noncomputable def robustSuffixRewardLoss (ω : Ω) : ℝ :=
  let n := run.robustFollowLength ω
  rewardLoss (T - n) (fun t => run.y (n + t) ω)
    (fun t => run.J (n + t) ω) (fun t => run.I (n + t) ω)

variable [IsProbabilityMeasure P]

theorem integrable_robustPrefixSwapRegret : Integrable run.robustPrefixSwapRegret P :=
  run.integrable_robustFollowLength_apply
    (fun n ω => swapRegret n (fun t => run.y t ω) (fun t => run.I t ω)) fun n hn =>
    by simpa only [zero_add] using run.integrable_swapRegret_segment 0 n (by simpa using hn)

theorem integrable_robustPrefixRewardLoss : Integrable run.robustPrefixRewardLoss P :=
  run.integrable_robustFollowLength_apply
    (fun n ω => rewardLoss n (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω)) fun n hn =>
    by simpa only [zero_add] using run.integrable_rewardLoss_segment 0 n (by simpa using hn)

theorem integrable_robustSuffixSwapRegret : Integrable run.robustSuffixSwapRegret P :=
  run.integrable_robustFollowLength_apply
    (fun n ω => swapRegret (T - n) (fun t => run.y (n + t) ω) (fun t => run.I (n + t) ω)) fun n hn =>
    run.integrable_swapRegret_segment n (T - n) (by omega)

theorem integrable_robustSuffixRewardLoss : Integrable run.robustSuffixRewardLoss P :=
  run.integrable_robustFollowLength_apply (fun n ω => rewardLoss (T - n)
    (fun t => run.y (n + t) ω) (fun t => run.J (n + t) ω) (fun t => run.I (n + t) ω)) fun n hn =>
    run.integrable_rewardLoss_segment n (T - n) (by omega)

theorem robustRegret_split :
    ((∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P) ≤
      (∫ ω, run.robustPrefixSwapRegret ω ∂P) + (∫ ω, run.robustSuffixSwapRegret ω ∂P)) ∧
    ((∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P) ≤
      (∫ ω, run.robustPrefixRewardLoss ω ∂P) + (∫ ω, run.robustSuffixRewardLoss ω ∂P)) := by
  constructor
  · rw [← integral_add run.integrable_robustPrefixSwapRegret run.integrable_robustSuffixSwapRegret]
    apply integral_mono
    · simpa only [zero_add] using run.integrable_swapRegret_segment 0 T (by simp)
    · exact run.integrable_robustPrefixSwapRegret.add run.integrable_robustSuffixSwapRegret
    · intro ω
      let n := run.robustFollowLength ω
      have hn : n ≤ T := run.robustFollowLength_le ω
      have h := swapRegret_split_le (n := n) (m := T - n)
        (fun t => run.y t ω) (fun t => run.I t ω)
      rwa [show n + (T - n) = T by omega] at h
  · rw [← integral_add run.integrable_robustPrefixRewardLoss run.integrable_robustSuffixRewardLoss]
    apply integral_mono
    · simpa only [zero_add] using run.integrable_rewardLoss_segment 0 T (by simp)
    · exact run.integrable_robustPrefixRewardLoss.add run.integrable_robustSuffixRewardLoss
    · intro ω
      let n := run.robustFollowLength ω
      have hn : n ≤ T := run.robustFollowLength_le ω
      have h := rewardLoss_split_le (n := n) (m := T - n)
        (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω)
      rwa [show n + (T - n) = T by omega] at h

private theorem restart_setIntegral_le {s : Set Ω} (hs : P s ≠ 0) {f : Ω → ℝ} {B : ℝ}
    (h : (∫ ω, f ω ∂eventProbability P s) ≤ B) :
    (∫ ω in s, f ω ∂P) ≤ B * P.real s := by
  have heq : P s • eventProbability P s = P.restrict s := by
    rw [eventProbability, smul_smul, ENNReal.mul_inv_cancel hs (measure_ne_top P s), one_smul]
  rw [← heq, integral_smul_measure, smul_eq_mul, measureReal_def, mul_comm B]
  exact mul_le_mul_of_nonneg_left h ENNReal.toReal_nonneg

private theorem robustSuffix_integrals_on_length_le (hK : 0 < K)
    (hη : 0 < etaStar K T) (hμ : 0 < muStar K T) (hμ' : muStar K T ≤ 1 / 2)
    {n : ℕ} (hn : n ≤ T) :
    let s := {ω | run.robustFollowLength ω = n}
    let B := rT K T (etaStar K T) (muStar K T) + Real.sqrt (2 * T * K * Real.log K)
    ((∫ ω in s, swapRegret (T - n) (fun t => run.y (n + t) ω) (fun t => run.I (n + t) ω) ∂P) ≤
      B * P.real s) ∧
    ((∫ ω in s, rewardLoss (T - n) (fun t => run.y (n + t) ω)
      (fun t => run.J (n + t) ω) (fun t => run.I (n + t) ω) ∂P) ≤ B * P.real s) := by
  intro s B
  by_cases hs₀ : P s = 0
  · simp [Measure.restrict_eq_zero.mpr hs₀, measureReal_def, hs₀]
  have hs : MeasurableSet[run.info n] s := run.measurableSet_robustFollowLength_eq hn
  let : IsProbabilityMeasure (eventProbability P s) := eventProbability_isProbabilityMeasure hs₀
  let restart := run.restartOn n hn s hs hs₀ (calibeatPolicy K (etaStar K T) (muStar K T))
    (fun t ht _ hω => run.played_eq_restart_of_length ht hω)
  have hb := finite_horizon_bounds K (T - n) (etaStar K T) (muStar K T) hK hη hμ hμ'
    (by unfold muStar; rfl) (eventProbability P s) restart
  have hsuf : (T - n : ℕ) ≤ T := Nat.sub_le ..
  have hrt : rT K (T - n) (etaStar K T) (muStar K T) ≤ rT K T (etaStar K T) (muStar K T) := by
    have hden : 0 ≤ 1 - muStar K T := by linarith
    unfold rT
    gcongr
  have hlog : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have hsqrt : Real.sqrt (2 * ↑(T - n) * K * Real.log K) ≤ Real.sqrt (2 * T * K * Real.log K) := by
    apply Real.sqrt_le_sqrt
    gcongr
  exact ⟨restart_setIntegral_le hs₀ (hb.1.trans (add_le_add hrt hsqrt)),
    restart_setIntegral_le hs₀ (hb.2.trans (hrt.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))))⟩

/-- The expected regret after restarting is bounded by the full-horizon
calibeating bound. Each first-crossing event gets its own conditional run. -/
theorem robust_restart_regret (hK : 0 < K)
    (hη : 0 < etaStar K T) (hμ : 0 < muStar K T) (hμ' : muStar K T ≤ 1 / 2) :
    let B := rT K T (etaStar K T) (muStar K T) + Real.sqrt (2 * T * K * Real.log K)
    ((∫ ω, run.robustSuffixSwapRegret ω ∂P) ≤ B) ∧
      ((∫ ω, run.robustSuffixRewardLoss ω ∂P) ≤ B) := by
  intro B
  let E (n : ℕ) : Set Ω := {ω | run.robustFollowLength ω = n}
  have hmass : (∑ n ∈ Finset.range (T + 1), P.real (E n)) = 1 := by
    have h := (run.integral_robustFollowLength_apply (fun _ _ => (1 : ℝ))
      (fun _ _ => integrable_const _)).symm
    simpa only [E, integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one,
      probReal_univ] using h
  have hsum : (∑ n ∈ Finset.range (T + 1), B * P.real (E n)) = B := by
    rw [← Finset.mul_sum, hmass, mul_one]
  constructor
  · unfold robustSuffixSwapRegret
    rw [run.integral_robustFollowLength_apply (fun n ω => swapRegret (T - n)
      (fun t => run.y (n + t) ω) (fun t => run.I (n + t) ω))
      (fun n hn => run.integrable_swapRegret_segment n (T - n) (by omega)), ← hsum]
    exact Finset.sum_le_sum fun n hn => (run.robustSuffix_integrals_on_length_le hK hη hμ hμ'
      (Nat.le_of_lt_succ (Finset.mem_range.mp hn))).1
  · unfold robustSuffixRewardLoss
    rw [run.integral_robustFollowLength_apply (fun n ω => rewardLoss (T - n)
      (fun t => run.y (n + t) ω) (fun t => run.J (n + t) ω) (fun t => run.I (n + t) ω))
      (fun n hn => run.integrable_rewardLoss_segment n (T - n) (by omega)), ← hsum]
    exact Finset.sum_le_sum fun n hn => (run.robustSuffix_integrals_on_length_le hK hη hμ hμ'
      (Nat.le_of_lt_succ (Finset.mem_range.mp hn))).2

end CalibeatBandit.Supplement.QProtocolRun

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

private theorem factorial_ge_geometric (n : ℕ) : 2 * 3 ^ n ≤ (n + 2).factorial := by
  induction n with
  | zero => decide
  | succ n ih =>
    change 2 * 3 ^ (n + 1) ≤ (n + 2 + 1).factorial
    rw [pow_succ, Nat.factorial_succ, ← mul_assoc]
    calc
      2 * 3 ^ n * 3 ≤ (n + 2).factorial * 3 := Nat.mul_le_mul_right _ ih
      _ ≤ (n + 2 + 1) * (n + 2).factorial := by
        rw [mul_comm ((n + 2).factorial)]
        exact Nat.mul_le_mul_right _ (by omega)

private theorem exp_le_bernstein {x a : ℝ} (hx : |x| ≤ a) (ha : a < 3) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - a / 3)) := by
  let f (n : ℕ) := x ^ n / (n.factorial : ℝ)
  have ha₀ : 0 ≤ a := (abs_nonneg x).trans hx
  have h₁ : HasSum f (Real.exp x) := by
    simpa [f, Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x
  have h₂ := hasSum_geometric_of_lt_one (show 0 ≤ a / 3 by positivity) (show a / 3 < 1 by linarith)
  have hsplit : Real.exp x = 1 + x + ∑' n, f (n + 2) := by
    rw [← h₁.tsum_eq, ← h₁.summable.sum_add_tsum_nat_add 2]
    simp [f, Finset.sum_range_succ]
  rw [hsplit]
  apply add_le_add_right
  have htail := (summable_nat_add_iff 2).2 h₁.summable
  calc
    (∑' n, f (n + 2)) ≤ ∑' n, (x ^ 2 / 2) * (a / 3) ^ n := by
      apply htail.tsum_le_tsum _ (h₂.mul_left (x ^ 2 / 2)).summable
      intro n
      have hf := (show (2 : ℝ) * (3 : ℝ) ^ n ≤ ((n + 2).factorial : ℝ) by
        exact_mod_cast factorial_ge_geometric n)
      have h0 : (0 : ℝ) < ((n + 2).factorial : ℝ) := by positivity
      have heq : (x ^ 2 / 2) * (a / 3) ^ n = (x ^ 2 * a ^ n) / (2 * 3 ^ n) := by
        rw [div_pow, div_mul_div_comm]
      rw [heq]
      exact (div_le_div_of_nonneg_right (show x ^ (n + 2) ≤ x ^ 2 * a ^ n by
        rw [pow_add, mul_comm]
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) hx _)) (sq_nonneg x)) h0.le).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hf)
    _ = x ^ 2 / (2 * (1 - a / 3)) := by
      rw [(h₂.mul_left (x ^ 2 / 2)).tsum_eq]
      have hn : 1 - a / 3 ≠ 0 := by linarith
      field_simp

private theorem condExp_bernstein_le_one {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : @Measurable Ω ℝ mΩ _ X) {b v η : ℝ}
    (hb : ∀ ω, |X ω| ≤ b) (hv : 0 ≤ v)
    (hη : 0 ≤ η) (hηb : η * b < 3)
    (hc : condExp m P X =ᵐ[P] 0)
    (hvX : condExp m P (fun ω => X ω ^ 2) ≤ᵐ[P] fun _ => v) :
    let α := η ^ 2 / (2 * (1 - η * b / 3))
    condExp m P (fun ω => Real.exp (η * X ω - α * v)) ≤ᵐ[P] fun _ => 1 := by
  intro α
  have hα : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg (sq_nonneg _) (by linarith)
  let k := Real.exp (-(α * v))
  let F : Ω → ℝ := fun ω => k * (1 + η * X ω + α * X ω ^ 2)
  have hi : Integrable X P := @integrable_of_abs_bound Ω mΩ P _ X hX b hb
  have hi2 : Integrable (fun ω => X ω ^ 2) P := by
    refine @integrable_of_abs_bound Ω mΩ P _ (fun ω => X ω ^ 2) (hX.pow_const (2 : ℕ)) (b ^ 2) ?_
    intro ω
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb ω) _
  have hA : Integrable (fun ω => 1 + η * X ω) P :=
    (integrable_const _).add (hi.const_mul η)
  have hB : Integrable (fun ω => α * X ω ^ 2) P := hi2.const_mul α
  have hF : Integrable F P := (hA.add hB).const_mul k
  have hE : Integrable (fun ω => Real.exp (η * X ω - α * v)) P := by
    have hf : @Measurable Ω ℝ mΩ _ (fun ω => Real.exp (η * X ω - α * v)) :=
      Real.continuous_exp.measurable.comp ((hX.const_mul η).sub measurable_const)
    refine @integrable_of_abs_bound Ω mΩ P _ _ hf (Real.exp (η * b)) fun ω => ?_
    rw [abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_exp.mpr
    exact (sub_le_self _ (mul_nonneg hα hv)).trans
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb ω)) hη)
  have he (ω : Ω) : Real.exp (η * X ω - α * v) ≤ F ω := by
    rw [sub_eq_add_neg, Real.exp_add, mul_comm]
    have h := exp_le_bernstein (x := η * X ω) (a := η * b)
      (by rw [abs_mul, abs_of_nonneg hη]; exact mul_le_mul_of_nonneg_left (hb ω) hη) hηb
    have heq : (η * X ω) ^ 2 / (2 * (1 - η * b / 3)) = α * X ω ^ 2 := by
      dsimp [α]
      ring
    rw [heq] at h
    exact mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
  have hF' :
      condExp m P F =ᵐ[P] fun ω =>
        k * (1 + η * condExp m P X ω + α * condExp m P (fun ω => X ω ^ 2) ω) := by
    let U : Ω → ℝ := fun _ => 1
    let Y : Ω → ℝ := η • X
    let Z : Ω → ℝ := α • (fun ω => X ω ^ 2)
    have hiU : Integrable U P := integrable_const _
    have hiY : Integrable Y P := hi.smul η
    have hiZ : Integrable Z P := hi2.smul α
    have hU : condExp m P U = U := condExp_const hm (1 : ℝ)
    have hY : condExp m P Y =ᵐ[P] η • condExp m P X := condExp_smul ..
    have hZ : condExp m P Z =ᵐ[P] α • condExp m P (fun ω => X ω ^ 2) := condExp_smul ..
    have heq : F = k • (U + Y + Z) := rfl
    rw [heq]
    filter_upwards [condExp_smul (μ := P) k (U + Y + Z) m, condExp_add (hiU.add hiY) hiZ m,
      condExp_add hiU hiY m, hY, hZ] with ω h₁ h₂ h₃ h₄ h₅
    rw [h₁, Pi.smul_apply, h₂, Pi.add_apply, h₃, Pi.add_apply, hU, h₄, h₅]
    rfl
  filter_upwards [condExp_mono (m := m) hE hF (ae_of_all _ he), hF', hc, hvX] with ω h₁ h₂ h₃ h₄
  apply h₁.trans
  rw [h₂, h₃]
  change k * (1 + η * 0 + α * condExp m P (fun ω => X ω ^ 2) ω) ≤ 1
  calc
    _ ≤ k * (1 + α * v) := by
      rw [mul_zero, add_zero]
      gcongr
    _ ≤ k * Real.exp (α * v) :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _ |>.trans_eq' (add_comm _ _))
        (Real.exp_nonneg _)
    _ = 1 := by dsimp [k]; rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- Bernstein's upper tail for martingale differences with a uniform bound on
their absolute size and on their conditional second moments. -/
theorem bernstein_upper_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (info : ℕ → MeasurableSpace Ω) {s : ℕ} (hs : 0 < s)
    (hinfo : ∀ a n, a ≤ n → n ≤ s → info a ≤ info n)
    (hinfo_le : ∀ n ≤ s, info n ≤ mΩ)
    (d : ℕ → Ω → ℝ) {b v L : ℝ} (hb₀ : 0 ≤ b) (hv : 0 < v) (hL : 0 < L)
    (hm : ∀ t < s, Measurable[info (t + 1)] (d t))
    (hb : ∀ t < s, ∀ ω, |d t ω| ≤ b)
    (hc : ∀ t < s, condExp (info t) P (d t) =ᵐ[P] 0)
    (hvX : ∀ t < s, condExp (info t) P (fun ω => d t ω ^ 2) ≤ᵐ[P] fun _ => v) :
    P {ω | Real.sqrt (2 * s * v * L) + b * L / 3 < ∑ t ∈ Finset.range s, d t ω}
      ≤ ENNReal.ofReal (Real.exp (-L)) := by
  let V : ℝ := s * v
  let R : ℝ := Real.sqrt (2 * V * L)
  let c := b / 3
  let D := V + c * R
  let η := R / D
  let α := η ^ 2 / (2 * (1 - η * b / 3))
  let A := R + c * L
  have hV : 0 < V := by exact mul_pos (by exact_mod_cast hs) hv
  have hR : 0 < R := Real.sqrt_pos.2 (by positivity)
  have hc₀ : 0 ≤ c := by positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hη : 0 ≤ η := by positivity
  have hnorm : 1 - η * b / 3 = V / D := by
    dsimp [η]
    field_simp
    dsimp [D, c]
    ring
  have hηb : η * b < 3 := by nlinarith only [hnorm, (div_pos hV hD)]
  have hR2 : R ^ 2 = 2 * V * L := Real.sq_sqrt (by positivity)
  have hα : α = R ^ 2 / (2 * D * V) := by
    dsimp only [α]
    rw [hnorm]
    dsimp only [η]
    field_simp [ne_of_gt hD, ne_of_gt hV]
  have hexp : -η * A + s * (α * v) = -L := by
    rw [show (s : ℝ) * (α * v) = α * V by dsimp [V]; ring]
    calc
      _ = (-(R * A) + R ^ 2 / 2) / D := by
        rw [hα]
        dsimp only [η]
        field_simp [ne_of_gt hD, ne_of_gt hV]
      _ = -(L * D) / D := by
        congr 1
        dsimp only [A, D]
        rw [mul_add, ← pow_two, hR2]
        ring
      _ = -L := by rw [neg_div, mul_div_cancel_right₀ _ hD.ne']
  let S (ω : Ω) : ℝ := ∑ t ∈ Finset.range s, d t ω
  have hmS : Measurable S := by
    apply Finset.measurable_sum
    intro t ht'
    have ht : t < s := Finset.mem_range.mp ht'
    exact (hm t ht).mono (hinfo_le (t + 1) (by omega)) le_rfl
  have hS (ω : Ω) : |S ω| ≤ s * b := by
    calc
      _ ≤ ∑ t ∈ Finset.range s, |d t ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.range s, b := Finset.sum_le_sum fun t ht => hb t (Finset.mem_range.mp ht) ω
      _ = _ := by simp
  have hi : Integrable (fun ω => Real.exp (η * S ω)) P := by
    apply integrable_of_abs_bound (B := Real.exp (η * (s * b)))
      (Real.continuous_exp.measurable.comp (hmS.const_mul _))
    intro ω
    change |Real.exp (η * S ω)| ≤ _
    rw [abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hS ω)) hη)
  have hg (t : ℕ) (ht : t < s) : condExp (info t) P
      (fun ω => Real.exp (η * d t ω - α * v)) ≤ᵐ[P] fun _ => 1 :=
    @condExp_bernstein_le_one Ω mΩ P _ (info t) (hinfo_le t ht.le) _ ((hm t ht).mono (hinfo_le (t+1) (by omega)) le_rfl) b v η
      (hb t ht) hv.le hη hηb (hc t ht) (hvX t ht)
  have hbound := integral_exp_sum_le_one P info info hinfo hinfo_le
    (fun n hn => hinfo_le n hn.le) (fun _ _ => le_rfl)
    (fun t ω => η * d t ω - α * v) (B := η * b + |α * v|)
    (fun t ht => ((hm t ht).const_mul η).sub measurable_const)
    (fun t ht ω => (abs_sub _ _).trans (by
      rw [abs_mul, abs_of_nonneg hη]
      gcongr
      exact hb t ht ω)) hg
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, Real.exp_sub] at hbound
  rw [integral_div] at hbound
  have hmgf : mgf S P η ≤ Real.exp (s * (α * v)) := by
    unfold mgf
    rw [show (s : ℝ) * (α * v) = α * (s * v) by ring]
    simpa only [one_mul] using (div_le_iff₀ (Real.exp_pos _)).mp hbound
  have hre : P.real {ω | A < S ω} ≤ Real.exp (-L) := by
    calc
      _ ≤ P.real {ω | A ≤ S ω} :=
        measureReal_mono (μ := P) (s₁ := {ω | A < S ω}) (s₂ := {ω | A ≤ S ω}) (fun ω h => (show A < S ω from h).le) (measure_ne_top _ _)
      _ ≤ Real.exp (-η * A) * mgf S P η :=
        measure_ge_le_exp_mul_mgf A hη hi
      _ ≤ Real.exp (-η * A) * Real.exp (s * (α * v)) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, hexp]
  have hR' : R = Real.sqrt (2 * s * v * L) := by
    dsimp [R, V]
    congr 1
    ring
  have hA : A = Real.sqrt (2 * s * v * L) + b * L / 3 := by
    change R + c * L = _
    rw [hR']
    dsimp [c]
    ring
  rw [← hA, ← ENNReal.ofReal_toReal (measure_ne_top P {ω | A < S ω})]
  exact ENNReal.ofReal_le_ofReal hre

/-- The two-sided form of the same concentration bound. -/
theorem bernstein_abs_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (info : ℕ → MeasurableSpace Ω) {s : ℕ} (hs : 0 < s)
    (hinfo : ∀ a n, a ≤ n → n ≤ s → info a ≤ info n)
    (hinfo_le : ∀ n ≤ s, info n ≤ mΩ)
    (d : ℕ → Ω → ℝ) {b v L : ℝ} (hb₀ : 0 ≤ b) (hv : 0 < v) (hL : 0 < L)
    (hm : ∀ t < s, Measurable[info (t + 1)] (d t))
    (hb : ∀ t < s, ∀ ω, |d t ω| ≤ b)
    (hc : ∀ t < s, condExp (info t) P (d t) =ᵐ[P] 0)
    (hvX : ∀ t < s, condExp (info t) P (fun ω => d t ω ^ 2) ≤ᵐ[P] fun _ => v) :
    P {ω | Real.sqrt (2 * s * v * L) + b * L / 3 < |∑ t ∈ Finset.range s, d t ω|}
      ≤ 2 * ENNReal.ofReal (Real.exp (-L)) := by
  let A := Real.sqrt (2 * s * v * L) + b * L / 3
  let high : Set Ω := {ω | A < ∑ t ∈ Finset.range s, d t ω}
  let low : Set Ω := {ω | A < ∑ t ∈ Finset.range s, -d t ω}
  have hhi : P high ≤ ENNReal.ofReal (Real.exp (-L)) :=
    bernstein_upper_tail P info hs hinfo hinfo_le d hb₀ hv hL hm hb hc hvX
  have hlo : P low ≤ ENNReal.ofReal (Real.exp (-L)) :=
    bernstein_upper_tail P info hs hinfo hinfo_le (fun t ω => -d t ω) hb₀ hv hL
      (fun t ht => (hm t ht).neg) (fun t ht ω => by simpa using hb t ht ω)
      (fun t ht => (condExp_neg ..).trans (by simpa using (hc t ht).neg))
      (fun t ht => by simpa only [neg_sq] using hvX t ht)
  calc
    _ ≤ P (high ∪ low) := by
      apply measure_mono
      intro ω hω
      change A < |∑ t ∈ Finset.range s, d t ω| at hω
      rw [abs_eq_max_neg, lt_max_iff] at hω
      simpa [high, low, Finset.sum_neg_distrib] using hω
    _ ≤ P high + P low := measure_union_le _ _
    _ ≤ _ := by rw [two_mul]; exact add_le_add hhi hlo

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal

private theorem condExp_select_on {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {F : Set Ω} (hF : @MeasurableSet Ω mΩ F) {I : Ω → ι} (hI : @Measurable Ω ι mΩ _ I)
    {p : Ω → ι → ℝ}
    (hlaw : ∀ j, condExp m P ((F ∩ I ⁻¹' {j}).indicator (fun _ => (1 : ℝ))) =ᵐ[P]
      F.indicator (fun ω => p ω j))
    (g : ι → Ω → ℝ) (hg : ∀ j, Measurable[m] (g j))
    (B : ℝ) (hb : ∀ j ω, |g j ω| ≤ B) :
    condExp m P (F.indicator (fun ω => g (I ω) ω)) =ᵐ[P]
      F.indicator (fun ω => ∑ j, p ω j * g j ω) := by
  classical
  let ind (j : ι) : Ω → ℝ := (F ∩ I ⁻¹' {j}).indicator (fun _ => 1)
  have hindMeas (j : ι) : @Measurable Ω ℝ mΩ _ (ind j) :=
    measurable_const.indicator (hF.inter (hI (measurableSet_singleton _)))
  have hindBound (j : ι) (ω : Ω) : |ind j ω| ≤ 1 := by
    by_cases h : ω ∈ F ∩ I ⁻¹' {j} <;> simp [ind, h]
  have hintegrable (j : ι) : Integrable (ind j) P :=
    @integrable_of_abs_bound Ω mΩ P _ (ind j) (hindMeas j) 1 (hindBound j)
  have hprod (j : ι) : Integrable (g j * ind j) P := by
    refine @integrable_of_abs_bound Ω mΩ P _ (g j * ind j)
      (((hg j).mono hm le_rfl).mul (hindMeas j)) B fun ω => ?_
    rw [Pi.mul_apply, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hindBound j ω)).trans (hb j ω)
  have heq : F.indicator (fun ω => g (I ω) ω) = ∑ j, g j * ind j := by
    funext ω
    by_cases h : ω ∈ F <;>
      simp [Finset.sum_apply, ind, Set.indicator_apply, h, mul_ite]
  rw [heq]
  refine (condExp_finsetSum (fun j _ => hprod j) m).trans ?_
  have ha (j : ι) : condExp m P (g j * ind j) =ᵐ[P]
      fun ω => g j ω * F.indicator (fun ξ => p ξ j) ω := by
    refine (condExp_mul_of_stronglyMeasurable_left (hg j).stronglyMeasurable
      (hprod j) (hintegrable j)).trans ?_
    filter_upwards [hlaw j] with ω h
    change g j ω * condExp m P (ind j) ω = _
    rw [h]
  filter_upwards [ae_all_iff.mpr ha] with ω h
  rw [Finset.sum_apply]
  by_cases hω : ω ∈ F
  · rw [Set.indicator_of_mem hω]
    exact Finset.sum_congr rfl fun j _ => by rw [h j, Set.indicator_of_mem hω, mul_comm]
  · rw [Set.indicator_of_notMem hω]
    exact Finset.sum_eq_zero fun j _ => by rw [h j, Set.indicator_of_notMem hω, mul_zero]

private theorem sum_centered_square_le {ι : Type*} [Fintype ι] (p f : ι → ℝ)
    (hp : ∑ i, p i = 1) :
    let c := ∑ i, p i * f i
    ∑ i, p i * (f i - c) ^ 2 ≤ ∑ i, p i * f i ^ 2 := by
  intro c
  have heq (i : ι) : p i * (f i - c) ^ 2 =
      p i * f i ^ 2 - 2 * c * (p i * f i) + p i * c ^ 2 := by ring
  simp_rw [heq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hp]
  change (∑ i, p i * f i ^ 2) - 2 * c * c + 1 * c ^ 2 ≤ _
  nlinarith only [sq_nonneg c]

private theorem condExp_centered_selected_on {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {F : Set Ω} (hF : @MeasurableSet Ω mΩ F) {I : Ω → ι} (hI : @Measurable Ω ι mΩ _ I)
    {p : Ω → ι → ℝ}
    (hlaw : ∀ j, condExp m P ((F ∩ I ⁻¹' {j}).indicator (fun _ => (1 : ℝ))) =ᵐ[P]
      F.indicator (fun ω => p ω j))
    (g : ι → Ω → ℝ) {c : Ω → ℝ} (hg : ∀ j, Measurable[m] (g j))
    (hc : Measurable[m] c)
    (B v : ℝ) (hb : ∀ j ω, |g j ω - c ω| ≤ B)
    (hpsum : ∀ ω, ∑ j, p ω j = 1)
    (hmean : ∀ ω, ∑ j, p ω j * g j ω = c ω)
    (hsecond : ∀ ω, ∑ j, p ω j * g j ω ^ 2 ≤ v) (hv : 0 ≤ v) :
    let d := F.indicator (fun ω => g (I ω) ω - c ω)
    (condExp m P d =ᵐ[P] 0) ∧
      (condExp m P (fun ω => d ω ^ 2) ≤ᵐ[P] fun _ => v) := by
  intro d
  have h₁ := @condExp_select_on Ω ι mΩ _ _ _ P _ m hm F hF I hI p hlaw (fun j ω => g j ω - c ω)
    (fun j => (hg j).sub hc) B hb
  have h₂ := @condExp_select_on Ω ι mΩ _ _ _ P _ m hm F hF I hI p hlaw (fun j ω => (g j ω - c ω) ^ 2)
    (fun j => ((hg j).sub hc).pow_const _) (B ^ 2) (fun j ω => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb j ω) _)
  constructor
  · filter_upwards [h₁] with ω he
    rw [he]
    change F.indicator _ ω = 0
    by_cases hω : ω ∈ F
    · rw [Set.indicator_of_mem hω]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hpsum, hmean, one_mul, sub_self]
    · exact Set.indicator_of_notMem hω _
  · have heq : (fun ω => d ω ^ 2) = F.indicator (fun ω => (g (I ω) ω - c ω) ^ 2) := by
      funext ω
      by_cases hω : ω ∈ F <;> simp [d, hω]
    rw [heq]
    filter_upwards [h₂] with ω he
    rw [he]
    by_cases hω : ω ∈ F
    · rw [Set.indicator_of_mem hω]
      exact (by simpa only [hmean] using sum_centered_square_le (p ω) (fun j => g j ω) (hpsum ω)
        : (∑ j, p ω j * (g j ω - c ω) ^ 2) ≤ ∑ j, p ω j * g j ω ^ 2).trans (hsecond ω)
    · rwa [Set.indicator_of_notMem hω]
 
private def pushMass {K : ℕ} (σ : Fin K → Fin K) (q : Fin K → ℝ) (j : Fin K) : ℝ :=
  ∑ i, if σ i = j then q i else 0

private theorem sum_pushMass_mul {K : ℕ} (σ : Fin K → Fin K) (q y : Fin K → ℝ) :
    ∑ j, pushMass σ q j * y j = ∑ i, q i * y (σ i) := by
  classical
  unfold pushMass
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

private theorem pushMass_prob {K : ℕ} (σ : Fin K → Fin K) {q : Fin K → ℝ}
    (hq : IsProbVec q) : IsProbVec (pushMass σ q) := by
  refine ⟨fun j => Finset.sum_nonneg fun i _ => ?_, ?_⟩
  · split
    · exact hq.1 _
    · exact le_rfl
  · simpa only [mul_one] using (sum_pushMass_mul σ q (fun _ => 1)).trans (by simpa using hq.2)

private theorem prob_le_one {K : ℕ} {q : Fin K → ℝ} (hq : IsProbVec q) (j : Fin K) :
    q j ≤ 1 :=
  (Finset.single_le_sum (fun i _ => hq.1 i) (Finset.mem_univ j)).trans_eq hq.2

private theorem followMix_prob {K : ℕ} (hK : 0 < K) {ε : ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) {q : Fin K → ℝ} (hq : IsProbVec q) :
    IsProbVec (followMix ε q) := by
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  refine ⟨fun j => add_nonneg (mul_nonneg (sub_nonneg.mpr hε₁) (hq.1 j))
    (div_nonneg hε₀ (by positivity)), ?_⟩
  unfold followMix
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hq.2, mul_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

def robustSwapStep {K : ℕ} (σ : Fin K → Fin K) (q y : Fin K → ℝ) : ℝ :=
  ∑ i, q i * (y (σ i) - y i)

private theorem robustSwapStep_eq {K : ℕ} (σ : Fin K → Fin K) (q y : Fin K → ℝ) :
    robustSwapStep σ q y = ∑ j, (pushMass σ q j - q j) * y j := by
  unfold robustSwapStep
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, sum_pushMass_mul]

private theorem robustSwapStep_abs_le {K : ℕ} (σ : Fin K → Fin K) {q y : Fin K → ℝ}
    (hq : IsProbVec q) (hy : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1) :
    |robustSwapStep σ q y| ≤ 1 := by
  calc
    _ ≤ ∑ j, |q j * (y (σ j) - y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, q j := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hq.1 j)]
      have hp := hy (σ j)
      have hq' := hy j
      exact mul_le_of_le_one_right (hq.1 j) (abs_le.mpr ⟨by linarith [hp.1, hq'.2],
        by linarith [hp.2, hq'.1]⟩)
    _ = 1 := hq.2

private def followedSwapScore {K : ℕ} (σ : Fin K → Fin K) (ε : ℝ) (q y : Fin K → ℝ)
    (j : Fin K) : ℝ :=
  (pushMass σ q j - q j) * y j / followMix ε q j

private theorem followMix_ge_uniform {K : ℕ} {ε : ℝ} (hε : ε ≤ 1)
    {q : Fin K → ℝ} (hq : IsProbVec q) (j : Fin K) :
    ε / K ≤ followMix ε q j := by
  unfold followMix
  linarith only [mul_nonneg (sub_nonneg.mpr hε) (hq.1 j)]

private theorem followedSwapScore_abs_le {K : ℕ} (hK : 0 < K)
    (σ : Fin K → Fin K) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) {q y : Fin K → ℝ}
    (hq : IsProbVec q) (hy : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1) (j : Fin K) :
    |followedSwapScore σ ε q y j| ≤ K / ε := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hp := followMix_ge_uniform hε₁ hq j
  have hpos := (div_pos hε₀ hk).trans_le hp
  have hQ := pushMass_prob σ hq
  have hd : |pushMass σ q j - q j| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hQ.1 j, prob_le_one hq j],
      by linarith [prob_le_one hQ j, hq.1 j]⟩
  unfold followedSwapScore
  rw [abs_div, abs_of_pos hpos, abs_mul, abs_of_nonneg (hy j).1]
  calc
    _ ≤ 1 / followMix ε q j := by gcongr; exact (mul_le_of_le_one_right (abs_nonneg _) (hy j).2).trans hd
    _ ≤ 1 / (ε / K) := one_div_le_one_div_of_le (div_pos hε₀ hk) hp
    _ = _ := one_div_div _ _

private theorem followedSwapScore_mean {K : ℕ} (hK : 0 < K)
    (σ : Fin K → Fin K) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) {q y : Fin K → ℝ}
    (hq : IsProbVec q) :
    ∑ j, followMix ε q j * followedSwapScore σ ε q y j = robustSwapStep σ q y := by
  rw [robustSwapStep_eq]
  apply Finset.sum_congr rfl
  intro j _
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hp := (div_pos hε₀ hk).trans_le (followMix_ge_uniform hε₁ hq j)
  unfold followedSwapScore
  field_simp

private theorem followedSwapScore_second {K : ℕ} (hK : 0 < K)
    (σ : Fin K → Fin K) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1 / 2) {q y : Fin K → ℝ}
    (hq : IsProbVec q) (hy : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1) :
    ∑ j, followMix ε q j * followedSwapScore σ ε q y j ^ 2 ≤ K / ε + 2 := by
  let Q := pushMass σ q
  let p := followMix ε q
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hQ := pushMass_prob σ hq
  have hε₂ : ε ≤ 1 := by linarith
  have hp (j : Fin K) := followMix_ge_uniform hε₂ hq j
  have hp_pos (j : Fin K) := (div_pos hε₀ hk).trans_le (hp j)
  have hQpart (j : Fin K) : Q j ^ 2 / p j ≤ (K / ε) * Q j := by
    calc
      _ ≤ Q j ^ 2 / (ε / K) := div_le_div_of_nonneg_left (sq_nonneg _) (div_pos hε₀ hk) (hp j)
      _ = K / ε * Q j ^ 2 := by simp only [div_div_eq_mul_div]; ring
      _ ≤ _ := by
        gcongr
        exact pow_le_of_le_one (hQ.1 j) (prob_le_one hQ j) (by norm_num)
  have hqpart (j : Fin K) : q j ^ 2 / p j ≤ 2 * q j := by
    apply (div_le_iff₀ (hp_pos j)).2
    have hp' : (1 - ε) * q j ≤ p j := le_add_of_nonneg_right (div_nonneg hε₀.le hk.le)
    have hh : q j ≤ (2 * (1 - ε)) * q j :=
      le_mul_of_one_le_left (hq.1 j) (by linarith)
    have hh' : q j ≤ 2 * p j := hh.trans (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hp' (by norm_num))
    calc
      q j ^ 2 = q j * q j := pow_two _
      _ ≤ q j * (2 * p j) := mul_le_mul_of_nonneg_left hh' (hq.1 j)
      _ = _ := by ring
  calc
    _ = ∑ j, ((Q j - q j) * y j) ^ 2 / p j := by
      apply Finset.sum_congr rfl
      intro j _
      unfold followedSwapScore
      change p j * ((Q j - q j) * y j / p j) ^ 2 = _
      field_simp
    _ ≤ ∑ j, ((K / ε) * Q j + 2 * q j) := by
      apply Finset.sum_le_sum
      intro j _
      refine (show ((Q j - q j) * y j) ^ 2 / p j ≤ Q j ^ 2 / p j + q j ^ 2 / p j from ?_).trans
        (add_le_add (hQpart j) (hqpart j))
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (hp_pos j).le
      rw [mul_pow]
      have hyy : y j ^ 2 ≤ 1 := by
        exact pow_le_one₀ (hy j).1 (hy j).2
      calc
        _ ≤ (Q j - q j) ^ 2 := mul_le_of_le_one_right (sq_nonneg _) hyy
        _ ≤ _ := by nlinarith only [mul_nonneg (hQ.1 j) (hq.1 j)]
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hQ.2, hq.2, mul_one, mul_one]

namespace QProtocolRun

variable {K T : ℕ} {ζ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] (run : QProtocolRun K T P (robustPolicy K T ζ))

def robustEstimatorDifference (σ : Fin K → Fin K) (t : ℕ) : Ω → ℝ :=
  (run.robustFollowing t).indicator (fun ω =>
    followedSwapScore σ (robustEps T ζ) (run.q t ω) (run.y t ω) (run.I t ω) -
      robustSwapStep σ (run.q t ω) (run.y t ω))

def robustRecommendationDifference (σ : Fin K → Fin K) (t : ℕ) : Ω → ℝ :=
  fun ω => run.y t ω (σ (run.J t ω)) - run.y t ω (run.J t ω) -
    robustSwapStep σ (run.q t ω) (run.y t ω)

private theorem robustSwapStep_measurable (σ : Fin K → Fin K) {t : ℕ} (ht : t < T) :
    Measurable[run.info t] (fun ω => robustSwapStep σ (run.q t ω) (run.y t ω)) := by
  have hQm := run.q_measurable t ht
  have hYm := run.y_measurable t ht
  let _ : MeasurableSpace Ω := run.info t
  unfold robustSwapStep
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply j).comp hQm).mul
    (((measurable_pi_apply (σ j)).comp hYm).sub
      ((measurable_pi_apply j).comp hYm))

private theorem followedSwapScore_measurable (σ : Fin K → Fin K) {t : ℕ}
    (ht : t < T) (j : Fin K) :
    Measurable[run.info t] (fun ω =>
      followedSwapScore σ (robustEps T ζ) (run.q t ω) (run.y t ω) j) := by
  let q := run.q t
  let y := run.y t
  have hQm : Measurable[run.info t] q := run.q_measurable t ht
  have hYm : Measurable[run.info t] y := run.y_measurable t ht
  let _ : MeasurableSpace Ω := run.info t
  have mq (i : Fin K) : Measurable (fun ω => q ω i) :=
    (measurable_pi_apply i).comp hQm
  have mp : Measurable (fun ω => pushMass σ (q ω) j) := by
    unfold pushMass
    apply Finset.measurable_sum
    intro i _
    by_cases h : σ i = j <;> simp only [h, if_true, if_false]
    · exact mq i
    · exact measurable_const
  have my : Measurable (fun ω => y ω j) :=
    (measurable_pi_apply j).comp hYm
  unfold followedSwapScore followMix
  exact ((mp.sub (mq j)).mul my).div (((mq j).const_mul _).add measurable_const)

private theorem robustEps_pos_eq {T : ℕ} (hT : 0 < T) (ζ : ℝ) :
    0 < robustEps T ζ ∧ (robustEps T ζ)⁻¹ = (T : ℝ) ^ ζ := by
  rw [robustEps, Real.rpow_neg (by positivity), inv_inv]
  exact ⟨by positivity, rfl⟩

theorem robustEstimatorDifference_bounds (hK : 0 < K) {t : ℕ}
    (ht : t < T) (hε : robustEps T ζ ≤ 1 / 2) (σ : Fin K → Fin K) :
    let d := run.robustEstimatorDifference σ t
    Measurable[run.info (t + 1)] d ∧
      (∀ ω, |d ω| ≤ K * (T : ℝ) ^ ζ + 1) ∧
      (condExp (run.info t) P d =ᵐ[P] 0) ∧
      (condExp (run.info t) P (fun ω => d ω ^ 2) ≤ᵐ[P] fun _ => K * (T : ℝ) ^ ζ + 2) := by
  intro d
  let ε := robustEps T ζ
  let g (j : Fin K) (ω : Ω) := followedSwapScore σ ε (run.q t ω) (run.y t ω) j
  let c (ω : Ω) := robustSwapStep σ (run.q t ω) (run.y t ω)
  have hε₀ : 0 < ε := (robustEps_pos_eq (by omega) ζ).1
  have hε₁ : ε ≤ 1 := by dsimp [ε]; linarith
  have hcast : (K : ℝ) / ε = K * (T : ℝ) ^ ζ := by
    rw [div_eq_mul_inv, (robustEps_pos_eq (by omega) ζ).2]
  have hg : ∀ j, Measurable[run.info t] (g j) := run.followedSwapScore_measurable σ ht
  have hc : Measurable[run.info t] c := run.robustSwapStep_measurable σ ht
  have hq (ω : Ω) : IsProbVec (run.q t ω) :=
    ⟨run.q_nonneg t ht ω, run.q_sum t ht ω⟩
  have hb (j : Fin K) (ω : Ω) : |g j ω - c ω| ≤ K / ε + 1 :=
    (abs_sub _ _).trans (add_le_add
      (followedSwapScore_abs_le hK σ hε₀ hε₁ (hq ω) (run.y_mem t ht ω) j)
      (robustSwapStep_abs_le σ (hq ω) (run.y_mem t ht ω)))
  have hF := run.measurableSet_robustFollowing ht.le
  have hm₂ := run.info_mono t ht
  have hm₀ := run.info_le (t + 1) (by omega)
  have hmeas : Measurable[run.info (t + 1)] d := by
    change Measurable[run.info (t+1)]
      ((run.robustFollowing t).indicator fun ω => g (run.I t ω) ω - c ω)
    have hIm := run.I_measurable t ht
    have hFm := hm₂ _ hF
    let _ : MeasurableSpace Ω := run.info (t+1)
    exact ((measurable_select hIm
      (fun j => (hg j).mono hm₂ le_rfl)).sub (hc.mono hm₂ le_rfl)).indicator hFm
  have hav := condExp_centered_selected_on (run.info_le t ht.le) (run.info_le t ht.le _ hF)
    ((run.I_measurable t ht).mono hm₀ le_rfl)
    (run.condExp_robustFollowing_action ht) g hg hc (K / ε + 1) (K / ε + 2) hb
    (fun ω => (followMix_prob hK hε₀.le hε₁ (hq ω)).2)
    (fun ω => followedSwapScore_mean hK σ hε₀ hε₁ (hq ω))
    (fun ω => followedSwapScore_second hK σ hε₀ hε (hq ω) (run.y_mem t ht ω)) (by positivity)
  refine ⟨hmeas, fun ω => ?_, hav.1, ?_⟩
  · rw [← hcast]
    change |(run.robustFollowing t).indicator (fun ω => g (run.I t ω) ω - c ω) ω| ≤ _
    by_cases h : ω ∈ run.robustFollowing t
    · rw [Set.indicator_of_mem h]
      exact hb _ _
    · rw [Set.indicator_of_notMem h, abs_zero]
      positivity
  · rw [← hcast]
    exact hav.2

theorem robustRecommendationDifference_bounds {t : ℕ} (ht : t < T) (σ : Fin K → Fin K) :
    let d := run.robustRecommendationDifference σ t
    Measurable[run.info (t + 1)] d ∧
      (∀ ω, |d ω| ≤ 2) ∧
      (condExp (run.info t) P d =ᵐ[P] 0) ∧
      (condExp (run.info t) P (fun ω => d ω ^ 2) ≤ᵐ[P] fun _ => 1) := by
  intro d
  let g (j : Fin K) (ω : Ω) := run.y t ω (σ j) - run.y t ω j
  let c (ω : Ω) := robustSwapStep σ (run.q t ω) (run.y t ω)
  have hg (j : Fin K) : Measurable[run.info t] (g j) :=
    ((measurable_pi_apply (σ j)).comp (run.y_measurable t ht)).sub
      ((measurable_pi_apply j).comp (run.y_measurable t ht))
  have hc : Measurable[run.info t] c := run.robustSwapStep_measurable σ ht
  have hq (ω : Ω) : IsProbVec (run.q t ω) :=
    ⟨run.q_nonneg t ht ω, run.q_sum t ht ω⟩
  have hgb (j : Fin K) (ω : Ω) : |g j ω| ≤ 1 := by
    have hs := run.y_mem t ht ω (σ j)
    have hj := run.y_mem t ht ω j
    dsimp [g]
    exact abs_le.mpr ⟨by linarith [hs.1,hj.2], by linarith [hs.2,hj.1]⟩
  have hb (j : Fin K) (ω : Ω) : |g j ω - c ω| ≤ 2 := by
    calc
      _ ≤ |g j ω| + |c ω| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (hgb j ω) (robustSwapStep_abs_le σ (hq ω) (run.y_mem t ht ω))
      _ = 2 := by norm_num
  have hm₂ := run.info_mono t ht
  have hm₀ := run.info_le (t + 1) (by omega)
  have hmeas : Measurable[run.info (t+1)] d := by
    have hJm := run.J_measurable t ht
    let _ : MeasurableSpace Ω := run.info (t+1)
    exact (measurable_select hJm (fun j => (hg j).mono hm₂ le_rfl)).sub
      (hc.mono hm₂ le_rfl)
  have hav := condExp_centered_selected_on (F := Set.univ)
    (run.info_le t ht.le) MeasurableSet.univ ((run.J_measurable t ht).mono hm₀ le_rfl)
    (fun j => by simpa using run.J_law t ht j) g hg hc 2 1 hb
    (fun ω => (hq ω).2) (fun _ => rfl)
    (fun ω => calc
      _ ≤ ∑ j, run.q t ω j * 1 := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (by
          rw [← sq_abs]
          exact pow_le_one₀ (abs_nonneg _) (hgb j ω)) ((hq ω).1 j)
      _ = 1 := by simpa only [mul_one] using (hq ω).2) (by norm_num)
  refine ⟨hmeas, fun ω => hb _ ω, ?_, ?_⟩
  · change condExp (run.info t) P (fun ω => g (run.J t ω) ω - c ω) =ᵐ[P] 0
    simpa only [Set.indicator_univ] using hav.1
  · change condExp (run.info t) P (fun ω => (g (run.J t ω) ω - c ω) ^ 2) ≤ᵐ[P] fun _ => 1
    simpa only [Set.indicator_univ] using hav.2

omit [IsProbabilityMeasure P] in
theorem followedSwapScore_eq_robustSwapStep (σ : Fin K → Fin K) (t : ℕ) (ω : Ω) :
    followedSwapScore σ (robustEps T ζ) (run.q t ω) (run.y t ω) (run.I t ω) =
      robustSwapStep σ (run.q t ω) (robustYhat
        (followMix (robustEps T ζ) (run.q t ω)) (run.I t ω) (run.y t ω (run.I t ω))) := by
  classical
  rw [robustSwapStep_eq]
  unfold followedSwapScore robustYhat
  simp [mul_ite, Finset.sum_ite_eq, mul_div_assoc]

end QProtocolRun

end

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

def swapGain {K : ℕ} (T : ℕ) (q u : ℕ → Fin K → ℝ) (i j : Fin K) : ℝ :=
  ∑ t ∈ Finset.range T, q t i * (u t j - u t i)

def bestSwapGain {K : ℕ} (T : ℕ) (q u : ℕ → Fin K → ℝ) (i : Fin K) : ℝ :=
  Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (swapGain T q u i)

theorem swapGain_le_best {K T : ℕ} (q u : ℕ → Fin K → ℝ) (i j : Fin K) :
    swapGain T q u i j ≤ bestSwapGain T q u i :=
  Finset.le_sup' (swapGain T q u i) (Finset.mem_univ j)


/-- The swap map can maximize every row independently. -/
theorem pseudoSwapRegret_eq_sum_bestSwapGain {K : ℕ} (T : ℕ) (q u : ℕ → Fin K → ℝ) :
    pseudoSwapRegret T q u = ∑ i, bestSwapGain T q u i := by
  classical
  have score (f : Fin K → Fin K) :
      (∑ t ∈ Finset.range T, ((∑ i, q t i * u t (f i)) - q t ⬝ᵥ u t)) =
        ∑ i, swapGain T q u i (f i) := by
    unfold swapGain dotProduct
    have h (t : ℕ) : (∑ i, q t i * u t (f i)) - ∑ i, q t i * u t i =
        ∑ i, q t i * (u t (f i) - u t i) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    simp_rw [h]
    exact Finset.sum_comm
  unfold pseudoSwapRegret
  simp_rw [score]
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun f _ => Finset.sum_le_sum fun i _ => swapGain_le_best q u i (f i)
  · have exists_best (i : Fin K) : ∃ j, bestSwapGain T q u i = swapGain T q u i j := by
      obtain ⟨j, _, h⟩ := Finset.exists_mem_eq_sup' ⟨i, Finset.mem_univ i⟩ (swapGain T q u i)
      exact ⟨j, h⟩
    choose f hf using exists_best
    calc
      _ = ∑ i, swapGain T q u i (f i) := Finset.sum_congr rfl fun i _ => hf i
      _ ≤ _ := Finset.le_sup' (fun f : Fin K → Fin K => ∑ i, swapGain T q u i (f i))
        (Finset.mem_univ f)


end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

open Filter MeasureTheory
open scoped BigOperators ENNReal

private theorem abs_max_sub_max_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (f g : ι → ℝ) {C : ℝ} (h : ∀ i, |f i - g i| ≤ C) :
    |Finset.univ.sup' Finset.univ_nonempty f - Finset.univ.sup' Finset.univ_nonempty g| ≤ C := by
  classical
  apply abs_le.mpr
  constructor
  · have hle : Finset.univ.sup' Finset.univ_nonempty g
        ≤ Finset.univ.sup' Finset.univ_nonempty f + C := by
      apply Finset.sup'_le
      intro i hi
      linarith only [(abs_le.mp (h i)).1, Finset.le_sup' f hi]
    linarith
  · have hle : Finset.univ.sup' Finset.univ_nonempty f
        ≤ Finset.univ.sup' Finset.univ_nonempty g + C := by
      apply Finset.sup'_le
      intro i hi
      linarith only [(abs_le.mp (h i)).2, Finset.le_sup' g hi]
    linarith

private theorem pseudoSwapRegret_eq_robustSwapStep {K : ℕ} (s : ℕ)
    (q y : ℕ → Fin K → ℝ) :
    pseudoSwapRegret s q y = Finset.univ.sup' ⟨id, Finset.mem_univ id⟩
      (fun σ : Fin K → Fin K => ∑ t ∈ Finset.range s, robustSwapStep σ (q t) (y t)) := by
  unfold pseudoSwapRegret robustSwapStep dotProduct
  simp_rw [mul_sub, Finset.sum_sub_distrib]

private theorem robustHhat_eq_pseudoSwapRegret {K : ℕ} (hK : 0 < K) (T : ℕ) (ζ : ℝ)
    (q : ℕ → Fin K → ℝ) (I : ℕ → Fin K) (r : ℕ → ℝ) (s : ℕ) :
    robustHhat T ζ q I r s = pseudoSwapRegret s q
      (fun t => robustYhat (followMix (robustEps T ζ) (q t)) (I t) (r t)) := by
  classical
  let _ : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  rw [pseudoSwapRegret_eq_sum_bestSwapGain]
  unfold robustHhat bestSwapGain
  apply Finset.sum_congr rfl
  intro i _
  exact (Finset.sup'_univ_eq_ciSup (α := ℝ) (f := swapGain s q _ i)).symm

private theorem robustL_pos {K T s : ℕ} (hK : 0 < K) (hT : 0 < T) (hs : 0 < s) :
    0 < robustL K T s := by
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
  unfold robustL
  refine add_pos_of_nonneg_of_pos (mul_nonneg (by positivity) (Real.log_nonneg hk)) (Real.log_pos ?_)
  have ht₂ : (1 : ℝ) ≤ (T : ℝ) ^ 2 := one_le_pow₀ ht
  calc
    (1 : ℝ) < 4 * 1 * (1 + 1) * 1 := by norm_num
    _ ≤ _ := by gcongr

private theorem robustC_mul {K T s : ℕ} (ζ : ℝ) (hs : 0 < s) :
    (s : ℝ) * robustC K T ζ s =
      Real.sqrt (2 * s * (K * (T : ℝ) ^ ζ + 2) * robustL K T s) +
      (K * (T : ℝ) ^ ζ + 1) * robustL K T s / 3 := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  let c := 2 * (K * (T : ℝ) ^ ζ + 2) * robustL K T s
  have hfirst : (s : ℝ) * Real.sqrt (c / s) =
      Real.sqrt (2 * s * (K * (T : ℝ) ^ ζ + 2) * robustL K T s) := by
    rw [show (s : ℝ) * Real.sqrt (c / s) = Real.sqrt ((s : ℝ)^2 * (c / s)) by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs'.le]]
    congr 1
    dsimp [c]
    field_simp
  unfold robustC
  rw [mul_add]
  change _ + _ = _ + _
  rw [hfirst]
  congr 1
  field_simp

private theorem sum_reciprocal_succ_mul_succ (T : ℕ) :
    (∑ u ∈ Finset.range T, 1 / (((u : ℝ) + 1) * ((u : ℝ) + 2))) = 1 - 1 / (T + 1) := by
  induction T with
  | zero => norm_num
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

private theorem robustL_union_factor {K T u : ℕ} (hK : 0 < K) (hT : 0 < T) :
    (Fintype.card (Fin K → Fin K) : ℝ) * (2 * Real.exp (-robustL K T (u + 1))) =
      (1 / (2 * (T : ℝ) ^ 2)) * (1 / (((u : ℝ) + 1) * ((u : ℝ) + 2))) := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, robustL, neg_add,
    Real.exp_add, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hk]
  rw [Real.exp_log (by positivity)]
  push_cast
  field_simp [ne_of_gt hk]
  ring

private theorem measure_prefix_union {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {K T : ℕ} (hK : 0 < K) (hT : 0 < T) (bad : ℕ → (Fin K → Fin K) → Set Ω)
    (hbad : ∀ u < T, ∀ σ, P (bad u σ) ≤ 2 * ENNReal.ofReal (Real.exp (-robustL K T (u+1)))) :
    P (⋃ u ∈ Finset.range T, ⋃ σ, bad u σ) ≤
      ENNReal.ofReal (1 / (2 * (T : ℝ) ^ 2)) := by
  classical
  let f (u : ℕ) := (1 / (2 * (T : ℝ) ^ 2)) * (1 / (((u : ℝ) + 1) * ((u : ℝ) + 2)))
  have hB (u : ℕ) (hu : u < T) : P (⋃ σ, bad u σ) ≤ ENNReal.ofReal (f u) := by
    calc
      _ ≤ ∑' σ, P (bad u σ) := measure_iUnion_le _
      _ ≤ ∑ _ : Fin K → Fin K, 2 * ENNReal.ofReal (Real.exp (-robustL K T (u+1))) := by
        rw [tsum_fintype]
        exact Finset.sum_le_sum fun σ _ => hbad u hu σ
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        unfold f
        rw [← robustL_union_factor hK hT (u := u), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
        norm_num
  calc
    _ ≤ ∑ u ∈ Finset.range T, P (⋃ σ, bad u σ) := measure_biUnion_finset_le _ _
    _ ≤ ∑ u ∈ Finset.range T, ENNReal.ofReal (f u) := Finset.sum_le_sum fun u hu => hB u (Finset.mem_range.mp hu)
    _ = ENNReal.ofReal (∑ u ∈ Finset.range T, f u) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun u _ => by unfold f; positivity)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      unfold f
      rw [← Finset.mul_sum, sum_reciprocal_succ_mul_succ]
      exact mul_le_of_le_one_right (by positivity) (sub_le_self _ (by positivity))

namespace QProtocolRun

variable {K T : ℕ} {ζ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] (run : QProtocolRun K T P (robustPolicy K T ζ))

/-- Equation (C.11) for each prefix whose last round is in follow mode. -/
def robustEstimationGood : Set Ω :=
  {ω | ∀ u < T, ω ∈ run.robustFollowing u →
    |robustHhat T ζ (fun t => run.q t ω) (fun t => run.I t ω) (fun t => run.y t ω (run.I t ω)) (u+1)
      - pseudoSwapRegret (u+1) (fun t => run.q t ω) (fun t => run.y t ω)|
        ≤ (u+1 : ℕ) * robustC K T ζ (u+1)}

/-- Equation (C.12) for all recommendation prefixes. -/
def robustRecommendationGood : Set Ω :=
  {ω | ∀ u < T,
    |swapRegret (u+1) (fun t => run.y t ω) (fun t => run.J t ω)
      - pseudoSwapRegret (u+1) (fun t => run.q t ω) (fun t => run.y t ω)|
        ≤ (u+1 : ℕ) * robustC K T ζ (u+1)}

private theorem measurable_pseudoSwapRegret {s : ℕ} (hs : s ≤ T) :
    Measurable (fun ω => pseudoSwapRegret s (fun t => run.q t ω) (fun t => run.y t ω)) := by
  classical
  let _ : Nonempty (Fin K → Fin K) := ⟨id⟩
  simp only [pseudoSwapRegret_eq_robustSwapStep, Finset.sup'_univ_eq_ciSup]
  apply Measurable.iSup
  intro σ
  apply Finset.measurable_sum
  intro t ht
  have h₁ := (Finset.mem_range.mp ht).trans_le hs
  have h₂ := run.info_le t h₁.le
  unfold robustSwapStep
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_pi_apply i).comp ((run.q_measurable t h₁).mono h₂ le_rfl)).mul
    (((measurable_pi_apply (σ i)).comp ((run.y_measurable t h₁).mono h₂ le_rfl)).sub
      ((measurable_pi_apply i).comp ((run.y_measurable t h₁).mono h₂ le_rfl)))

private theorem measurable_recSwapRegret {s : ℕ} (hs : s ≤ T) :
    Measurable (fun ω => swapRegret s (fun t => run.y t ω) (fun t => run.J t ω)) := by
  classical
  let _ : Nonempty (Fin K → Fin K) := ⟨id⟩
  unfold swapRegret
  simp only [Finset.sup'_univ_eq_ciSup]
  apply Measurable.iSup
  intro σ
  apply Finset.measurable_sum
  intro t ht
  have ht' := (Finset.mem_range.mp ht).trans_le hs
  have h₂ := run.info_le t ht'.le
  have h₃ := run.info_le (t+1) (Nat.succ_le_of_lt ht')
  exact measurable_select ((run.J_measurable t ht').mono h₃ le_rfl) fun j =>
    (((measurable_pi_apply (σ j)).comp ((run.y_measurable t ht').mono h₂ le_rfl)).sub
      ((measurable_pi_apply j).comp ((run.y_measurable t ht').mono h₂ le_rfl)))

theorem measurableSet_robustEstimationGood : MeasurableSet run.robustEstimationGood := by
  unfold robustEstimationGood
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun u => MeasurableSet.iInter fun hu => ?_
  have hs : u + 1 ≤ T := Nat.succ_le_of_lt hu
  have hM := (run.measurable_robustHhat (s := u+1) (t := u+1) le_rfl hs).mono
    (run.info_le _ hs) le_rfl
  have hA := measurableSet_le ((hM.sub (run.measurable_pseudoSwapRegret hs)).abs)
    (measurable_const (a := ((u+1 : ℕ) : ℝ) * robustC K T ζ (u+1)))
  exact ((run.info_le u hu.le _ (run.measurableSet_robustFollowing hu.le)).compl.union hA).congr
    (by ext ω; simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq]; tauto)

theorem measurableSet_robustRecommendationGood : MeasurableSet run.robustRecommendationGood := by
  unfold robustRecommendationGood
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun u => MeasurableSet.iInter fun hu => ?_
  have hs : u + 1 ≤ T := Nat.succ_le_of_lt hu
  exact measurableSet_le
    (((run.measurable_recSwapRegret hs).sub (run.measurable_pseudoSwapRegret hs)).abs) measurable_const

theorem measure_compl_robustEstimationGood (hK : 0 < K) (hT : 0 < T)
    (hε : robustEps T ζ ≤ 1 / 2) :
    P run.robustEstimationGoodᶜ ≤ ENNReal.ofReal (1 / (2 * (T : ℝ) ^ 2)) := by
  classical
  let bad (u : ℕ) (σ : Fin K → Fin K) : Set Ω :=
    {ω | (u+1 : ℕ) * robustC K T ζ (u+1) <
      |∑ t ∈ Finset.range (u+1), run.robustEstimatorDifference σ t ω|}
  refine (measure_mono (show run.robustEstimationGoodᶜ ⊆ ⋃ u ∈ Finset.range T, ⋃ σ, bad u σ from ?_)).trans
    (measure_prefix_union P hK hT bad fun u hu σ => ?_)
  · intro ω hω
    simp only [Set.mem_compl_iff, robustEstimationGood, Set.mem_setOf_eq] at hω
    simp only [Set.mem_iUnion, Finset.mem_range]
    by_contra! hb
    apply hω
    intro u hu hf
    rw [robustHhat_eq_pseudoSwapRegret hK]
    simp only [pseudoSwapRegret_eq_robustSwapStep]
    letI : Nonempty (Fin K → Fin K) := ⟨id⟩
    apply abs_max_sub_max_le
    intro σ
    rw [← Finset.sum_sub_distrib]
    have heq : ∀ t < u+1, robustSwapStep σ (run.q t ω)
        (robustYhat (followMix (robustEps T ζ) (run.q t ω)) (run.I t ω) (run.y t ω (run.I t ω))) -
        robustSwapStep σ (run.q t ω) (run.y t ω) = run.robustEstimatorDifference σ t ω := by
      intro t ht
      have htFollow : ω ∈ run.robustFollowing t := fun v hv => hf v (by omega)
      unfold robustEstimatorDifference
      rw [Set.indicator_of_mem htFollow, run.followedSwapScore_eq_robustSwapStep]
    rw [Finset.sum_congr rfl fun t ht => heq t (Finset.mem_range.mp ht)]
    exact not_lt.mp (hb u hu σ)
  · have hs : 0 < u+1 := by omega
    have hsT : u+1 ≤ T := by omega
    have hL := robustL_pos hK hT hs
    change P {ω | (u+1 : ℕ) * robustC K T ζ (u+1) <
        |∑ t ∈ Finset.range (u+1), run.robustEstimatorDifference σ t ω|} ≤ _
    rw [robustC_mul _ hs]
    refine bernstein_abs_tail P run.info hs (fun a n ha hn => run.toDrawRun.info_le_info ha (hn.trans hsT))
      (fun n hn => run.info_le n (hn.trans hsT)) (run.robustEstimatorDifference σ)
      (by positivity) (by positivity) hL ?_ ?_ ?_ ?_
    · exact fun t ht => (run.robustEstimatorDifference_bounds hK (ht.trans_le hsT) hε σ).1
    · exact fun t ht => (run.robustEstimatorDifference_bounds hK (ht.trans_le hsT) hε σ).2.1
    · exact fun t ht => (run.robustEstimatorDifference_bounds hK (ht.trans_le hsT) hε σ).2.2.1
    · exact fun t ht => (run.robustEstimatorDifference_bounds hK (ht.trans_le hsT) hε σ).2.2.2

theorem measure_compl_robustRecommendationGood (hK : 0 < K) (hT : 0 < T)
    (hε : robustEps T ζ ≤ 1 / 2) :
    P run.robustRecommendationGoodᶜ ≤ ENNReal.ofReal (1 / (2 * (T : ℝ) ^ 2)) := by
  classical
  let bad (u : ℕ) (σ : Fin K → Fin K) : Set Ω :=
    {ω | (u+1 : ℕ) * robustC K T ζ (u+1) <
      |∑ t ∈ Finset.range (u+1), run.robustRecommendationDifference σ t ω|}
  refine (measure_mono (show run.robustRecommendationGoodᶜ ⊆ ⋃ u ∈ Finset.range T, ⋃ σ, bad u σ from ?_)).trans
    (measure_prefix_union P hK hT bad fun u hu σ => ?_)
  · intro ω hω
    simp only [Set.mem_compl_iff, robustRecommendationGood, Set.mem_setOf_eq] at hω
    simp only [Set.mem_iUnion, Finset.mem_range]
    by_contra! hb
    apply hω
    intro u hu
    rw [pseudoSwapRegret_eq_robustSwapStep]
    unfold swapRegret
    letI : Nonempty (Fin K → Fin K) := ⟨id⟩
    apply abs_max_sub_max_le
    intro σ
    rw [← Finset.sum_sub_distrib]
    exact not_lt.mp (hb u hu σ)
  · have hs : 0 < u+1 := by omega
    have hsT : u+1 ≤ T := by omega
    have hL := robustL_pos hK hT hs
    have hp : (1 : ℝ) ≤ K * (T : ℝ) ^ ζ := by
      have hpos : 0 < (T : ℝ) ^ ζ := by positivity
      have ht1 : (1 : ℝ) ≤ (T : ℝ) ^ ζ := by
        have hT₀ : (0 : ℝ) ≤ T := by positivity
        have hi : ((T : ℝ) ^ ζ)⁻¹ ≤ 1 / 2 := by
          simpa only [robustEps, Real.rpow_neg hT₀] using hε
        linarith only [(inv_le_iff_one_le_mul₀ hpos).mp hi]
      exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hK) ht1
    have hc : Real.sqrt (2 * (u+1 : ℕ) * 1 * robustL K T (u+1)) +
          2 * robustL K T (u+1) / 3 ≤ (u+1 : ℕ) * robustC K T ζ (u+1) := by
      rw [robustC_mul _ hs]
      apply add_le_add
      · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith only [hp]) (by positivity)) hL.le)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith only [hp]) hL.le) (by norm_num)
    have hsub : bad u σ ⊆ {ω |
        Real.sqrt (2 * (u+1 : ℕ) * 1 * robustL K T (u+1)) + 2 * robustL K T (u+1) / 3 <
          |∑ t ∈ Finset.range (u+1), run.robustRecommendationDifference σ t ω|} := by
      intro ω hω
      exact hc.trans_lt hω
    refine (measure_mono hsub).trans ?_
    refine bernstein_abs_tail P run.info hs (fun a n ha hn => run.toDrawRun.info_le_info ha (hn.trans hsT))
      (fun n hn => run.info_le n (hn.trans hsT)) (run.robustRecommendationDifference σ)
      (by norm_num) (by norm_num) hL ?_ ?_ ?_ ?_
    · exact fun t ht => (run.robustRecommendationDifference_bounds (ht.trans_le hsT) σ).1
    · exact fun t ht => (run.robustRecommendationDifference_bounds (ht.trans_le hsT) σ).2.1
    · exact fun t ht => (run.robustRecommendationDifference_bounds (ht.trans_le hsT) σ).2.2.1
    · exact fun t ht => (run.robustRecommendationDifference_bounds (ht.trans_le hsT) σ).2.2.2

end QProtocolRun

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

open MeasureTheory Set
open scoped ENNReal

private theorem robust_inverse_square (T : ℕ) :
    (T : ℝ) ^ (-2 : ℝ) = ((T : ℝ) ^ (2 : ℕ))⁻¹ := by
  rw [show (-2 : ℝ) = -(2 : ℝ) by ring, Real.rpow_neg (Nat.cast_nonneg T), Real.rpow_ofNat]

private theorem robustEps_le_half_of_four_le {T : ℕ}
    (hT : 4 ≤ T) {ζ : ℝ} (hζ : 1 / 2 ≤ ζ) :
    robustEps T ζ ≤ 1 / 2 := by
  have ht : (4 : ℝ) ≤ T := by exact_mod_cast hT
  have ht1 : 1 ≤ (T : ℝ) := by linarith
  have hs := Real.sqrt_le_sqrt ht
  rw [show Real.sqrt (4 : ℝ) = 2 by norm_num] at hs
  have h := Real.rpow_le_rpow_of_exponent_le ht1 (show -ζ ≤ -(1 / 2) by linarith)
  refine h.trans ?_
  rw [Real.rpow_neg (Nat.cast_nonneg T), ← Real.sqrt_eq_rpow]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs

private theorem robustEps_mul_le_rate {K T : ℕ} {ζ : ℝ} (hK : 1 ≤ K) (hT : 1 ≤ T)
    (hζ : 1 / 2 ≤ ζ) :
    robustEps T ζ * (T : ℝ) ≤ robustRate K T ζ := by
  have ht1 : 1 ≤ (T : ℝ) := by exact_mod_cast hT
  have ht₀ : 0 < (T : ℝ) := by linarith
  have hk1 : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  have hL := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hk1 ht1)
  calc
    _ = (T : ℝ) ^ (-ζ + 1) := by
      unfold robustEps
      rw [Real.rpow_add ht₀, Real.rpow_one]
    _ ≤ (T : ℝ) ^ ((1 + ζ) / 2) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    _ ≤ _ := by
      unfold robustRate
      have hn : 0 ≤ (T : ℝ) ^ ((1 + ζ) / 2) := by positivity
      calc
        _ ≤ _ * _ := le_mul_of_one_le_left hn hk1
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (by linarith)

private theorem robust_one_action (y : ℕ → Fin 1 → ℝ) (I J : ℕ → Fin 1) (T : ℕ) :
    rewardLoss T y J I = 0 := by
  have h (f : Fin 1 → Fin 1) :
      ∑ t ∈ Finset.range T, (y t (f (J t)) - y t (I t)) = 0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [Subsingleton.elim (f (J t)) (I t), sub_self]
  unfold rewardLoss
  simp_rw [h]
  exact Finset.sup'_const _ _

universe u

/-- Algorithm 2, with the switching threshold from the paper and the tuned
calibeating policy after the switch, satisfies both clauses of robust calibeating. -/
theorem theorem_3_5 :
    ∀ ζ : ℝ, 1 / 2 < ζ → ζ < 1 →
      ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ K T : ℕ, 1 ≤ K → 1 ≤ T →
        IsRobust.{u} K T
          (C * K * (T : ℝ) ^ (-(1 - ζ) / 2) * (1 + Real.log (K * T)) ^ k)
          (C * K * (T : ℝ) ^ (-(1 - ζ) / 2) * (1 + Real.log (K * T)) ^ k)
          (2 * (T : ℝ) ^ (-ζ) + (T : ℝ) ^ (-2 : ℝ))
          (robustC K T ζ) (robustPolicy K T ζ) := by
  intro ζ hζ _
  refine ⟨160, by norm_num, 1, ?_⟩
  intro K T hK hT
  have hpK : 0 < K := by omega
  have hpT : 0 < T := by omega
  have hz : 0 ≤ ζ := by linarith
  let R := robustRate K T ζ
  have hR : 1 ≤ R := robustRate_ge_one hK hT hz
  have threshNonneg : 0 ≤ robustC K T ζ T := by
    have hL := robustL_nonneg hK hT hT
    unfold robustC
    positivity
  have bad {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (run : QProtocolRun K T P (robustPolicy K T ζ))
      (hε : robustEps T ζ ≤ 1 / 2) :
      P (run.robustEstimationGood ∩ run.robustRecommendationGood)ᶜ ≤
        ENNReal.ofReal ((T : ℝ) ^ (-2 : ℝ)) := by
    rw [compl_inter, robust_inverse_square]
    have hE := run.measure_compl_robustEstimationGood hpK hpT hε
    have hJ := run.measure_compl_robustRecommendationGood hpK hpT hε
    refine (measure_union_le _ _).trans ((add_le_add hE hJ).trans_eq ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  constructor
  · intro Ω mΩ P iP run
    rw [← robustRate_normalize hpT ζ (160 : ℝ)]
    change (∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P) ≤
      160 * R ∧ (∫ ω, rewardLoss T (fun t => run.y t ω)
        (fun t => run.J t ω) (fun t => run.I t ω) ∂P) ≤ 160 * R
    have trivial (h : (T : ℝ) ≤ 160 * R) :
        (∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P) ≤
          160 * R ∧ (∫ ω, rewardLoss T (fun t => run.y t ω)
            (fun t => run.J t ω) (fun t => run.I t ω) ∂P) ≤ 160 * R := by
      have hS := run.integrable_swapRegret_segment 0 T (by simp)
      have hR := run.integrable_rewardLoss_segment 0 T (by simp)
      simp only [zero_add] at hS hR
      have A := integral_mono hS (integrable_const (T : ℝ)) (fun ω =>
        rewardLoss_le_rounds _ _ _ (fun t ht i => run.y_mem t ht ω i))
      have B := integral_mono hR (integrable_const (T : ℝ)) (fun ω =>
        rewardLoss_le_rounds _ _ _ (fun t ht i => run.y_mem t ht ω i))
      simp only [integral_const, probReal_univ, one_smul] at A B
      exact ⟨A.trans h, B.trans h⟩
    by_cases hsmall : 32 * R ≤ (T : ℝ)
    swap
    · exact trivial (by linarith)
    by_cases h1 : K = 1
    · subst K
      have hs (ω : Ω) : swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) = 0 :=
        robust_one_action _ _ _ _
      have hr (ω : Ω) : rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω)
          (fun t => run.I t ω) = 0 := robust_one_action _ _ _ _
      simp only [hs, hr, integral_zero]
      constructor <;> linarith
    have hT4 : 4 ≤ T := by
      have hTr : (4 : ℝ) ≤ T := by linarith
      exact_mod_cast hTr
    have hε := robustEps_le_half_of_four_le hT4 hζ.le
    let E := run.robustEstimationGood ∩ run.robustRecommendationGood
    have hE : MeasurableSet E :=
      run.measurableSet_robustEstimationGood.inter run.measurableSet_robustRecommendationGood
    have hprefix := run.robust_prefix_expected hK hT hz threshNonneg
      run.robustFollowLength run.measurable_robustFollowLength run.robustFollowLength_le
      (fun ω t ht => run.follows_before_length ht) E hE (bad P run hε)
      (fun _ hω => hω.1) (fun _ hω => hω.2)
    obtain ⟨he, hm, hm', hbound⟩ := robustRate_restart_parameters (by omega : 2 ≤ K) hT hz hsmall
    have hsuffix := run.robust_restart_regret hpK he hm hm'
    have hthresh : (T : ℝ) * robustC K T ζ T ≤ 20 * R :=
      robustThreshold_le_rate hK hT hz (by linarith)
    have hεR : robustEps T ζ * T ≤ R := robustEps_mul_le_rate hK hT hζ.le
    have hTinv : (T : ℝ) * (T : ℝ) ^ (-2 : ℝ) ≤ 1 := by
      have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
      have htp : 0 < (T : ℝ) := by linarith
      rw [robust_inverse_square, ← div_eq_mul_inv]
      exact (div_le_one (by positivity)).2 (by nlinarith [mul_nonneg htp.le (sub_nonneg.mpr ht)])
    have hpreS : (∫ ω, run.robustPrefixSwapRegret ω ∂P) ≤ 104 * R := by
      have hp := hprefix.1
      change (∫ ω, run.robustPrefixSwapRegret ω ∂P) ≤ _ at hp
      linarith [hp, hεR, hthresh, hTinv]
    have hpreR : (∫ ω, run.robustPrefixRewardLoss ω ∂P) ≤ 104 * R := by
      have hp := hprefix.2
      change (∫ ω, run.robustPrefixRewardLoss ω ∂P) ≤ _ at hp
      linarith [hp, hεR, hthresh, hTinv]
    have hspl := run.robustRegret_split
    exact ⟨hspl.1.trans (by linarith [hpreS, hsuffix.1, hbound]),
      hspl.2.trans (by linarith [hpreR, hsuffix.2, hbound])⟩
  · intro Ω mΩ P iP run ρ hρ₀ hρ₁ hcap
    by_cases hε : robustEps T ζ ≤ 1 / 2
    · let E := run.robustEstimationGood ∩ run.robustRecommendationGood
      have hE : MeasurableSet E :=
        run.measurableSet_robustEstimationGood.inter run.measurableSet_robustRecommendationGood
      apply run.robust_consistency_of_event hpK hpT hz ρ hρ₀ hρ₁ E hE (bad P run hε) _ hcap
      intro ω hω
      refine robust_never_crosses ζ (fun t => run.q t ω) (fun t => run.y t ω)
        (fun t => run.J t ω) (fun t => run.I t ω) (fun t => run.y t ω (run.I t ω))
        hω.2 ?_ ?_
      · intro s hs hst
        have he := hω.1.2 (s - 1) (by omega)
        rw [show s - 1 + 1 = s by omega] at he
        linarith only [(abs_le.mp he).1]
      · intro t ht hf
        linarith only [(abs_le.mp (hω.1.1 t ht hf)).2]
    · have hγ : 1 ≤ 2 * robustEps T ζ + (T : ℝ) ^ (-2 : ℝ) := by
        have h : (1 / 2 : ℝ) < robustEps T ζ := lt_of_not_ge hε
        linarith [Real.rpow_nonneg (Nat.cast_nonneg T) (-2 : ℝ)]
      exact run.robust_consistency_of_gamma_ge_one ρ _ hρ₀ hγ

end CalibeatBandit.Supplement

end

section

universe u

open MeasureTheory Filter Asymptotics CalibeatBandit CalibeatBandit.Supplement

set_option autoImplicit false in
theorem solution :
    ∀ ζ : ℝ, 1 / 2 < ζ → ζ < 1 →
      ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ K T : ℕ, 1 ≤ K → 1 ≤ T →
        IsRobust.{u} K T
          (C * K * (T : ℝ) ^ (-(1 - ζ) / 2) * (1 + Real.log (K * T)) ^ k)
          (C * K * (T : ℝ) ^ (-(1 - ζ) / 2) * (1 + Real.log (K * T)) ^ k)
          (2 * (T : ℝ) ^ (-ζ) + (T : ℝ) ^ (-2 : ℝ))
          (robustC K T ζ) (robustPolicy K T ζ) := CalibeatBandit.Supplement.theorem_3_5

end
