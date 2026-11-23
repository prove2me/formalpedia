-- Prove2me | solution 1 for CalibeatBandit.tree_expected_selected_hits
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T18:47:38.154011+00:00
-- url     : https://prove2.me/submissions/af3a8140-b2cc-4f71-9af4-a8a1c466369e

import Mathlib
import Definitions.Def_CalibeatBandit_lower_bound_models
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_hard_tree_environment
import Definitions.Def_CalibeatBandit_hard_tree_analysis
import Theorems.Thm_CalibeatBandit_integral_periodHits_average_le

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

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

@[simp] theorem rewardTapePrefix_refl (N r : ℕ) :
    rewardTapePrefix N (le_refl r) = id := by simp [rewardTapePrefix]

@[simp] theorem rewardTapePrefix_succ (N : ℕ) {r t : ℕ} (h : r ≤ t) :
    rewardTapePrefix N (Nat.le_succ_of_le h) = rewardTapePrefix N h ∘ Prod.fst := by
  unfold rewardTapePrefix
  exact Nat.leRec_succ _ _ h

theorem measurable_rewardTapePrefix (N : ℕ) {r t : ℕ} (h : r ≤ t) :
    Measurable (rewardTapePrefix N h) := by
  induction h with
  | refl => rw [rewardTapePrefix_refl]; exact measurable_id
  | step h ih => rw [rewardTapePrefix_succ N h]; exact ih.comp measurable_fst

theorem rewardTapePrefix_comp (N : ℕ) {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    rewardTapePrefix N hrs ∘ rewardTapePrefix N hst = rewardTapePrefix N (hrs.trans hst) := by
  induction hst with
  | refl => simp
  | step hs ih =>
    rw [rewardTapePrefix_succ N hs, rewardTapePrefix_succ N (hrs.trans hs)]
    funext tape
    exact congrFun ih tape.1

theorem rewardTapePrefix_map (N : ℕ) {r t : ℕ} (h : r ≤ t) :
    (rewardTapeLaw N t).map (rewardTapePrefix N h) = rewardTapeLaw N r := by
  induction h with
  | refl => rw [rewardTapePrefix_refl, Measure.map_id]
  | step h ih =>
    rw [rewardTapePrefix_succ N h]
    change ((rewardTapeLaw N _).prod (roundDrawLaw N)).map
      (rewardTapePrefix N h ∘ Prod.fst) = _
    rw [← Measure.map_map (measurable_rewardTapePrefix N h) measurable_fst, Measure.map_fst_prod,
      measure_univ, one_smul, ih]

open scoped ENNReal

theorem measurable_supportedBase : Measurable fun x => (supportedBase x : ℝ) := by
  have he : (fun x => (supportedBase x : ℝ)) = fun x => if x ∈ Icc (0 : ℝ) 1 then x else 0 := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [supportedBase, hx]
  rw [he]
  exact Measurable.ite measurableSet_Icc measurable_id measurable_const

theorem measurable_supportedThreshold : Measurable fun x => (supportedThreshold x : ℝ) := by
  have he : (fun x => (supportedThreshold x : ℝ)) = fun x => if x ∈ Ico (0 : ℝ) 1 then x else 0 := by
    funext x
    by_cases hx : x ∈ Ico (0 : ℝ) 1 <;> simp [supportedThreshold, hx]
  rw [he]
  exact Measurable.ite measurableSet_Ico measurable_id measurable_const

theorem measurable_boundedRoundReward {N : ℕ} (η u : ℝ) (i : Fin N) :
    Measurable (boundedRoundReward η u i) := by
  let z (d : ℝ × (Fin N → ℝ)) : ℝ := supportedBase d.1
  have hz : Measurable z := measurable_supportedBase.comp measurable_fst
  have hth := measurable_supportedThreshold.comp ((measurable_pi_apply i).comp
    (measurable_snd : Measurable (Prod.snd : ℝ × (Fin N → ℝ) → (Fin N → ℝ))))
  unfold boundedRoundReward bonusReward
  simp only [decide_eq_true_eq]
  exact (measurable_const.add (hz.div_const _)).add
    (((hz.const_mul _).mul (measurable_const.sub hz)).mul
      (Measurable.ite (measurableSet_lt hth measurable_const) measurable_const measurable_const))

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

/-- Append a period's independent draws to a tape for the preceding rounds. -/
def rewardTapeAppend (N start : ℕ) :
    (r : ℕ) → RewardTape N start × RewardTape N r → RewardTape N (start + r)
  | 0, p => p.1
  | r + 1, p => (rewardTapeAppend N start r (p.1, p.2.1), p.2.2)

theorem measurable_rewardTapeAppend (N start r : ℕ) :
    Measurable (rewardTapeAppend N start r) := by
  induction r with
  | zero => exact measurable_fst
  | succ r ih =>
    exact (ih.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)

theorem rewardTapeAppend_map (N start r : ℕ) :
    ((rewardTapeLaw N start).prod (rewardTapeLaw N r)).map (rewardTapeAppend N start r) =
      rewardTapeLaw N (start + r) := by
  induction r with
  | zero =>
    change ((rewardTapeLaw N start).prod (rewardTapeLaw N 0)).map Prod.fst = _
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    rfl
  | succ r ih =>
    let A := RewardTape N start
    let B := RewardTape N r
    let D := ℝ × (Fin N → ℝ)
    let μ := rewardTapeLaw N start
    let ν := rewardTapeLaw N r
    let ρ := roundDrawLaw N
    let f := rewardTapeAppend N start r
    let assoc : (A × B) × D ≃ᵐ A × B × D := MeasurableEquiv.prodAssoc
    have hf : Measurable f := measurable_rewardTapeAppend N start r
    let g : A × (B × D) → RewardTape N (start + r) × D := rewardTapeAppend N start (r + 1)
    have hg : Measurable g := measurable_rewardTapeAppend N start (r + 1)
    have ha : MeasurePreserving assoc ((μ.prod ν).prod ρ) (μ.prod (ν.prod ρ)) :=
      measurePreserving_prodAssoc μ ν ρ
    have hmap : ((μ.prod ν).prod ρ).map (Prod.map f id) =
        (rewardTapeLaw N (start + r)).prod ρ := by
      rw [← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id, ih]
    change (μ.prod (ν.prod ρ)).map g = (rewardTapeLaw N (start + r)).prod ρ
    rw [← ha.map_eq, Measure.map_map hg assoc.measurable]
    exact hmap

theorem rewardTapePrefix_append (N start : ℕ) {s r : ℕ} (hs : s ≤ r)
    (p : RewardTape N start) (q : RewardTape N r) :
    rewardTapePrefix N (Nat.add_le_add_left hs start) (rewardTapeAppend N start r (p, q)) =
      rewardTapeAppend N start s (p, rewardTapePrefix N hs q) := by
  induction hs with
  | refl =>
    simp only [rewardTapePrefix_refl, id_eq]
  | @step r hs ih =>
    have hf := rewardTapePrefix_succ N (Nat.add_le_add_left hs start)
    have hg := rewardTapePrefix_succ N hs
    change rewardTapePrefix N (Nat.le_succ_of_le (Nat.add_le_add_left hs start))
        (rewardTapeAppend N start (r + 1) (p, q)) =
      rewardTapeAppend N start s (p, rewardTapePrefix N (Nat.le_succ_of_le hs) q)
    rw [hf, hg]
    exact ih q.1

/-- Add the observations from a period to the history before it starts,
converting normalized observations back to the learner's raw reward scale. -/
noncomputable def historyAppend (start : ℕ) :
    (r : ℕ) → FeedbackHistory start × FeedbackHistory r → FeedbackHistory (start + r)
  | 0, p => p.1
  | r + 1, p => (historyAppend start r (p.1, p.2.1), 1 / 8 + p.2.2 / 8)

theorem measurable_historyAppend (start r : ℕ) : Measurable (historyAppend start r) := by
  induction r with
  | zero => exact measurable_fst
  | succ r ih =>
    exact (ih.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_const.add (((measurable_snd : Measurable (Prod.snd : FeedbackHistory r × ℝ → ℝ)).comp
        measurable_snd).div_const _))

theorem measurable_rawTapeHistory {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (r : ℕ) : Measurable (rawTapeHistory η u pick r) := by
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
    change Measurable (fun p : RewardTape N r × (ℝ × (Fin N → ℝ)) =>
      (rawTapeHistory η u pick r p.1,
        boundedRoundReward η (u r (pick r (rawTapeHistory η u pick r p.1)))
          (pick r (rawTapeHistory η u pick r p.1)) p.2))
    exact (ih.comp measurable_fst).prodMk
      (measurable_select ((hm r).comp (ih.comp measurable_fst)) fun i =>
        (measurable_boundedRoundReward η (u r i) i).comp measurable_snd)

/-- Conditional on the past, the full learner in a period is precisely a
learner on the normalized observations made within that period. -/
theorem rawTapeHistory_append {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (start r : ℕ)
    (past : RewardTape N start) (next : RewardTape N r) :
    let initial := rawTapeHistory η u pick start past
    let localPick (t : ℕ) (x : FeedbackHistory t) := pick (start + t) (historyAppend start t (initial, x))
    rawTapeHistory η u pick (start + r) (rewardTapeAppend N start r (past, next)) =
      historyAppend start r (initial,
        boundedTapeTranscript η (fun t => u (start + t)) localPick r next) := by
  intro initial localPick
  induction r with
  | zero => rfl
  | succ r ih =>
    let x := rawTapeHistory η u pick (start + r) (rewardTapeAppend N start r (past, next.1))
    let y := boundedTapeTranscript η (fun t => u (start + t)) localPick r next.1
    let hist := historyAppend start r (initial, y)
    let j (p : FeedbackHistory (start + r)) := pick (start + r) p
    change (x, boundedRoundReward η (u (start + r) (j x)) (j x) next.2) =
      (hist, 1 / 8 + boundedObservation η (u (start + r) (localPick r y)) (localPick r y) next.2 / 8)
    have hx : x = hist := ih next.1
    have hj : localPick r y = j hist := rfl
    rw [hx, hj]
    congr 1
    unfold boundedObservation
    ring

theorem rawTapeHistory_congr {N : ℕ} (η : ℝ) (u u' : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (r : ℕ)
    (h : ∀ t < r, u t = u' t) (tape : RewardTape N r) :
    rawTapeHistory η u pick r tape = rawTapeHistory η u' pick r tape := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have he := ih (fun t ht => h t (Nat.lt_succ_of_lt ht)) tape.1
    simp only [rawTapeHistory, he, h r (Nat.lt_succ_self r)]
    rfl

private theorem measurable_playHit {A : Type*} [MeasurableSpace A] {N : ℕ} {a : A → Fin N}
    (ha : Measurable a) (j : Fin N) : Measurable fun x => if a x = j then (1 : ℝ) else 0 :=
  Measurable.ite (measurableSet_eq_fun ha measurable_const) measurable_const measurable_const

theorem boundedTapeTranscript_congr {N : ℕ} (η : ℝ) (u u' : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (r : ℕ)
    (h : ∀ t < r, u t = u' t) (tape : RewardTape N r) :
    boundedTapeTranscript η u pick r tape = boundedTapeTranscript η u' pick r tape := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [boundedTapeTranscript, boundedTapeTranscript, ih (fun t ht => h t (Nat.lt_succ_of_lt ht)),
      h r (Nat.lt_succ_self r)]

/-- Count plays of one action in an interval on the full reward tape. -/
noncomputable def globalPeriodHits {N T : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (a : Fin N)
    (start r : ℕ) (hend : start + r ≤ T) (tape : RewardTape N T) : ℝ :=
  ∑ i : Fin r, if pick (start + i)
    (rawTapeHistory η u pick (start + i)
      (rewardTapePrefix N ((Nat.add_le_add_left i.isLt.le start).trans hend) tape)) = a then 1 else 0

theorem measurable_globalPeriodHits {N T : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (a : Fin N) (start r : ℕ) (hend : start + r ≤ T) :
    Measurable (globalPeriodHits η u pick a start r hend) :=
  Finset.measurable_sum _ fun i _ => measurable_playHit
    ((hm (start + i)).comp ((measurable_rawTapeHistory η u pick hm (start + i)).comp
      (measurable_rewardTapePrefix N _))) a

theorem abs_globalPeriodHits {N T : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (a : Fin N)
    (start r : ℕ) (hend : start + r ≤ T) (tape : RewardTape N T) :
    |globalPeriodHits η u pick a start r hend tape| ≤ r := by
  classical
  unfold globalPeriodHits
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _ : Fin r, (1 : ℝ) := Finset.sum_le_sum fun _ _ => by split <;> norm_num
    _ = _ := by simp

private theorem integral_globalPeriodHits_prefix {N T : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (a : Fin N) (start r : ℕ) (hend : start + r ≤ T) :
    (∫ tape, globalPeriodHits η u pick a start r hend tape ∂rewardTapeLaw N T) =
      ∫ tape, globalPeriodHits η u pick a start r le_rfl tape ∂rewardTapeLaw N (start + r) := by
  have he := integral_map (μ := rewardTapeLaw N T) (measurable_rewardTapePrefix N hend).aemeasurable
    (measurable_globalPeriodHits η u pick hm a start r (le_refl (start + r))).aestronglyMeasurable
  rw [rewardTapePrefix_map] at he
  rw [he]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun tape => ?_
  unfold globalPeriodHits
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcomp := congrFun (rewardTapePrefix_comp N (Nat.add_le_add_left i.isLt.le start) hend) tape
  dsimp only [Function.comp_apply] at hcomp
  rw [hcomp]

private theorem globalPeriodHits_append {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (a : Fin N) (start r : ℕ)
    (past : RewardTape N start) (next : RewardTape N r) :
    let initial := rawTapeHistory η u pick start past
    let localPick (t : ℕ) (x : FeedbackHistory t) := pick (start + t) (historyAppend start t (initial, x))
    globalPeriodHits η u pick a start r le_rfl (rewardTapeAppend N start r (past, next)) =
      periodHits η (fun t => u (start + t)) localPick a r next := by
  intro initial localPick
  unfold globalPeriodHits periodHits
  refine Finset.sum_congr rfl fun i _ => ?_
  have hp := rewardTapePrefix_append N start i.isLt.le past next
  rw [hp]
  have hh := rawTapeHistory_append η u pick start i past (rewardTapePrefix N i.isLt.le next)
  rw [hh]

set_option maxHeartbeats 850000 in
/-- The one-period bound also holds after averaging over all earlier draws
in the global tape. Varying this period's selected action leaves the initial
history unchanged. -/
theorem tree_global_period_average {h M U N T : ℕ}
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (hη : 0 ≤ η) (hη₁ : η < 1)
    (active : ℕ → Fin (2 ^ h)) (leaf : Fin (2 ^ h)) (start r : ℕ) (hend : start + r ≤ T)
    (hbefore : ∀ t < start, active t ≠ leaf) (hwithin : ∀ t < r, active (start + t) = leaf)
    (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool) (selected : Fin (2 ^ h) → Fin M)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t)) :
    let aux (j : Fin M) := e.symm (.inr (.inl j))
    let u (j : Fin M) := scheduledBonuses e active coin leafCoin (Function.update selected leaf j)
    (∑ j : Fin M, ∫ tape, globalPeriodHits η (u j) pick (aux j) start r hend tape ∂rewardTapeLaw N T) / M
      ≤ (r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M)) := by
  classical
  intro aux u
  let μ := rewardTapeLaw N start
  let ν := rewardTapeLaw N r
  let whole := scheduledBonuses e active coin leafCoin selected
  let payoff (j : Fin M) := globalPeriodHits η (u j) pick (aux j) start r (le_refl (start + r))
  let app := rewardTapeAppend N start r
  let F (j : Fin M) (p : RewardTape N start × RewardTape N r) := payoff j (app p)
  have hF (j : Fin M) : Integrable (F j) (μ.prod ν) := by
    apply Integrable.of_bound
      ((measurable_globalPeriodHits η (u j) pick hm (aux j) start r _).comp
        (measurable_rewardTapeAppend N start r)).aestronglyMeasurable r
    refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs]
    exact abs_globalPeriodHits η (u j) pick (aux j) start r _ (app p)
  have hwhole (j : Fin M) :
      (∫ tape, globalPeriodHits η (u j) pick (aux j) start r hend tape ∂rewardTapeLaw N T) =
        ∫ p, (∫ next, F j (p, next) ∂ν) ∂μ := by
    rw [integral_globalPeriodHits_prefix η (u j) pick hm (aux j) start r hend]
    have he := integral_map (μ := μ.prod ν) (measurable_rewardTapeAppend N start r).aemeasurable
      (measurable_globalPeriodHits η (u j) pick hm (aux j) start r (le_refl (start + r))).aestronglyMeasurable
    change (∫ t, payoff j t ∂(μ.prod ν).map app) = ∫ p, F j p ∂μ.prod ν at he
    rw [show (μ.prod ν).map app = rewardTapeLaw N (start + r) from rewardTapeAppend_map N start r] at he
    exact he.trans (integral_prod (F j) (hF j))
  rw [Finset.sum_congr rfl (fun j _ => hwhole j), ← integral_finsetSum _ (fun j _ => (hF j).integral_prod_left),
    ← integral_div]
  let bound := (r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))
  have hf : Integrable (fun p => (∑ j : Fin M, ∫ next, F j (p, next) ∂ν) / M) μ :=
    (integrable_finsetSum _ fun j _ => (hF j).integral_prod_left).div_const _
  suffices h : ∀ p : RewardTape N start,
      (∑ j : Fin M, ∫ next, F j (p, next) ∂ν) / M ≤ bound by
    simpa only [integral_const, probReal_univ, one_smul] using integral_mono hf (integrable_const bound) h
  intro p
  let initial := rawTapeHistory η whole pick start p
  let localPick (t : ℕ) (x : FeedbackHistory t) := pick (start + t) (historyAppend start t (initial, x))
  have hlocal (t : ℕ) : Measurable (localPick t) :=
    (hm _).comp ((measurable_historyAppend start t).comp (measurable_const.prodMk measurable_id))
  let bonus (j : Fin M) (t : ℕ) (i : Fin N) := treeBonusProb leaf coin (leafCoin (start + t)) j (e i)
  have hprev (j : Fin M) : rawTapeHistory η (u j) pick start p = initial := by
    apply rawTapeHistory_congr
    intro t ht
    funext i
    simp only [u, whole, scheduledBonuses, Function.update_of_ne (hbefore t ht)]
  have hbonus (j : Fin M) (t : ℕ) (ht : t < r) : u j (start + t) = bonus j t := by
    funext i
    simp only [u, bonus, scheduledBonuses, hwithin t ht, Function.update_self]
  have heq (j : Fin M) (next : RewardTape N r) : F j (p, next) =
      periodHits η (bonus j) localPick (aux j) r next := by
    change globalPeriodHits η (u j) pick (aux j) start r le_rfl (rewardTapeAppend N start r (p, next)) = _
    rw [globalPeriodHits_append, hprev]
    change periodHits η (fun t => u j (start + t)) localPick (aux j) r next = _
    unfold periodHits
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [boundedTapeTranscript_congr _ _ (bonus j) _ _ (fun t ht => hbonus j t (ht.trans i.isLt))]
  rw [Finset.sum_congr rfl (fun j _ => integral_congr_ae (Filter.Eventually.of_forall (heq j)))]
  exact integral_periodHits_average_le e η hη hη₁ leaf coin (fun t => leafCoin (start + t))
    (selected leaf) localPick hlocal r

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set
open scoped ENNReal

theorem blockLeaf_within {h r : ℕ} (l : Fin (2 ^ h)) {t : ℕ} (ht : t < r) :
    blockLeaf h r (l.val * r + t) = l := by
  apply Fin.ext
  change min ((l.val * r + t) / r) (2 ^ h - 1) = l.val
  have hr : 0 < r := Nat.zero_lt_of_lt ht
  rw [Nat.mul_comm l.val r, Nat.mul_add_div hr, Nat.div_eq_of_lt ht, add_zero, min_eq_left]
  omega

theorem blockLeaf_before {h r : ℕ} (l : Fin (2 ^ h)) {t : ℕ} (ht : t < l.val * r) :
    blockLeaf h r t ≠ l := by
  have hr : 0 < r := by
    by_contra! hn
    simp [Nat.eq_zero_of_le_zero hn] at ht
  have hdiv := (Nat.div_lt_iff_lt_mul hr).mpr ht
  intro he
  have he' := congrArg Fin.val he
  change min (t / r) (2 ^ h - 1) = l.val at he'
  exact hdiv.not_ge (he'.symm.trans_le (min_le_left _ _))

/-- Sum over all rounds by summing over the equal-length periods. -/
theorem sum_blocks {A : Type*} [AddCommMonoid A] (f : ℕ → A) (l r : ℕ) :
    (∑ j : Fin l, ∑ t : Fin r, f (j.val * r + t.val)) = ∑ t ∈ Finset.range (l * r), f t := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Fin.sum_univ_castSucc, Nat.succ_mul, Finset.sum_range_add]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, Fin.sum_univ_eq_sum_range (fun t : ℕ => f (l * r + t))]

theorem integral_finiteTableLaw {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (f : A → ℝ) :
    (∫ a, f a ∂finiteTableLaw A) = (∑ a, f a) / Fintype.card A := by
  rw [finiteTableLaw, integral_smul_measure, integral_count, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, div_eq_inv_mul]

/-- A uniform table can be averaged by fixing it and averaging over a fresh
value at one coordinate. Swap the old value and the fresh value to see this. -/
theorem sum_update_average {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    [DecidableEq A] (a : A) (f : (A → B) → ℝ) :
    (∑ g : A → B, (∑ b : B, f (Function.update g a b)) / Fintype.card B) = ∑ g, f g := by
  classical
  let flip (p : (A → B) × B) := (Function.update p.1 a p.2, p.1 a)
  have hflip : Function.Involutive flip := by
    intro p
    apply Prod.ext
    · funext a'
      by_cases ha : a' = a
      · subst a'
        simp [flip]
      · simp [flip, Function.update_of_ne ha]
    · simp [flip]
  let e : ((A → B) × B) ≃ ((A → B) × B) := ⟨flip, flip, hflip, hflip⟩
  have he := e.sum_comp (fun p => f p.1)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at he
  change (∑ g : A → B, ∑ b : B, f (Function.update g a b)) = ∑ g : A → B, ∑ _ : B, f g at he
  rw [← Finset.sum_div, he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  have hb : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

theorem measurable_with_fixed_table {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [Fintype A] [MeasurableSingletonClass A] {f : A × B → C}
    (hf : ∀ a, Measurable (fun b => f (a, b))) : Measurable f := by
  intro S hS
  have he : f ⁻¹' S = ⋃ a, {a} ×ˢ ((fun b => f (a, b)) ⁻¹' S) := by
    ext ⟨a, b⟩
    simp
  rw [he]
  exact MeasurableSet.iUnion fun a => (measurableSet_singleton a).prod (hf a hS)

theorem measurable_treeEnvironmentAction {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (hm : ∀ t, Measurable (pick t)) (anchor : Fin N) (t : ℕ) :
    Measurable (fun env : TreeEnvironment h M N T => treeEnvironmentAction e active η pick anchor env t) := by
  apply measurable_with_fixed_table
  intro table
  by_cases ht : t < T
  · simp only [treeEnvironmentAction, dif_pos ht]
    exact (hm t).comp ((measurable_rawTapeHistory η (tableBonuses e active table) pick hm t).comp
      (measurable_rewardTapePrefix N ht.le))
  · simp only [treeEnvironmentAction, dif_neg ht]
    exact measurable_const

theorem measurable_treeEnvironmentPlay {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (hm : ∀ t, Measurable (pick t)) (anchor : Fin N) (t : ℕ) (i : Fin N) :
    Measurable (fun env : TreeEnvironment h M N T => treeEnvironmentPlay e active η pick anchor env t i) :=
  (Measurable.of_discrete (f := fun a : Fin N => (Pi.single a (1 : ℝ) : Fin N → ℝ) i)).comp
    (measurable_treeEnvironmentAction e active η pick hm anchor t)

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

private theorem treeTableSum {h M T : ℕ} (f : TreeTables h M T → ℝ) :
    (∑ table, f table) = ∑ b : Fin T → Bool, ∑ c : TreeNode h → Bool,
      ∑ J : Fin (2 ^ h) → Fin M, f (b, c, J) := by
  simp only [Fintype.sum_prod_type]

theorem integrable_treePlayMass {h M U N T : ℕ} [Nonempty (Fin M)]
    (e : Fin N ≃ TreeAction h M U) (active : ℕ → Fin (2 ^ h)) (η : ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (anchor : Fin N) (a : TreeTables h M T → ℕ → Fin N) :
    Integrable (fun env : TreeEnvironment h M N T =>
      ∑ t ∈ Finset.range T, treeEnvironmentPlay e active η pick anchor env t (a env.1 t))
      (treeEnvironmentLaw h M N T) := by
  classical
  apply integrable_finsetSum
  intro t _
  have hq : Measurable (fun env : TreeEnvironment h M N T =>
      treeEnvironmentPlay e active η pick anchor env t (a env.1 t)) := by
    exact measurable_select ((Measurable.of_discrete (f := fun table => a table t)).comp measurable_fst)
      (fun i => measurable_treeEnvironmentPlay e active η pick hm anchor t i)
  apply Integrable.of_bound hq.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro env
  unfold treeEnvironmentPlay
  rw [Pi.single_apply]
  split <;> norm_num

/-- Averaging over all tables, the learner's expected number of selected
auxiliary plays is bounded by the sum of the bounds for each period. -/
theorem tree_expected_selected_hits {h M U N r : ℕ} [Nonempty (Fin M)]
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (hη : 0 ≤ η) (hη₁ : η < 1)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t)) (anchor : Fin N) :
    let L := 2 ^ h
    let T := L * r
    let active := blockLeaf h r
    let P := treeEnvironmentLaw h M N T
    let q := treeEnvironmentPlay (T := T) e active η pick anchor
    (∫ env, ∑ t ∈ Finset.range T, q env t (treeAuxAction e (env.1.2.2 (active t))) ∂P) ≤
      (L : ℝ) * ((r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))) := by
  classical
  intro L T active P q
  let C := TreeTables h M T
  let μ := finiteTableLaw C
  let ν := rewardTapeLaw N T
  let aux := treeAuxAction e
  let u (table : C) := tableBonuses e active table
  let B := (r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))
  let W (env : TreeEnvironment h M N T) := ∑ t ∈ Finset.range T,
    q env t (aux (env.1.2.2 (active t)))
  have hW : Integrable W (μ.prod ν) :=
    integrable_treePlayMass e active η pick hm anchor (fun table t => aux (table.2.2 (active t)))
  have he (l : Fin L) : l.val * r + r ≤ T := by
    have h := Nat.mul_le_mul_right r (Nat.succ_le_of_lt l.isLt)
    rwa [Nat.succ_mul] at h
  let f (l : Fin L) (env : TreeEnvironment h M N T) :=
    globalPeriodHits η (u env.1) pick (aux (env.1.2.2 l)) (l.val * r) r (he l) env.2
  have hf (l : Fin L) : Integrable (f l) (μ.prod ν) := by
    have hm' : Measurable (f l) := by
      apply measurable_with_fixed_table
      intro table
      exact measurable_globalPeriodHits η (u table) pick hm (aux (table.2.2 l)) (l.val * r) r (he l)
    apply Integrable.of_bound hm'.aestronglyMeasurable r
    exact Filter.Eventually.of_forall (fun env => Real.norm_eq_abs _ ▸
      abs_globalPeriodHits η (u env.1) pick (aux (env.1.2.2 l)) (l.val * r) r (he l) env.2)
  have hf_eq (env : TreeEnvironment h M N T) : W env = ∑ l : Fin L, f l env := by
    unfold W
    rw [← sum_blocks (fun t => q env t (aux (env.1.2.2 (active t)))) L r]
    refine Finset.sum_congr rfl fun l _ => ?_
    unfold f globalPeriodHits
    refine Finset.sum_congr rfl fun i _ => ?_
    have ht : l.val * r + i.val < T := (Nat.add_lt_add_left i.isLt _).trans_le (he l)
    have ha : active (l.val * r + i.val) = l := blockLeaf_within l i.isLt
    simp only [q, treeEnvironmentPlay, treeEnvironmentAction, dif_pos ht, Pi.single_apply, ha]
    by_cases hh : pick (l.val * r + i.val) (rawTapeHistory η (u env.1) pick (l.val * r + i.val)
        (rewardTapePrefix N ht.le env.2)) = aux (env.1.2.2 l)
    · simp [hh, u]
    · simp [hh, Ne.symm hh, u]
  have hper (l : Fin L) : (∫ env, f l env ∂μ.prod ν) ≤ B := by
    rw [integral_prod (f l) (hf l), integral_finiteTableLaw]
    apply (div_le_iff₀ (show 0 < (Fintype.card C : ℝ) by exact_mod_cast Fintype.card_pos)).mpr
    rw [treeTableSum]
    have hadd (b : Fin T → Bool) (c : TreeNode h → Bool) :
        (∑ J : Fin (2 ^ h) → Fin M, ∫ tape, f l ((b, c, J), tape) ∂ν) ≤
          ∑ _ : Fin (2 ^ h) → Fin M, B := by
      rw [← sum_update_average l (fun J => ∫ tape, f l ((b, c, J), tape) ∂ν)]
      refine Finset.sum_le_sum fun J _ => ?_
      have hb := tree_global_period_average e η hη hη₁ active l (l.val * r) r (he l)
        (fun _ ht => blockLeaf_before l ht) (fun _ ht => blockLeaf_within l ht)
        c (tableLeafCoin b) J pick hm
      have he' (j : Fin M) : (Function.update J l j) l = j := Function.update_self ..
      simp only [f, u, tableBonuses, aux, treeAuxAction, he'] at *
      rw [Fintype.card_fin]
      exact hb
    have hc := Finset.sum_le_sum (s := Finset.univ) fun b _ =>
      Finset.sum_le_sum (s := Finset.univ) fun c _ => hadd b c
    refine hc.trans_eq ?_
    rw [← treeTableSum (f := fun _ : C => B)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  change ∫ env, W env ∂μ.prod ν ≤ (L : ℝ) * B
  have hw : (fun env => W env) = fun env => ∑ l, f l env := funext hf_eq
  rw [hw, integral_finsetSum _ (fun l _ => hf l)]
  exact (Finset.sum_le_sum (s := Finset.univ) (fun l _ => hper l)).trans_eq (by simp)

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.tree_expected_selected_hits := @CalibeatBandit.tree_expected_selected_hits
