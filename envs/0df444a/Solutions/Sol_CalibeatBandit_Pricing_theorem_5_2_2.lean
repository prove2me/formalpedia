-- Prove2me | solution 2 for CalibeatBandit.Pricing.theorem_5_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T17:43:09.532143+00:00
-- url     : https://prove2.me/submissions/16084658-3fb2-4491-a469-3194f91ef4ac

import Mathlib
import Definitions.Def_CalibeatBandit_lower_bound_models
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_hard_tree_environment
import Theorems.Thm_CalibeatBandit_exists_hard_tree_environment
import Theorems.Thm_CalibeatBandit_tree_scale_threshold

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

namespace CalibeatBandit

open Set MeasureTheory

/-- In every realization, the selected auxiliary action is a revenue
maximizer. This is the input used by the pricing reduction. -/
theorem bonusReward_le_selected {η : ℝ} (hη : 0 ≤ η) (z : Icc (0 : ℝ) 1) (hit : Bool) :
    bonusReward η z hit ≤ bonusReward η z true := by
  have hb : 0 ≤ η / 8 * (z : ℝ) * (1 - (z : ℝ)) :=
    mul_nonneg (mul_nonneg (by positivity) z.property.1) (sub_nonneg.mpr z.property.2)
  cases hit <;> simp [bonusReward, hb]

theorem treeReward_max {h M U : ℕ} {η : ℝ} (hη : 0 ≤ η) (leaf : Fin (2 ^ h))
    (coin : TreeNode h → Bool) (leafCoin : Bool) (selected : Fin M) (z : Icc (0 : ℝ) 1)
    (draw : TreeAction h M U → Ico (0 : ℝ) 1) (a : TreeAction h M U) :
    treeReward η leaf coin leafCoin selected z draw a ≤
      treeReward η leaf coin leafCoin selected z draw (.inr (.inl selected)) := by
  have hc : (draw (.inr (.inl selected)) : ℝ) <
      treeBonusProb (U := U) leaf coin leafCoin selected (.inr (.inl selected)) := by
    simpa [treeBonusProb] using (draw (.inr (.inl selected))).property.2
  exact (bonusReward_le_selected hη z _).trans_eq (by simp [treeReward, hc])

theorem card_treeNode (h : ℕ) : Fintype.card (TreeNode h) = 2 ^ (h + 1) - 1 := by
  simp only [TreeNode, Fintype.card_sigma, Fintype.card_fin, Fin.sum_univ_eq_sum_range]
  induction h with
  | zero => norm_num
  | succ h ih =>
    rw [Finset.sum_range_succ, ih, pow_succ (2 : ℕ) (h + 1)]
    have hp : 0 < (2 : ℕ) ^ (h + 1) := by positivity
    omega

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

theorem rewardTapePrefix_comp (N : ℕ) {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    rewardTapePrefix N hrs ∘ rewardTapePrefix N hst = rewardTapePrefix N (hrs.trans hst) := by
  induction hst with
  | refl => simp
  | step hs ih =>
    rw [rewardTapePrefix_succ N hs, rewardTapePrefix_succ N (hrs.trans hs)]
    funext tape
    exact congrFun ih tape.1

open scoped ENNReal

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

theorem rawTapeHistory_eq_feedbackHistory {N T : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (tape : RewardTape N T) (t : ℕ) (ht : t ≤ T) :
    rawTapeHistory η u pick t (rewardTapePrefix N ht tape) =
      feedbackHistory pick (fun s i => boundedRoundReward η (u s i) i (tapeDraw tape s)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he : (rewardTapePrefix N ht tape).1 = rewardTapePrefix N ((Nat.le_succ t).trans ht) tape := by
      have hf : rewardTapePrefix N (Nat.le_succ t) = (Prod.fst : RewardTape N (t + 1) → RewardTape N t) := by
        rw [rewardTapePrefix_succ N (le_refl t), rewardTapePrefix_refl, Function.id_comp]
      have hc := congrFun (rewardTapePrefix_comp N (Nat.le_succ t) ht) tape
      rw [hf] at hc
      exact hc
    have hdraw : tapeDraw tape t = (rewardTapePrefix N ht tape).2 := by
      simp only [tapeDraw, dif_pos (Nat.lt_of_succ_le ht)]
    have hhist := ih ((Nat.le_succ t).trans ht)
    simp only [rawTapeHistory, feedbackHistory, he, hhist, hdraw]
    rfl

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set Filter

theorem swapRegret_congr_before {N T : ℕ} {y y' : ℕ → Fin N → ℝ}
    {I I' : ℕ → Fin N}
    (hy : ∀ t < T, ∀ i, y t i = y' t i) (hI : ∀ t < T, I t = I' t) :
    swapRegret T y I = swapRegret T y' I' := by
  unfold swapRegret
  congr 1
  funext f
  exact Finset.sum_congr rfl fun t ht => by
    have ht' := Finset.mem_range.mp ht
    rw [hI t ht', hy t ht', hy t ht']

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set Filter

theorem tree_horizon_eq (h : ℕ) :
    2 ^ h * treePeriodLength h = treeActionBudget h ^ 4 := by
  unfold treePeriodLength treeActionBudget
  ring

theorem treeBonusScale_pos (h : ℕ) : 0 < treeBonusScale h := by unfold treeBonusScale treeActionBudget treeHeight; positivity

theorem treeBonusScale_le_inv_actions {h N : ℕ} (hN : N ≤ 2 * treeActionBudget h) (hn : 0 < N) :
    treeBonusScale h ≤ 1 / (N : ℝ) := by
  unfold treeBonusScale
  apply div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hn)
  have he : (N : ℝ) ≤ 2 * (treeActionBudget h : ℝ) := by exact_mod_cast hN
  have hh : 1 ≤ treeHeight h := by unfold treeHeight; linarith only [Nat.cast_nonneg (α := ℝ) h]
  have hk : 0 ≤ (treeActionBudget h : ℝ) := by positivity
  nlinarith only [he, hk, mul_nonneg hk (sub_nonneg.mpr hh)]

/-- An exact action budget of 16 times the number of leaves. -/
theorem treeActionEquiv_exact (h : ℕ) :
    ∃ U : ℕ, Nonempty (Fin (treeActionBudget h) ≃ TreeAction h (8 * 2 ^ h) U) := by
  let A := (2 ^ (h + 1) - 1) * 2 + 8 * 2 ^ h
  have hA : A ≤ treeActionBudget h := by unfold A treeActionBudget; rw [pow_succ]; omega
  refine ⟨treeActionBudget h - A, ⟨Fintype.equivOfCardEq ?_⟩⟩
  simp only [TreeAction, Fintype.card_fin, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool,
    card_treeNode]
  unfold A at hA ⊢
  omega

end CalibeatBandit

end

section

set_option autoImplicit false

open scoped BigOperators

namespace CalibeatBandit.Pricing

theorem abs_revenue_le_one (cost : Price) (demand : Demand) (p : Price) :
    |revenue cost demand p| ≤ 1 := by
  rw [revenue, abs_mul, abs_of_nonneg (demand p).property.1]
  apply (mul_le_of_le_one_right (abs_nonneg _) (demand p).property.2).trans
  exact abs_le.mpr ⟨by linarith [p.property.1, cost.property.2],
    by linarith [p.property.2, cost.property.1]⟩

theorem benchmark_bddAbove (T : ℕ) (cost : Price) (demand : ℕ → Demand)
    (reference posted : ℕ → Price) :
    BddAbove {g | ∃ f : Price → Price, Measurable f ∧
      g = ∑ t ∈ Finset.range T, (revenue cost (demand t) (f (reference t)) -
        revenue cost (demand t) (posted t))} := by
  refine ⟨(T : ℝ) * 2, ?_⟩
  rintro _ ⟨f, _, rfl⟩
  calc
    _ ≤ ∑ _ ∈ Finset.range T, (2 : ℝ) := Finset.sum_le_sum fun t _ => by
      have h₁ := abs_le.mp (abs_revenue_le_one cost (demand t) (f (reference t)))
      have h₂ := abs_le.mp (abs_revenue_le_one cost (demand t) (posted t))
      linarith
    _ = _ := by simp

theorem comparison_le_benchmark {T : ℕ} {cost : Price} {demand : ℕ → Demand}
    {reference posted : ℕ → Price} {f : Price → Price} (hf : Measurable f) :
    ∑ t ∈ Finset.range T, (revenue cost (demand t) (f (reference t)) -
      revenue cost (demand t) (posted t)) ≤ benchmark T cost demand reference posted :=
  le_csSup (benchmark_bddAbove T cost demand reference posted) ⟨f, hf, rfl⟩

theorem exists_measurable_price_remapping {ι : Type*} [Fintype ι]
    (price : ι → Price) (hprice : Function.Injective price) (target : ι → Price) :
    ∃ f : Price → Price, Measurable f ∧ f ∘ price = target := by
  let _ : MeasurableSpace ι := ⊤
  have _ : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have hEmbed : MeasurableEmbedding price :=
    ⟨hprice, measurable_of_finite price, fun s _ => (s.toFinite.image price).measurableSet⟩
  exact hEmbed.exists_measurable_extend (measurable_of_finite target) (fun p => ⟨p⟩)

end CalibeatBandit.Pricing

end

section

set_option autoImplicit false

open scoped BigOperators

namespace CalibeatBandit.Pricing

/-- The upper endpoints of the demand intervals in Theorem 5.2. -/
noncomputable def intervalPrice {n : ℕ} (i : Fin (n + 1)) : Price :=
  ⟨1 / 2 + ((i : ℕ) + 1 : ℝ) / (4 * (n + 1)), by
    have hi : ((i : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      exact_mod_cast (show (i : ℕ) + 1 ≤ n + 1 by omega)
    have hd : 0 < 4 * ((n : ℝ) + 1) := by positivity
    have h : (((i : ℕ) : ℝ) + 1) / (4 * ((n : ℝ) + 1)) ≤ 1 / 4 := by
      apply (div_le_iff₀ hd).mpr
      linarith
    exact ⟨by positivity, by linarith⟩⟩

theorem intervalPrice_pos {n : ℕ} (i : Fin (n + 1)) : 0 < (intervalPrice i : ℝ) := by
  unfold intervalPrice
  positivity

theorem intervalPrice_bounds {n : ℕ} (i : Fin (n + 1)) :
    (1 / 2 : ℝ) ≤ intervalPrice i ∧ (intervalPrice i : ℝ) ≤ 3 / 4 := by
  have hi : ((i : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast (show (i : ℕ) + 1 ≤ n + 1 by omega)
  have hd : 0 < 4 * ((n : ℝ) + 1) := by positivity
  have h := (div_le_iff₀ hd).mpr (show ((i : ℕ) : ℝ) + 1 ≤
      1 / 4 * (4 * ((n : ℝ) + 1)) by linarith)
  change (1 / 2 : ℝ) ≤ 1 / 2 + (((i : ℕ) : ℝ) + 1) / (4 * (n + 1)) ∧
    1 / 2 + (((i : ℕ) : ℝ) + 1) / (4 * (n + 1)) ≤ 3 / 4
  exact ⟨le_add_of_nonneg_right (by positivity), by linarith⟩

theorem intervalPrice_succ_sub {n : ℕ} (i : Fin n) :
    (intervalPrice i.succ : ℝ) - intervalPrice i.castSucc = 1 / (4 * ((n : ℝ) + 1)) := by
  change (1 / 2 + (((i.succ : ℕ) : ℝ) + 1) / (4 * ((n : ℝ) + 1))) -
    (1 / 2 + (((i.castSucc : ℕ) : ℝ) + 1) / (4 * ((n : ℝ) + 1))) = _
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

/-- The lower-bound rewards yield a non-increasing demand. The argument
allows any realization of the bonus indicators in one round. -/
theorem interval_ratios_of_rewards {n : ℕ} {z η : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hη : 0 ≤ η) (hη' : η ≤ 1 / ((n : ℝ) + 1))
    (bonus : Fin (n + 1) → Bool) :
    let y := fun i => 1 / 8 + z / 8 + (η / 8 * z * (1 - z)) * (if bonus i then 1 else 0)
    (∀ i, y i / (intervalPrice i : ℝ) ∈ Set.Icc (0 : ℝ) 1) ∧
      Antitone (fun i => y i / (intervalPrice i : ℝ)) := by
  intro y
  let base := 1 / 8 + z / 8
  let bonusSize := η / 8 * z * (1 - z)
  have hz₀ : 0 ≤ z := hz.1
  have hz₁ : z ≤ 1 := hz.2
  have hb₀ : 0 ≤ bonusSize := by
    dsimp [bonusSize]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hz₁)
  have hb₁ : bonusSize ≤ η / 32 := by
    have h := mul_le_mul_of_nonneg_left (show z * (1 - z) ≤ 1 / 4 by
      nlinarith [sq_nonneg (z - 1 / 2)]) (show 0 ≤ η / 8 by positivity)
    dsimp [bonusSize]
    nlinarith only [h]
  have hr (i : Fin (n + 1)) : base ≤ y i ∧ y i ≤ base + bonusSize := by
    change base ≤ base + bonusSize * (if bonus i then 1 else 0) ∧
      base + bonusSize * (if bonus i then 1 else 0) ≤ base + bonusSize
    cases bonus i <;> simp [hb₀]
  have hη₁ : η ≤ 1 := hη'.trans ((div_le_one (by positivity)).mpr (by
    have h : 0 ≤ (n : ℝ) := by positivity
    linarith))
  have hbase : 1 / 8 ≤ base := le_add_of_nonneg_right (by positivity)
  have hbase' : base ≤ 1 / 4 := by dsimp [base]; linarith
  constructor
  · intro i
    have hp := intervalPrice_bounds i
    exact ⟨div_nonneg (by linarith [(hr i).1]) (intervalPrice_pos i).le,
      (div_le_one (intervalPrice_pos i)).mpr (by linarith [(hr i).2, hp.1])⟩
  · apply Fin.antitone_iff_succ_le.mpr
    intro i
    apply (div_le_div_iff₀ (intervalPrice_pos i.succ) (intervalPrice_pos i.castSucc)).mpr
    let p : ℝ := intervalPrice i.castSucc
    let q : ℝ := intervalPrice i.succ
    have hp₀ : 0 ≤ p := (intervalPrice_pos i.castSucc).le
    have hq₀ : 0 ≤ q := (intervalPrice_pos i.succ).le
    have hp₁ : p ≤ 1 := (intervalPrice i.castSucc).property.2
    have hdiff : q - p = 1 / (4 * ((n : ℝ) + 1)) := intervalPrice_succ_sub i
    have hdiff₀ : 0 ≤ q - p := by rw [hdiff]; positivity
    change y i.succ * p ≤ y i.castSucc * q
    calc
      _ ≤ (base + bonusSize) * p := mul_le_mul_of_nonneg_right (hr i.succ).2 hp₀
      _ = base * p + bonusSize * p := add_mul _ _ _
      _ ≤ base * p + bonusSize := add_le_add_right (mul_le_of_le_one_right hb₀ hp₁) _
      _ ≤ base * p + base * (q - p) := by
        apply add_le_add_right
        calc
          _ ≤ η / 32 := hb₁
          _ ≤ (1 / 8) * (q - p) := by
            rw [hdiff, show (1 / 8 : ℝ) * (1 / (4 * ((n : ℝ) + 1))) =
              (1 / ((n : ℝ) + 1)) / 32 by
                field_simp
                ring]
            exact div_le_div_of_nonneg_right hη' (by norm_num)
          _ ≤ base * (q - p) :=
            mul_le_mul_of_nonneg_right hbase hdiff₀
      _ = base * q := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hr i.castSucc).1 hq₀

theorem intervalPrice_strictMono (n : ℕ) : StrictMono (@intervalPrice n) := by
  intro i j hij
  change 1 / 2 + (((i : ℕ) : ℝ) + 1) / (4 * (n + 1)) <
    1 / 2 + (((j : ℕ) : ℝ) + 1) / (4 * (n + 1))
  have h : ((i : ℕ) : ℝ) < j := by exact_mod_cast hij
  exact add_lt_add_right (div_lt_div_of_pos_right (by linarith) (by positivity)) _

/-- Assign a posted price to the first interval whose upper endpoint covers it.
The convention at zero and above the last endpoint is the first action. -/
noncomputable def intervalIndex (n : ℕ) (p : Price) : Fin (n + 1) := by
  classical
  let s := Finset.univ.filter (fun i : Fin (n + 1) => p ≤ intervalPrice i)
  exact if h : zeroPrice < p ∧ s.Nonempty then s.min' h.2 else 0

private theorem intervalIndex_spec {n : ℕ} {p : Price} (hp : zeroPrice < p)
    (h : ∃ i : Fin (n + 1), p ≤ intervalPrice i) :
    p ≤ intervalPrice (intervalIndex n p) ∧
      ∀ j : Fin (n + 1), j < intervalIndex n p → intervalPrice j < p := by
  classical
  let s := Finset.univ.filter (fun i : Fin (n + 1) => p ≤ intervalPrice i)
  obtain ⟨i, hi⟩ := h
  have hs : s.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have he : intervalIndex n p = s.min' hs := dif_pos ⟨hp, hs⟩
  rw [he]
  refine ⟨(Finset.mem_filter.mp (Finset.min'_mem s hs)).2, fun j hj => ?_⟩
  by_contra! hge
  exact (not_lt_of_ge (Finset.min'_le s j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hge⟩))) hj

private theorem intervalIndex_mono_of_covered {n : ℕ} {p q : Price} (hp : zeroPrice < p)
    (hpq : p ≤ q) (hq : ∃ i : Fin (n + 1), q ≤ intervalPrice i) :
    intervalIndex n p ≤ intervalIndex n q := by
  have hq' := (intervalIndex_spec (hp.trans_le hpq) hq).1
  have hs := intervalIndex_spec hp ⟨_, hpq.trans hq'⟩
  by_contra! h
  exact not_lt_of_ge (hpq.trans hq') (hs.2 _ h)

theorem intervalIndex_intervalPrice {n : ℕ} (i : Fin (n + 1)) :
    intervalIndex n (intervalPrice i) = i := by
  have hp : zeroPrice < intervalPrice i := intervalPrice_pos i
  have h := intervalIndex_spec hp ⟨i, le_rfl⟩
  apply le_antisymm
  · by_contra! hi
    exact (lt_irrefl _ (h.2 i hi))
  · exact (intervalPrice_strictMono n).le_iff_le.mp h.1

theorem intervalIndex_measurable (n : ℕ) : Measurable (intervalIndex n) := by
  classical
  apply measurable_to_countable'
  intro i
  have hi (j : Fin (n + 1)) : MeasurableSet {p : Price | p ≤ intervalPrice j} :=
    measurableSet_le measurable_id measurable_const
  have hp : MeasurableSet {p : Price | zeroPrice < p} :=
    measurableSet_lt measurable_const measurable_id
  let above : Set Price := {p | ∀ j : Fin (n + 1), intervalPrice j < p}
  have ha : MeasurableSet above := by
    have he : above = ⋂ j : Fin (n + 1), {p : Price | intervalPrice j < p} := by ext p; simp [above]
    rw [he]
    exact MeasurableSet.iInter fun _ => measurableSet_lt measurable_const measurable_id
  let cell : Set Price := {p | zeroPrice < p ∧ p ≤ intervalPrice i ∧
    ∀ j : Fin (n + 1), j < i → intervalPrice j < p}
  have hcell : MeasurableSet cell := by
    have he : cell = {p : Price | zeroPrice < p} ∩ {p : Price | p ≤ intervalPrice i} ∩
        (⋂ j : {j : Fin (n + 1) // j < i}, {p : Price | intervalPrice j.val < p}) := by
      ext p
      simp only [cell, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Subtype.forall]
      tauto
    rw [he]
    exact (hp.inter (hi i)).inter (MeasurableSet.iInter fun _ => measurableSet_lt measurable_const measurable_id)
  have outside (p : Price) (h : ¬ (zeroPrice < p ∧ ∃ j : Fin (n + 1), p ≤ intervalPrice j)) :
      intervalIndex n p = 0 := by
    unfold intervalIndex
    apply dif_neg
    rintro ⟨hp, j, hj⟩
    exact h ⟨hp, j, (Finset.mem_filter.mp hj).2⟩
  have regular (p : Price) (h : zeroPrice < p ∧ ∃ j : Fin (n + 1), p ≤ intervalPrice j) :
      intervalIndex n p = i ↔ p ∈ cell := by
    obtain ⟨hc, hm⟩ := intervalIndex_spec h.1 h.2
    constructor
    · intro he
      exact ⟨h.1, he ▸ hc, he ▸ hm⟩
    · rintro ⟨_, hi, hmin⟩
      rcases lt_trichotomy (intervalIndex n p) i with hl | he | hg
      · exact (not_lt_of_ge hc (hmin _ hl)).elim
      · exact he
      · exact (not_lt_of_ge hi (hm _ hg)).elim
  have he : (intervalIndex n ⁻¹' {i}) = cell ∪
      (if i = 0 then ({p : Price | zeroPrice < p}ᶜ ∪ above) else ∅) := by
    ext p
    by_cases h : zeroPrice < p ∧ ∃ j : Fin (n + 1), p ≤ intervalPrice j
    · have hn : p ∉ above := by
        obtain ⟨j, hj⟩ := h.2
        exact fun ha => not_lt_of_ge hj (ha j)
      simpa [h.1, hn, Set.mem_preimage, Set.mem_singleton_iff] using regular p h
    · have heq := outside p h
      have hncell : p ∉ cell := fun hp => h ⟨hp.1, i, hp.2.1⟩
      have hnot : p ∈ {p : Price | zeroPrice < p}ᶜ ∪ above := by
        by_cases hpos : zeroPrice < p
        · exact Or.inr fun j => lt_of_not_ge fun hj => h ⟨hpos, j, hj⟩
        · exact Or.inl hpos
      by_cases hi : i = 0 <;> simp [heq, hncell, hnot, hi, eq_comm]
  rw [he]
  exact hcell.union (by split <;> simp_all only [MeasurableSet.empty, MeasurableSet.union, MeasurableSet.compl])

/-- The deterministic payoff comparison in Claim 5.3, for every realization
of the prices proposed by the simulated pricing algorithm. -/
theorem swapRegret_le_pricing {n T : ℕ}
    (index : Price → Fin (n + 1)) (hindex : Measurable index)
    (price : Fin (n + 1) → Price) (d : ℕ → Demand)
    (y : ℕ → Fin (n + 1) → ℝ) (posted : ℕ → Price)
    (hat : ∀ t < T, ∀ j, revenue zeroPrice (d t) (price j) = y t j)
    (hposted : ∀ t < T, revenue zeroPrice (d t) (posted t) ≤ y t (index (posted t))) :
    swapRegret T y (fun t => index (posted t)) ≤ benchmark T zeroPrice d posted posted := by
  unfold swapRegret
  refine Finset.sup'_le _ _ fun f _ => ?_
  let g : Price → Price := fun p => price (f (index p))
  have hg : Measurable g := (measurable_of_finite (fun j => price (f j))).comp hindex
  refine le_trans (Finset.sum_le_sum (fun t ht => ?_))
    (comparison_le_benchmark (T := T) (cost := zeroPrice) (demand := d)
      (reference := posted) (posted := posted) (f := g) hg)
  change y t (f (index (posted t))) - y t (index (posted t)) ≤
    revenue zeroPrice (d t) (price (f (index (posted t)))) - revenue zeroPrice (d t) (posted t)
  rw [hat t (Finset.mem_range.mp ht)]
  exact sub_le_sub_left (hposted t (Finset.mem_range.mp ht)) _

/-- Step demand with the designated revenues at interval endpoints.
The hypotheses are on the ratios of revenue to endpoint price. -/
noncomputable def intervalDemand {n : ℕ} (y : Fin (n + 1) → ℝ)
    (hy : ∀ i, y i / (intervalPrice i : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (hanti : Antitone fun i => y i / (intervalPrice i : ℝ)) : Demand := by
  classical
  let d (p : Price) : Price :=
    if p = zeroPrice then ⟨1, by norm_num, by norm_num⟩
    else if ∃ i : Fin (n + 1), p ≤ intervalPrice i then
      ⟨y (intervalIndex n p) / (intervalPrice (intervalIndex n p) : ℝ), hy _⟩
    else zeroPrice
  refine ⟨d, fun p q hpq => ?_⟩
  by_cases hp : p = zeroPrice
  · change (d q : ℝ) ≤ d p
    simpa [d, hp] using (d q).property.2
  have hp₀ : zeroPrice < p := lt_of_le_of_ne p.property.1 (Ne.symm hp)
  have hq : q ≠ zeroPrice := ne_of_gt (hp₀.trans_le hpq)
  by_cases hc : ∃ i : Fin (n + 1), q ≤ intervalPrice i
  · have hc' : ∃ i : Fin (n + 1), p ≤ intervalPrice i := by
      obtain ⟨i, hi⟩ := hc
      exact ⟨i, hpq.trans hi⟩
    change (d q : ℝ) ≤ d p
    simpa only [d, if_neg hp, if_neg hq, if_pos hc, if_pos hc'] using
      hanti (intervalIndex_mono_of_covered hp₀ hpq hc)
  · change (d q : ℝ) ≤ d p
    have hzero : d q = zeroPrice := by simp only [d, if_neg hq, if_neg hc]
    rw [hzero]
    exact (d p).property.1

theorem intervalDemand_feedback {n : ℕ} (y : Fin (n + 1) → ℝ)
    (hy : ∀ i, y i / (intervalPrice i : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (hanti : Antitone fun i => y i / (intervalPrice i : ℝ)) (p : Price) :
    revenue zeroPrice (intervalDemand y hy hanti) p =
      if zeroPrice < p ∧ (∃ i : Fin (n + 1), p ≤ intervalPrice i)
      then ((p : ℝ) / (intervalPrice (intervalIndex n p) : ℝ)) * y (intervalIndex n p)
      else 0 := by
  classical
  by_cases hp : p = zeroPrice
  · subst p
    simp [revenue]
  have hp₀ : zeroPrice < p := lt_of_le_of_ne p.property.1 (Ne.symm hp)
  by_cases hc : ∃ i : Fin (n + 1), p ≤ intervalPrice i
  · unfold revenue
    simp only [intervalDemand, hp, hc, hp₀, and_self, if_true, if_false,
      show (zeroPrice : ℝ) = 0 from rfl, sub_zero]
    ring
  · have hzero : intervalDemand y hy hanti p = zeroPrice := by
      simp only [intervalDemand, if_neg hp, if_neg hc]
    rw [if_neg (fun h => hc h.2), revenue, hzero]
    exact mul_zero _

theorem intervalDemand_endpoint {n : ℕ} (y : Fin (n + 1) → ℝ)
    (hy : ∀ i, y i / (intervalPrice i : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (hanti : Antitone fun i => y i / (intervalPrice i : ℝ)) (i : Fin (n + 1)) :
    revenue zeroPrice (intervalDemand y hy hanti) (intervalPrice i) = y i := by
  rw [intervalDemand_feedback, if_pos ⟨intervalPrice_pos i, ⟨i, le_rfl⟩⟩,
    intervalIndex_intervalPrice, div_self (intervalPrice_pos i).ne', one_mul]

theorem intervalDemand_revenue_le {n : ℕ} (y : Fin (n + 1) → ℝ)
    (hy : ∀ i, y i / (intervalPrice i : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (hanti : Antitone fun i => y i / (intervalPrice i : ℝ)) (p : Price) :
    revenue zeroPrice (intervalDemand y hy hanti) p ≤ y (intervalIndex n p) := by
  classical
  have hnonneg := ((div_nonneg_iff.mp (hy (intervalIndex n p)).1).resolve_right
    (fun h => (not_le_of_gt (intervalPrice_pos (intervalIndex n p))) h.2)).1
  rw [intervalDemand_feedback]
  split
  · rename_i h
    exact mul_le_of_le_one_left hnonneg ((div_le_one (intervalPrice_pos _)).mpr
      (intervalIndex_spec h.1 h.2).1)
  · exact hnonneg

/-- The simulation observes just the reward of the chosen discrete action.
The rescaled observation is exactly the revenue at the proposed price, and
the continuous swap regret dominates the simulated discrete swap regret. -/
theorem claim_5_3_pathwise {n T : ℕ} (y : ℕ → Fin (n + 1) → ℝ)
    (hy : ∀ t i, y t i / (intervalPrice i : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (hanti : ∀ t, Antitone fun i => y t i / (intervalPrice i : ℝ))
    (posted : ℕ → Price) :
    swapRegret T y (fun t => intervalIndex n (posted t)) ≤
      benchmark T zeroPrice (fun t => intervalDemand (y t) (hy t) (hanti t)) posted posted :=
  swapRegret_le_pricing (intervalIndex n) (intervalIndex_measurable n) intervalPrice
    (fun t => intervalDemand (y t) (hy t) (hanti t)) y posted
    (fun t _ => intervalDemand_endpoint (y t) (hy t) (hanti t))
    (fun t _ => intervalDemand_revenue_le (y t) (hy t) (hanti t) (posted t))

/-- If a measurable remapping of recommendations achieves the maximum revenue
in each round, the recommendation loss dominates swap regret. -/
theorem swap_le_recommendation_of_maximizer {T : ℕ} {d : ℕ → Demand}
    {cost : Price} {recommended posted : ℕ → Price} {f : Price → Price}
    (hf : Measurable f)
    (hmax : ∀ t < T, ∀ p, revenue cost (d t) p ≤ revenue cost (d t) (f (recommended t))) :
    benchmark T cost d posted posted ≤ benchmark T cost d recommended posted := by
  apply csSup_le
  · exact ⟨_, id, measurable_id, rfl⟩
  rintro _ ⟨g, _, rfl⟩
  exact (Finset.sum_le_sum fun t ht => sub_le_sub_right
    (hmax t (Finset.mem_range.mp ht) (g (posted t))) (revenue cost (d t) (posted t))).trans
      (comparison_le_benchmark (reference := recommended) (posted := posted) hf)

/-- If each recommendation label identifies a maximizing action, the same
discrete lower bound transfers to both pricing benchmarks. -/
theorem swapRegret_le_both_pricing_benchmarks {n T : ℕ} {ι : Type*} [Fintype ι]
    (y : ℕ → Fin (n + 1) → ℝ)
    (hy : ∀ t i, y t i / (intervalPrice i : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (hanti : ∀ t, Antitone fun i => y t i / (intervalPrice i : ℝ))
    (posted : ℕ → Price) (label : ℕ → ι) (recommended : ι → Price)
    (hrec : Function.Injective recommended) (best : ι → Fin (n + 1))
    (hbest : ∀ t < T, ∀ i, y t i ≤ y t (best (label t))) :
    let d := fun t => intervalDemand (y t) (hy t) (hanti t)
    let bandit := swapRegret T y (fun t => intervalIndex n (posted t))
    bandit ≤ benchmark T zeroPrice d posted posted ∧
    bandit ≤ benchmark T zeroPrice d (fun t => recommended (label t)) posted := by
  intro d bandit
  obtain ⟨f, hf, heq⟩ := exists_measurable_price_remapping recommended hrec
    (fun j => intervalPrice (best j))
  have hmax (t : ℕ) (ht : t < T) (p : Price) :
      revenue zeroPrice (d t) p ≤ revenue zeroPrice (d t) (f (recommended (label t))) := by
    change _ ≤ revenue zeroPrice (intervalDemand (y t) (hy t) (hanti t))
      ((f ∘ recommended) (label t))
    rw [heq, intervalDemand_endpoint]
    exact (intervalDemand_revenue_le (y t) (hy t) (hanti t) p).trans (hbest t ht _)
  have hs : bandit ≤ benchmark T zeroPrice d posted posted := claim_5_3_pathwise y hy hanti posted
  exact ⟨hs, hs.trans (swap_le_recommendation_of_maximizer hf hmax)⟩

/-- Appending rounds with zero revenue preserves both comparison benchmarks. -/
theorem benchmark_eq_of_zero_tail {T T' : ℕ} (hT : T ≤ T') (cost : Price)
    (d : ℕ → Demand) (reference posted : ℕ → Price)
    (hzero : ∀ t, T ≤ t → t < T' → ∀ p, revenue cost (d t) p = 0) :
    benchmark T' cost d reference posted = benchmark T cost d reference posted := by
  have hs (f : Price → Price) : (∑ t ∈ Finset.range T',
      (revenue cost (d t) (f (reference t)) - revenue cost (d t) (posted t))) =
      ∑ t ∈ Finset.range T, (revenue cost (d t) (f (reference t)) -
        revenue cost (d t) (posted t)) := by
    symm
    apply Finset.sum_subset (Finset.range_mono hT)
    intro t ht' ht
    have h := hzero t (Nat.le_of_not_lt fun h => ht (Finset.mem_range.mpr h))
      (Finset.mem_range.mp ht')
    rw [h, h, sub_zero]
  unfold benchmark
  simp_rw [hs]

/-- At the sparsity used by the lower-bound construction, the two pricing
rates are bounded by the same fourth-power scale after padding the horizon. -/
theorem pricing_rate_le_fourth_power {K N T : ℕ} (hN : 0 < N) (hK : K ≤ N)
    (hT : T ≤ 16 * N ^ 4) :
    (T : ℝ) ^ (3 / 4 : ℝ) + (K : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ) ≤
      16 * (N : ℝ) ^ 3 := by
  have hN₀ : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hT' : (T : ℝ) ≤ 16 * (N : ℝ) ^ 4 := by exact_mod_cast hT
  have hK' : (K : ℝ) ≤ N := by exact_mod_cast hK
  have h16 : (16 : ℝ) ^ (3 / 4 : ℝ) = 8 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast 2 4,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  have hpow (x : ℝ) : ((N : ℝ) ^ (4 : ℕ)) ^ x = (N : ℝ) ^ (4 * x) := by
    rw [← Real.rpow_natCast (N : ℝ) 4, ← Real.rpow_mul hN₀]
    norm_num
  have hfirst : (T : ℝ) ^ (3 / 4 : ℝ) ≤ 8 * (N : ℝ) ^ 3 := by
    calc
      _ ≤ (16 * (N : ℝ) ^ 4) ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg T) hT' (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (by positivity), h16, hpow]
        norm_num [Real.rpow_ofNat]
  have hsecond : (K : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ) ≤ 8 * (N : ℝ) ^ 3 := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) * (16 * (N : ℝ) ^ 4) ^ (2 / 3 : ℝ) :=
        mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg K) hK' (by norm_num))
          (Real.rpow_le_rpow (Nat.cast_nonneg T) hT' (by norm_num)) (by positivity) (by positivity)
      _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) * (8 * (N : ℝ) ^ (4 * (2 / 3) : ℝ)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), hpow]
        gcongr
        rw [← h16]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by
        rw [mul_left_comm, ← Real.rpow_add (by exact_mod_cast hN)]
        norm_num [Real.rpow_ofNat]
  linarith only [hfirst, hsecond]

/-- The distinct recommendation prices in the construction, one per period. -/
noncomputable def periodPrice {L T : ℕ} (hLT : 4 * L ≤ T) (l : Fin L) : Price :=
  ⟨3 / 4 + (((l : ℕ) : ℝ) + 1) / T, by
    have hpos := l.isLt
    have hT : 0 < (T : ℝ) := by exact_mod_cast (show 0 < T by omega)
    have hL : (4 : ℝ) * L ≤ T := by exact_mod_cast hLT
    have hl : (((l : ℕ) : ℝ) + 1) ≤ L := by
      exact_mod_cast (Nat.succ_le_of_lt l.isLt)
    have hb : (((l : ℕ) : ℝ) + 1) / T ≤ 1 / 4 := by
      apply (div_le_iff₀ hT).mpr
      linarith
    exact ⟨by positivity, by linarith⟩⟩

theorem periodPrice_injective {L T : ℕ} (hLT : 4 * L ≤ T) :
    Function.Injective (periodPrice hLT) := by
  intro i j he
  have hpos := i.isLt
  have hT : (T : ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  have h := congrArg Subtype.val he
  change 3 / 4 + (((i : ℕ) : ℝ) + 1) / T =
    3 / 4 + (((j : ℕ) : ℝ) + 1) / T at h
  have hs := (div_left_inj' hT).mp (add_left_cancel h)
  apply Fin.ext
  exact_mod_cast (show (((i : ℕ) : ℝ)) = ((j : ℕ) : ℝ) by linarith)

end CalibeatBandit.Pricing

end

section

set_option autoImplicit false

namespace CalibeatBandit.Pricing

open MeasureTheory Set

/-- A remapping specified at the prices appearing over a finite horizon
extends to a measurable map if equal input prices have equal outputs. -/
theorem measurable_remapping_of_coherence {ι : Type*} [Fintype ι]
    (ref target : ι → Price) (h : ∀ i j, ref i = ref j → target i = target j) :
    ∃ f : Price → Price, Measurable f ∧ f ∘ ref = target := by
  classical
  let _ : Fintype (range ref) := (finite_range ref).fintype
  let g (p : range ref) := target (Classical.choose p.property)
  obtain ⟨f, hf, he⟩ := exists_measurable_price_remapping
    (fun x : range ref => x.val) Subtype.coe_injective g
  refine ⟨f, hf, funext fun i => ?_⟩
  let p : range ref := ⟨ref i, mem_range_self i⟩
  exact (congrFun he p).trans (h _ i (Classical.choose_spec p.property))

/-- Maximum over the finitely many endpoint remappings in an interval
demand instance, using one index for each round of the reference history. -/
theorem benchmark_interval_eq_finite {n T : ℕ}
    (y : ℕ → Fin (n + 1) → ℝ)
    (hy : ∀ t i, y t i / (intervalPrice i : ℝ) ∈ Icc (0 : ℝ) 1)
    (hanti : ∀ t, Antitone fun i => y t i / (intervalPrice i : ℝ))
    (ref posted : ℕ → Price) :
    let d := fun t => intervalDemand (y t) (hy t) (hanti t)
    benchmark T zeroPrice d ref posted =
      Finset.univ.sup' Finset.univ_nonempty (fun g : Fin T → Fin (n + 1) =>
        if ∀ i j : Fin T, ref i = ref j → g i = g j then
          ∑ t : Fin T, (y t (g t) - revenue zeroPrice (d t) (posted t))
        else -(T : ℝ) * 2) := by
  classical
  intro d
  let F (g : Fin T → Fin (n + 1)) :=
    if ∀ i j : Fin T, ref i = ref j → g i = g j then
      ∑ t : Fin T, (y t (g t) - revenue zeroPrice (d t) (posted t))
    else -(T : ℝ) * 2
  change _ = Finset.univ.sup' _ F
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, id, measurable_id, rfl⟩
    · rintro _ ⟨f, _, rfl⟩
      let g (i : Fin T) := intervalIndex n (f (ref i))
      have hg : ∀ i j : Fin T, ref i = ref j → g i = g j := fun _ _ h => congrArg (intervalIndex n ∘ f) h
      rw [← Fin.sum_univ_eq_sum_range]
      refine (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin T))) fun t _ => sub_le_sub_right
        (intervalDemand_revenue_le (y t) (hy t) (hanti t) (f (ref t)))
        (revenue zeroPrice (d t) (posted t))).trans ?_
      simpa only [F, if_pos hg] using Finset.le_sup' F (Finset.mem_univ g)
  · apply Finset.sup'_le
    intro g _
    by_cases hg : ∀ i j : Fin T, ref i = ref j → g i = g j
    · obtain ⟨f, hf, he⟩ := measurable_remapping_of_coherence
        (fun t : Fin T => ref t) (fun t => intervalPrice (g t))
        (fun i j h => congrArg intervalPrice (hg i j h))
      have hc := comparison_le_benchmark (T := T) (cost := zeroPrice) (demand := d)
        (reference := ref) (posted := posted) hf
      rw [← Fin.sum_univ_eq_sum_range] at hc
      have hv (t : Fin T) : f (ref t) = intervalPrice (g t) := congrFun he t
      simp_rw [hv, d, intervalDemand_endpoint] at hc
      simpa only [F, if_pos hg] using hc
    · have hc := comparison_le_benchmark (T := T) (cost := zeroPrice) (demand := d)
        (reference := ref) (posted := posted) (f := fun _ => zeroPrice) measurable_const
      have hl : -(T : ℝ) * 2 ≤ ∑ t ∈ Finset.range T,
          (revenue zeroPrice (d t) zeroPrice - revenue zeroPrice (d t) (posted t)) := by
        calc
          _ = ∑ _ ∈ Finset.range T, (-2 : ℝ) := by simp
          _ ≤ _ := Finset.sum_le_sum (fun t _ => by
            have h₁ := (abs_le.mp (abs_revenue_le_one zeroPrice (d t) zeroPrice)).1
            have h₂ := (abs_le.mp (abs_revenue_le_one zeroPrice (d t) (posted t))).2
            linarith)
      simpa only [F, if_neg hg] using hl.trans hc

theorem intervalDemand_revenue_measurable {n : ℕ} (y : Fin (n + 1) → ℝ)
    (hy : ∀ i, y i / (intervalPrice i : ℝ) ∈ Icc (0 : ℝ) 1)
    (hanti : Antitone fun i => y i / (intervalPrice i : ℝ)) :
    Measurable (revenue zeroPrice (intervalDemand y hy hanti)) := by
  classical
  have hs : MeasurableSet {p : Price | zeroPrice < p ∧ ∃ i : Fin (n + 1), p ≤ intervalPrice i} := by
    have he : {p : Price | ∃ i : Fin (n + 1), p ≤ intervalPrice i} =
        ⋃ i : Fin (n + 1), {p : Price | p ≤ intervalPrice i} := by ext p; simp
    change MeasurableSet ({p : Price | zeroPrice < p} ∩ {p : Price | ∃ i : Fin (n + 1),
      p ≤ intervalPrice i})
    rw [he]
    exact (measurableSet_lt measurable_const measurable_id).inter
      (MeasurableSet.iUnion fun _ => measurableSet_le measurable_id measurable_const)
  rw [show revenue zeroPrice (intervalDemand y hy hanti) =
      (fun p => if zeroPrice < p ∧ (∃ i : Fin (n + 1), p ≤ intervalPrice i) then
        ((p : ℝ) / (intervalPrice (intervalIndex n p) : ℝ)) * y (intervalIndex n p) else 0) from
      funext (intervalDemand_feedback y hy hanti)]
  refine Measurable.ite hs ?_ measurable_const
  have hi := intervalIndex_measurable n
  have h₁ := (measurable_of_finite (fun i : Fin (n + 1) => (intervalPrice i : ℝ))).comp hi
  have h₂ := (measurable_of_finite y).comp hi
  exact (measurable_subtype_coe.div h₁).mul h₂

/-- The pricing lower-bound benchmarks are integrable for arbitrary
measurable posted prices. The reference may itself be the posted history. -/
theorem integrable_interval_benchmark {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {n T : ℕ} (y : ℕ → Fin (n + 1) → ℝ)
    (hy : ∀ t i, y t i / (intervalPrice i : ℝ) ∈ Icc (0 : ℝ) 1)
    (hanti : ∀ t, Antitone fun i => y t i / (intervalPrice i : ℝ))
    (ref posted : Ω → ℕ → Price)
    (href : ∀ t < T, Measurable (fun ω => ref ω t))
    (hp : ∀ t < T, Measurable (fun ω => posted ω t)) :
    let d := fun t => intervalDemand (y t) (hy t) (hanti t)
    Integrable (fun ω => benchmark T zeroPrice d (ref ω) (posted ω)) P := by
  classical
  intro d
  have hrepr (ω : Ω) : benchmark T zeroPrice d (ref ω) (posted ω) =
      Finset.univ.sup' Finset.univ_nonempty (fun g : Fin T → Fin (n + 1) =>
        if ∀ i j : Fin T, ref ω i = ref ω j → g i = g j then
          ∑ t : Fin T, (y t (g t) - revenue zeroPrice (d t) (posted ω t))
        else -(T : ℝ) * 2) :=
    benchmark_interval_eq_finite (T := T) y hy hanti (ref ω) (posted ω)
  rw [funext hrepr]
  apply integrable_finset_max Finset.univ_nonempty _ (B := (T : ℝ) * 2)
  · intro g
    have hset : MeasurableSet {ω | ∀ i j : Fin T, ref ω i = ref ω j → g i = g j} := by
      have he : {ω | ∀ i j : Fin T, ref ω i = ref ω j → g i = g j} =
          ⋂ i : Fin T, ⋂ j : Fin T, {ω | g i = g j} ∪ {ω | ref ω i = ref ω j}ᶜ := by
        ext ω
        simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff]
        constructor
        · intro h i j
          by_cases he : ref ω i = ref ω j
          · exact Or.inl (h i j he)
          · exact Or.inr he
        · intro h i j he
          exact (h i j).resolve_right (not_not_intro he)
      rw [he]
      refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
      by_cases h : g i = g j
      · simp [h]
      · simpa [h] using (measurableSet_eq_fun (href i i.isLt) (href j j.isLt)).compl
    refine Measurable.ite hset ?_ measurable_const
    exact Finset.measurable_sum _ fun t _ => measurable_const.sub
      ((intervalDemand_revenue_measurable (y t) (hy t) (hanti t)).comp (hp t t.isLt))
  · intro g ω
    split
    · calc
        _ ≤ ∑ t : Fin T, |y t (g t) - revenue zeroPrice (d t) (posted ω t)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ : Fin T, (2 : ℝ) := Finset.sum_le_sum fun t _ => by
          have ht := abs_revenue_le_one zeroPrice (d t) (intervalPrice (g t))
          have he : revenue zeroPrice (d t) (intervalPrice (g t)) = y t (g t) :=
            intervalDemand_endpoint (y t) (hy t) (hanti t) (g t)
          rw [he] at ht
          simpa only [one_add_one_eq_two] using (abs_sub _ _).trans
            (add_le_add ht (abs_revenue_le_one zeroPrice (d t) (posted ω t)))
        _ = _ := by simp
    · rw [abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg T), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

/-- Transfer an expected swap-regret lower bound for the simulated bandit
rule to both benchmarks of the pricing rule on the same oblivious sequence. -/
theorem expected_pricing_lower_of_discrete {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] {n T : ℕ}
    (y : ℕ → Fin (n + 1) → ℝ)
    (hy : ∀ t i, y t i / (intervalPrice i : ℝ) ∈ Icc (0 : ℝ) 1)
    (hanti : ∀ t, Antitone fun i => y t i / (intervalPrice i : ℝ))
    (posted : Ω → ℕ → Price) (hp : ∀ t < T, Measurable (fun ω => posted ω t))
    (label : ℕ → ι) (recommended : ι → Price) (hrec : Function.Injective recommended)
    (best : ι → Fin (n + 1))
    (hbest : ∀ t < T, ∀ i, y t i ≤ y t (best (label t))) {b : ℝ}
    (hb : b ≤ ∫ ω, swapRegret T y (fun t => intervalIndex n (posted ω t)) ∂P) :
    let d := fun t => intervalDemand (y t) (hy t) (hanti t)
    (b ≤ ∫ ω, benchmark T zeroPrice d (posted ω) (posted ω) ∂P) ∧
      (b ≤ ∫ ω, benchmark T zeroPrice d (fun t => recommended (label t)) (posted ω) ∂P) := by
  intro d
  have hp' (t : ℕ) (ht : t < T) : Measurable (fun ω => intervalIndex n (posted ω t)) :=
    (intervalIndex_measurable n).comp (hp t ht)
  have hY (t : ℕ) (i : Fin (n + 1)) : |y t i| ≤ 1 := by
    rw [← intervalDemand_endpoint (y t) (hy t) (hanti t) i]
    exact abs_revenue_le_one _ _ _
  have hI : Integrable (fun ω => swapRegret T y (fun t => intervalIndex n (posted ω t))) P := by
    unfold swapRegret
    apply integrable_finset_max ⟨id, Finset.mem_univ _⟩ _ (B := (T : ℝ) * 2)
    · intro f
      exact Finset.measurable_sum _ fun t ht =>
        ((measurable_of_finite (y t ∘ f)).comp (hp' t (Finset.mem_range.mp ht))).sub
          ((measurable_of_finite (y t)).comp (hp' t (Finset.mem_range.mp ht)))
    · intro f ω
      calc
        _ ≤ ∑ t ∈ Finset.range T, |y t (f (intervalIndex n (posted ω t))) -
            y t (intervalIndex n (posted ω t))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ Finset.range T, (2 : ℝ) := Finset.sum_le_sum fun t _ => by
          simpa only [one_add_one_eq_two] using (abs_sub _ _).trans (add_le_add (hY t _) (hY t _))
        _ = _ := by simp
  have hS := integrable_interval_benchmark (T := T) y hy hanti posted posted hp hp (P := P)
  have hR := integrable_interval_benchmark (T := T) y hy hanti (fun _ t => recommended (label t))
    posted (fun _ _ => measurable_const) hp (P := P)
  have hpoint (ω : Ω) := swapRegret_le_both_pricing_benchmarks y hy hanti (posted ω)
    label recommended hrec best hbest
  exact ⟨hb.trans (integral_mono hI hS fun ω => (hpoint ω).1),
    hb.trans (integral_mono hI hR fun ω => (hpoint ω).2)⟩

private theorem benchmark_congr_demand {T : ℕ} (cost : Price) (d d' : ℕ → Demand)
    (ref posted : ℕ → Price) (h : ∀ t < T, d t = d' t) :
    benchmark T cost d ref posted = benchmark T cost d' ref posted := by
  have hs (f : Price → Price) :
      (∑ t ∈ Finset.range T, (revenue cost (d t) (f (ref t)) - revenue cost (d t) (posted t))) =
      ∑ t ∈ Finset.range T, (revenue cost (d' t) (f (ref t)) - revenue cost (d' t) (posted t)) := by
    exact Finset.sum_congr rfl fun t ht => by rw [h t (Finset.mem_range.mp ht)]
  unfold benchmark
  simp_rw [hs]

/-- Transfer the discrete lower bound at a fourth-power horizon to the
continuous pricing rate at a longer horizon, using a zero-demand tail. -/
theorem padded_pricing_rate_of_discrete {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] {n T : ℕ} (hn : 0 < n)
    (hK : Fintype.card ι ≤ n + 1) (hT : (n + 1) ^ 4 ≤ T) (hT' : T ≤ 16 * (n + 1) ^ 4)
    (y : ℕ → Fin (n + 1) → ℝ)
    (hy : ∀ t i, y t i / (intervalPrice i : ℝ) ∈ Icc (0 : ℝ) 1)
    (hanti : ∀ t, Antitone fun i => y t i / (intervalPrice i : ℝ))
    (posted : Ω → ℕ → Price) (hp : ∀ t < (n + 1) ^ 4, Measurable (fun ω => posted ω t))
    (label : ℕ → ι) (recommended : ι → Price) (hrec : Function.Injective recommended)
    (best : ι → Fin (n + 1))
    (hbest : ∀ t < (n + 1) ^ 4, ∀ i, y t i ≤ y t (best (label t))) {c : ℝ} (hc : 0 ≤ c)
    (hb : c * ((n + 1 : ℕ) : ℝ) ^ 3 / Real.log (n + 1 : ℕ) ^ 6 ≤
      ∫ ω, swapRegret ((n + 1) ^ 4) y (fun t => intervalIndex n (posted ω t)) ∂P) :
    let rate := (c / 16) * ((T : ℝ) ^ (3 / 4 : ℝ) +
      (Fintype.card ι : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ)) / Real.log T ^ 6
    let d (t : ℕ) : Demand := if t < (n + 1) ^ 4 then intervalDemand (y t) (hy t) (hanti t)
      else ⟨fun _ => zeroPrice, fun _ _ _ => le_rfl⟩
    (rate ≤ ∫ ω, benchmark T zeroPrice d (posted ω) (posted ω) ∂P) ∧
      (rate ≤ ∫ ω, benchmark T zeroPrice d (fun t => recommended (label t)) (posted ω) ∂P) := by
  intro rate d
  let N := n + 1
  let T₀ := N ^ 4
  let d₀ (t : ℕ) := intervalDemand (y t) (hy t) (hanti t)
  have hPad (ω : Ω) (ref : ℕ → Price) :
      benchmark T zeroPrice d ref (posted ω) = benchmark T₀ zeroPrice d₀ ref (posted ω) := by
    rw [benchmark_eq_of_zero_tail hT zeroPrice d ref (posted ω)]
    · exact benchmark_congr_demand _ _ _ _ _ fun t ht => by simp only [d, d₀, if_pos ht]
    · intro t ht _ p
      simp [d, not_lt_of_ge ht, revenue, zeroPrice]
  have hN : 1 < (N : ℝ) := by
    exact_mod_cast (show 1 < N from Nat.succ_lt_succ hn)
  have hNT : N ≤ T := by
    apply le_trans _ hT
    exact le_self_pow₀ (by omega : 1 ≤ N) (by omega : (4 : ℕ) ≠ 0)
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hlogT : Real.log N ≤ Real.log T := Real.log_le_log (by positivity) (by exact_mod_cast hNT)
  have hscale := pricing_rate_le_fourth_power (N := N) (Nat.succ_pos n) hK hT'
  have hrate : rate ≤ c * (N : ℝ) ^ 3 / Real.log N ^ 6 := by
    calc
      rate ≤ ((c / 16) * (16 * (N : ℝ) ^ 3)) / Real.log T ^ 6 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (by positivity)) (by positivity)
      _ = c * (N : ℝ) ^ 3 / Real.log T ^ 6 := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ hlog.le hlogT 6)
  obtain ⟨hs, hr⟩ := expected_pricing_lower_of_discrete P y hy hanti posted hp label recommended
    hrec best hbest hb
  refine ⟨?_, ?_⟩
  · simp_rw [hPad]
    exact hrate.trans hs
  · simp_rw [hPad]
    exact hrate.trans hr

/-- Choose a tree large enough for the asymptotic discrete lower bound whose
fourth-power horizon fits in the pricing horizon. The next tree would have
twice as many actions and sixteen times as many rounds. -/
theorem exists_tree_horizon (minimum T : ℕ) (hT : (16 * 2 ^ minimum) ^ 4 ≤ T) :
    ∃ h : ℕ, minimum ≤ h ∧ (16 * 2 ^ h) ^ 4 ≤ T ∧ T < 16 * (16 * 2 ^ h) ^ 4 := by
  let P (h : ℕ) := (16 * 2 ^ h) ^ 4 ≤ T
  let h := Nat.findGreatest P T
  have hbound (d : ℕ) : d < (16 * 2 ^ d) ^ 4 := calc
    d < 2 ^ d := Nat.lt_two_pow_self
    _ ≤ 16 * 2 ^ d := by omega
    _ ≤ (16 * 2 ^ d) ^ 4 :=
      le_self_pow₀ (Nat.succ_le_of_lt (by positivity)) (by decide : (4 : ℕ) ≠ 0)
  have hm : minimum ≤ T := (hbound minimum).le.trans hT
  have hd : P h := Nat.findGreatest_spec hm hT
  have hnext : T < (16 * 2 ^ (h + 1)) ^ 4 := by
    by_cases hh : h + 1 ≤ T
    · exact lt_of_not_ge (Nat.findGreatest_is_greatest (P := P) (Nat.lt_succ_self h) hh)
    · exact (lt_of_not_ge hh).trans (hbound (h + 1))
  refine ⟨h, Nat.le_findGreatest hm hT, hd, ?_⟩
  rw [show (2 : ℕ) ^ (h + 1) = 2 ^ h * 2 from pow_succ 2 h] at hnext
  have he : (16 * (2 ^ h * 2) : ℕ) ^ 4 = 16 * (16 * 2 ^ h) ^ 4 := by ring
  rwa [he] at hnext

end CalibeatBandit.Pricing

end

section

set_option autoImplicit false

namespace CalibeatBandit.Pricing

open MeasureTheory Set

/-- Convert the bandit reward at the grid endpoint to the revenue at
the price the simulated learner actually posted. -/
noncomputable def scaledFeedback (n : ℕ) (p : Price) (y : ℝ) : ℝ :=
  if zeroPrice < p ∧ (∃ i : Fin (n + 1), p ≤ intervalPrice i) then
    ((p : ℝ) / (intervalPrice (intervalIndex n p) : ℝ)) * y else 0

theorem measurable_scaledFeedback (n : ℕ) :
    Measurable (fun p : Price × ℝ => scaledFeedback n p.1 p.2) := by
  classical
  have hp : Measurable (fun p : Price × ℝ => (p.1 : ℝ)) := measurable_subtype_coe.comp measurable_fst
  have hlo : MeasurableSet {p : Price × ℝ | zeroPrice < p.1} := by
    change MeasurableSet {p : Price × ℝ | (zeroPrice : ℝ) < (p.1 : ℝ)}
    exact measurableSet_lt (measurable_const (a := (zeroPrice : ℝ))) hp
  have hhi : MeasurableSet {p : Price × ℝ | ∃ i : Fin (n + 1), p.1 ≤ intervalPrice i} := by
    rw [show {p : Price × ℝ | ∃ i : Fin (n + 1), p.1 ≤ intervalPrice i} =
      ⋃ i : Fin (n + 1), {p : Price × ℝ | p.1 ≤ intervalPrice i} from by ext p; simp]
    apply MeasurableSet.iUnion
    intro i
    change MeasurableSet {p : Price × ℝ | (p.1 : ℝ) ≤ (intervalPrice i : ℝ)}
    exact measurableSet_le hp (measurable_const (a := (intervalPrice i : ℝ)))
  have hm : Measurable (fun p : Price × ℝ => (intervalPrice (intervalIndex n p.1) : ℝ)) :=
    (Measurable.of_discrete (f := fun i : Fin (n + 1) => (intervalPrice i : ℝ))).comp
      ((intervalIndex_measurable n).comp measurable_fst)
  exact Measurable.ite (hlo.inter hhi) ((hp.div hm).mul measurable_snd) measurable_const

/-- Recover the pricing learner's history from the discrete observations
alone, by replaying the earlier prices and scaling each observed reward. -/
noncomputable def pricingFromBandit (n : ℕ) (rule : PricingRule) :
    (t : ℕ) → FeedbackHistory t → Fin t → Price × ℝ
  | 0, _ => Fin.elim0
  | t + 1, history =>
    let prior := pricingFromBandit n rule t history.1
    let p := rule t prior
    Fin.lastCases (p, scaledFeedback n p history.2) prior

noncomputable def simulatedBandit (n : ℕ) (rule : PricingRule)
    (t : ℕ) (history : FeedbackHistory t) : Fin (n + 1) :=
  intervalIndex n (rule t (pricingFromBandit n rule t history))

theorem measurable_pricingFromBandit {S : Type*} [MeasurableSpace S] (n : ℕ)
    (rule : S → PricingRule)
    (hm : ∀ t, Measurable (fun p : S × (Fin t → Price × ℝ) => rule p.1 t p.2))
    (t : ℕ) : Measurable (fun p : S × FeedbackHistory t => pricingFromBandit n (rule p.1) t p.2) := by
  induction t with
  | zero =>
    apply measurable_pi_iff.mpr
    intro i
    exact i.elim0
  | succ t ih =>
    let past (p : S × FeedbackHistory (t + 1)) := pricingFromBandit n (rule p.1) t p.2.1
    have hpast : Measurable past :=
      ih.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    let price (p : S × FeedbackHistory (t + 1)) := rule p.1 t (past p)
    have hp : Measurable price := (hm t).comp (measurable_fst.prodMk hpast)
    have hrev : Measurable (fun p : S × FeedbackHistory (t + 1) => scaledFeedback n (price p) p.2.2) :=
      (measurable_scaledFeedback n).comp (hp.prodMk (measurable_snd.comp measurable_snd))
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [pricingFromBandit, Fin.lastCases_last, past, price] using hp.prodMk hrev
    · simpa only [pricingFromBandit, Fin.lastCases_castSucc, past] using (measurable_pi_iff.mp hpast) j

theorem measurable_simulatedBandit {S : Type*} [MeasurableSpace S] (n : ℕ)
    (rule : S → PricingRule)
    (hm : ∀ t, Measurable (fun p : S × (Fin t → Price × ℝ) => rule p.1 t p.2)) (t : ℕ) :
    Measurable (fun p : S × FeedbackHistory t => simulatedBandit n (rule p.1) t p.2) :=
  (intervalIndex_measurable n).comp
    ((hm t).comp (measurable_fst.prodMk (measurable_pricingFromBandit n rule hm t)))

/-- The bandit simulation uses one discrete observation each round. The
history it reconstructs is exactly the history on the interval demand. -/
theorem pricingFromBandit_eq_history {n : ℕ} (rule : PricingRule) (y : ℕ → Fin (n + 1) → ℝ)
    (hy : ∀ t i, y t i / (intervalPrice i : ℝ) ∈ Icc 0 1)
    (hanti : ∀ t, Antitone fun i => y t i / (intervalPrice i : ℝ)) (t : ℕ) :
    pricingFromBandit n rule t (feedbackHistory (simulatedBandit n rule) y t) =
      pricingHistory rule (fun s => revenue zeroPrice (intervalDemand (y s) (hy s) (hanti s))) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    let a := pricingFromBandit n rule t (feedbackHistory (simulatedBandit n rule) y t)
    let b := pricingHistory rule (fun s => revenue zeroPrice (intervalDemand (y s) (hy s) (hanti s))) t
    change Fin.lastCases (motive := fun _ : Fin (t + 1) => Price × ℝ) (rule t a, scaledFeedback n (rule t a) (y t (intervalIndex n (rule t a)))) a =
      Fin.lastCases (motive := fun _ : Fin (t + 1) => Price × ℝ) (rule t b, revenue zeroPrice (intervalDemand (y t) (hy t) (hanti t)) (rule t b)) b
    have he : a = b := ih
    rw [he, intervalDemand_feedback]
    rfl

theorem measurable_pricingHistory {S : Type*} [MeasurableSpace S] (rule : S → PricingRule)
    (hm : ∀ t, Measurable (fun p : S × (Fin t → Price × ℝ) => rule p.1 t p.2))
    (observe : ℕ → Price → ℝ) (ho : ∀ t, Measurable (observe t)) (t : ℕ) :
    Measurable (fun s => pricingHistory (rule s) observe t) := by
  induction t with
  | zero =>
    apply measurable_pi_iff.mpr
    intro i
    exact i.elim0
  | succ t ih =>
    have hp := (hm t).comp (measurable_id.prodMk ih)
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [pricingHistory, Fin.lastCases_last]
      exact hp.prodMk ((ho t).comp hp)
    · simpa only [pricingHistory, Fin.lastCases_castSucc] using (measurable_pi_iff.mp ih) j

end CalibeatBandit.Pricing

end

section

set_option autoImplicit false

namespace CalibeatBandit.Pricing

open MeasureTheory Set

private theorem pricingHistory_congr_before (rule : PricingRule)
    (obs obs' : ℕ → Price → ℝ) (t : ℕ) (h : ∀ s < t, obs s = obs' s) :
    pricingHistory rule obs t = pricingHistory rule obs' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ht := ih (fun s hs => h s (Nat.lt_succ_of_lt hs))
    simp only [pricingHistory, ht, h t (Nat.lt_succ_self t)]

end CalibeatBandit.Pricing

open CalibeatBandit.Pricing CalibeatBandit MeasureTheory Set Filter in
set_option maxHeartbeats 1200000 in
/-- Theorem 5.2 at the sparsity of the paper's construction. The number
of possible recommendations is the number of tree leaves. The learner
may use the entire fixed recommendation sequence when choosing a price. -/
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
      ∃ K : ℕ, 0 < K ∧ ∀ {S : Type*} [MeasurableSpace S] (P : Measure S)
        [IsProbabilityMeasure P] (rule : (ℕ → Price) → S → PricingRule),
        (∀ a t, Measurable (fun p : S × (Fin t → Price × ℝ) => rule a p.1 t p.2)) →
        ∃ (d : ℕ → Demand) (recommendationPrice : Fin K → Price) (label : ℕ → Fin K),
          let recommendations := recommendationPrice ∘ label
          let posted (s : S) (t : ℕ) :=
            rule recommendations s t (pricingHistory (rule recommendations s) (fun i => revenue zeroPrice (d i)) t)
          let rate := c * ((T : ℝ) ^ (3 / 4 : ℝ) + (K : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ)) /
            Real.log T ^ 6
          (rate ≤ ∫ s, benchmark T zeroPrice d (posted s) (posted s) ∂P) ∧
            (rate ≤ ∫ s, benchmark T zeroPrice d recommendations (posted s) ∂P) := by
  classical
  obtain ⟨K₀, hK₀, hscale⟩ := tree_scale_threshold
  let c : ℝ := 1 / (8 * 10 ^ 10)
  refine ⟨c / 16, by positivity, treeActionBudget K₀ ^ 4, ?_⟩
  intro T hT
  obtain ⟨h, hh₀, hlo, hhi⟩ := exists_tree_horizon K₀ (T := T) hT
  let L := 2 ^ h
  let r := treePeriodLength h
  let T₁ := L * r
  let η := treeBonusScale h
  let active := blockLeaf h r
  have hh : 0 < h := by omega
  have hK : K₀ ≤ treeActionBudget h := by
    have hp : h ≤ (2 : ℕ) ^ h := Nat.lt_two_pow_self.le
    unfold treeActionBudget
    omega
  have hpos : 0 < treeActionBudget h := by omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have hn' : n + 1 = treeActionBudget h := hn.symm
  have hnpos : 0 < n := by omega
  have hT₁ : T₁ = (n + 1) ^ 4 := by rw [hn']; exact tree_horizon_eq h
  have hN : (n + 1) ^ 4 ≤ T := by rw [hn']; exact hlo
  have hN' : T ≤ 16 * (n + 1) ^ 4 := by rw [hn']; exact hhi.le
  have hL : L ≤ n + 1 := by rw [hn']; unfold L treeActionBudget; omega
  have hLT : 4 * L ≤ T := by
    have ht : n + 1 ≤ (n + 1) ^ 4 :=
      le_self_pow₀ (by omega) (by decide : (4 : ℕ) ≠ 0)
    have hL' : 4 * L ≤ n + 1 := by rw [hn']; unfold L treeActionBudget; omega
    exact hL'.trans (ht.trans hN)
  let recPrice : Fin L → Price := periodPrice hLT
  have hrec : Function.Injective recPrice := periodPrice_injective hLT
  let recommendations : ℕ → Price := recPrice ∘ active
  refine ⟨L, by positivity, ?_⟩
  intro S ms P prob rule hm
  let rules := rule recommendations
  let pick (t : ℕ) (s : S) := simulatedBandit n (rules s) t
  have hpick (t : ℕ) : Measurable (fun p : S × FeedbackHistory t => pick t p.1 p.2) :=
    measurable_simulatedBandit n rules (hm recommendations) t
  obtain ⟨U, ⟨e₀⟩⟩ := treeActionEquiv_exact h
  let e : Fin (n + 1) ≃ TreeAction h (8 * 2 ^ h) U := (finCongr hn').trans e₀
  let anchor : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  have h₂ : n + 1 ≤ 2 * treeActionBudget h := by omega
  obtain ⟨env, henv⟩ := exists_hard_tree_environment P hh hn'.ge h₂ hK hscale e pick hpick anchor
  let y := treeEnvironmentReward e active η env
  have hη : 0 ≤ η := (treeBonusScale_pos h).le
  have hη' : η ≤ 1 / ((n : ℝ) + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using treeBonusScale_le_inv_actions (h := h) h₂ (Nat.zero_lt_succ n)
  have hratio (t : ℕ) : (∀ i, y t i / (intervalPrice i : ℝ) ∈ Icc 0 1) ∧
      Antitone (fun i => y t i / (intervalPrice i : ℝ)) := by
    let d := tapeDraw env.2 t
    let z := supportedBase d.1
    let b (i : Fin (n + 1)) := decide ((supportedThreshold (d.2 i) : ℝ) < tableBonuses e active env.1 t i)
    exact interval_ratios_of_rewards z.property hη hη' b
  let hy (t : ℕ) := (hratio t).1
  let hanti (t : ℕ) := (hratio t).2
  let d₁ (t : ℕ) := intervalDemand (y t) (hy t) (hanti t)
  let d (t : ℕ) : Demand := if t < (n + 1) ^ 4 then d₁ t else
    ⟨fun _ => zeroPrice, fun _ _ _ => le_rfl⟩
  let best (l : Fin L) := e.symm (.inr (.inl (env.1.2.2 l)))
  have hbest (t : ℕ) (_ : t < (n + 1) ^ 4) (i : Fin (n + 1)) : y t i ≤ y t (best (active t)) := by
    let z := supportedBase (tapeDraw env.2 t).1
    let draw (a : TreeAction h (8 * 2 ^ h) U) := supportedThreshold ((tapeDraw env.2 t).2 (e.symm a))
    have he (i : Fin (n + 1)) : y t i =
        treeReward η (active t) env.1.2.1 (tableLeafCoin env.1.1 t) (env.1.2.2 (active t)) z draw (e i) := by
      simp only [y, treeEnvironmentReward, boundedRoundReward, tableBonuses, scheduledBonuses,
        treeReward, z, draw, Equiv.symm_apply_apply]
      rfl
    rw [he i, he (best (active t))]
    simpa only [best, Equiv.apply_symm_apply] using
      treeReward_max hη (active t) env.1.2.1 (tableLeafCoin env.1.1 t) (env.1.2.2 (active t)) z draw (e i)
  let obs₁ (t : ℕ) := revenue zeroPrice (d₁ t)
  let obs (t : ℕ) := revenue zeroPrice (d t)
  let posted (s : S) (t : ℕ) := rules s t (pricingHistory (rules s) obs t)
  have hobs (t : ℕ) : Measurable (obs t) := by
    by_cases ht : t < (n + 1) ^ 4
    · simpa only [obs, d, if_pos ht, d₁] using intervalDemand_revenue_measurable (y t) (hy t) (hanti t)
    · have he : obs t = fun _ => (0 : ℝ) := by
        funext p
        simp [obs, d, ht, revenue, zeroPrice]
      rw [he]
      exact measurable_const
  have hp (t : ℕ) (_ht : t < (n + 1) ^ 4) : Measurable (fun s => posted s t) :=
    (hm recommendations t).comp (measurable_id.prodMk (measurable_pricingHistory rules (hm recommendations) obs hobs t))
  have hact (s : S) (t : ℕ) (ht : t < (n + 1) ^ 4) :
      treeEnvironmentAction e active η (fun t => pick t s) anchor env t = intervalIndex n (posted s t) := by
    have ht₁ : t < 2 ^ h * treePeriodLength h := by
      change t < T₁
      rwa [hT₁]
    simp only [treeEnvironmentAction, dif_pos ht₁]
    rw [rawTapeHistory_eq_feedbackHistory]
    change intervalIndex n (rules s t
      (pricingFromBandit n (rules s) t (feedbackHistory (simulatedBandit n (rules s)) y t))) = _
    rw [pricingFromBandit_eq_history (rules s) y hy hanti t]
    have he : pricingHistory (rules s) obs t = pricingHistory (rules s) obs₁ t := by
      apply pricingHistory_congr_before
      intro t' ht'
      simp only [obs, obs₁, d, if_pos (ht'.trans ht)]
    rw [show posted s t = rules s t (pricingHistory (rules s) obs t) from rfl, he]
  have hreg (s : S) : swapRegret T₁ y (treeEnvironmentAction e active η (fun t => pick t s) anchor env) =
      swapRegret ((n + 1) ^ 4) y (fun t => intervalIndex n (posted s t)) := by
    calc
      _ = swapRegret ((n + 1) ^ 4) y (treeEnvironmentAction e active η (fun t => pick t s) anchor env) :=
        congrArg (fun length => swapRegret length y (treeEnvironmentAction e active η (fun t => pick t s) anchor env)) hT₁
      _ = _ := swapRegret_congr_before (fun _ _ _ => rfl) (fun t ht => hact s t ht)
  have hb : c * ((n + 1 : ℕ) : ℝ) ^ 3 / Real.log (n + 1 : ℕ) ^ 6 ≤
      ∫ s, swapRegret ((n + 1) ^ 4) y (fun t => intervalIndex n (posted s t)) ∂P := by
    change ((n + 1 : ℕ) : ℝ) ^ 3 / (8 * 10 ^ 10 * Real.log (n + 1 : ℕ) ^ 6) ≤
      ∫ s, swapRegret T₁ y (treeEnvironmentAction e active η (fun t => pick t s) anchor env) ∂P at henv
    simp_rw [hreg] at henv
    convert henv using 1
    unfold c
    ring
  have hfinal := padded_pricing_rate_of_discrete P hnpos
    (show Fintype.card (Fin L) ≤ n + 1 by simpa only [Fintype.card_fin] using hL)
    hN hN' y hy hanti posted hp active recPrice hrec best hbest (show 0 ≤ c by dsimp [c]; positivity) hb
  refine ⟨d, recPrice, active, ?_⟩
  let rate := c / 16 * ((T : ℝ) ^ (3 / 4 : ℝ) + (L : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ)) /
    Real.log T ^ 6
  change (rate ≤ ∫ s, benchmark T zeroPrice d (posted s) (posted s) ∂P) ∧
    (rate ≤ ∫ s, benchmark T zeroPrice d recommendations (posted s) ∂P)
  simp only [Fintype.card_fin] at hfinal
  exact hfinal

end
