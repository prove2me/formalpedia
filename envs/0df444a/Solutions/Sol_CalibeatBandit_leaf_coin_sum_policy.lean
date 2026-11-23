-- Prove2me | solution 1 for CalibeatBandit.leaf_coin_sum_policy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T18:47:33.162427+00:00
-- url     : https://prove2.me/submissions/cb8056b9-820f-40c0-ab89-c60088ddecc5

import Mathlib
import Definitions.Def_CalibeatBandit_lower_bound_models
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_hard_tree_environment
import Definitions.Def_CalibeatBandit_hard_tree_analysis

section

set_option autoImplicit false

open Filter MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

theorem swapGain_le_best {K T : ℕ} (q u : ℕ → Fin K → ℝ) (i j : Fin K) :
    swapGain T q u i j ≤ bestSwapGain T q u i :=
  Finset.le_sup' (swapGain T q u i) (Finset.mem_univ j)

/-- The deterministic root comparison used in Lemma 4.4. -/
theorem root_bestSwapGain {K T : ℕ} (q u : ℕ → Fin K → ℝ)
    (i rootA rootB : Fin K) (H : ℝ)
    (hroot : ∀ t < T, u t rootA + u t rootB = 1 / (2 * H)) :
    (∑ t ∈ Finset.range T, q t i) / (4 * H) -
      (∑ t ∈ Finset.range T, q t i * u t i) ≤ bestSwapGain T q u i := by
  have hsum : swapGain T q u i rootA + swapGain T q u i rootB =
      (∑ t ∈ Finset.range T, q t i) * (1 / (2 * H)) -
        2 * (∑ t ∈ Finset.range T, q t i * u t i) := by
    simp only [swapGain, ← Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t ht => by
      rw [← hroot t (Finset.mem_range.mp ht)]
      ring
  have half : (∑ t ∈ Finset.range T, q t i) / (4 * H) =
      ((∑ t ∈ Finset.range T, q t i) * (1 / (2 * H))) / 2 := by
    by_cases h : H = 0
    · simp [h]
    · field_simp
      ring
  linarith only [half, hsum, swapGain_le_best (T := T) q u i rootA,
    swapGain_le_best (T := T) q u i rootB]

/-- The two deterministic comparisons used for a leaf action in Lemma 4.5.
The selected auxiliary action has bonus probability one in the leaf's period. -/
theorem leaf_bestSwapGain {K T : ℕ} (q u : ℕ → Fin K → ℝ)
    (period : Finset ℕ) (hperiod : period ⊆ Finset.range T)
    (i auxiliary rootA rootB : Fin K) (H : ℝ)
    (hq : ∀ t < T, 0 ≤ q t i) (hu : ∀ t < T, 0 ≤ u t auxiliary)
    (hoff : ∀ t < T, t ∉ period → u t i = 0)
    (hon : ∀ t ∈ period, u t auxiliary = 1)
    (hroot : ∀ t < T, u t rootA + u t rootB = 1 / (2 * H)) :
    (∑ t ∈ period, q t i * (1 - u t i)) ≤ bestSwapGain T q u i ∧
      (∑ t ∈ Finset.range T, q t i) / (4 * H) -
        (∑ t ∈ period, q t i * u t i) ≤ bestSwapGain T q u i := by
  classical
  constructor
  · apply le_trans _ (swapGain_le_best (T := T) q u i auxiliary)
    unfold swapGain
    have h := Finset.sum_le_sum_of_subset_of_nonneg hperiod
      (f := fun t => q t i * (u t auxiliary - u t i))
      (fun t ht hout => by
        rw [hoff t (Finset.mem_range.mp ht) hout, sub_zero]
        exact mul_nonneg (hq t (Finset.mem_range.mp ht)) (hu t (Finset.mem_range.mp ht)))
    have he : (∑ t ∈ period, q t i * (1 - u t i)) =
        ∑ t ∈ period, q t i * (u t auxiliary - u t i) :=
      Finset.sum_congr rfl fun t ht => by rw [hon t ht]
    exact he.le.trans h
  · have he : (∑ t ∈ period, q t i * u t i) = ∑ t ∈ Finset.range T, q t i * u t i := by
      apply Finset.sum_subset hperiod
      intro t ht hout
      rw [hoff t (Finset.mem_range.mp ht) hout, mul_zero]
    rw [he]
    exact root_bestSwapGain q u i rootA rootB H hroot

/-- After averaging over the fresh leaf coin, the two leaf comparisons give
the factor 1/(8H) in Lemma 4.5. -/
theorem leaf_expected_gain {H total inside gain : ℝ} (h₁ : inside / 2 ≤ gain)
    (h₂ : total / (4 * H) - inside / 2 ≤ gain) :
    total / (8 * H) ≤ gain := by
  have he : total / (4 * H) = 2 * (total / (8 * H)) := by ring
  linarith only [h₁, h₂, he]

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open Set MeasureTheory

namespace TreeNode

def root (h : ℕ) : TreeNode h := ⟨0, 0⟩

theorem root_active {h : ℕ} (l : Fin (2 ^ h)) : (root h).active l := by
  exact ⟨by simp [first, root], by simp [last, root]⟩

theorem active_leaf_iff {h : ℕ} (v : TreeNode h) (hd : (v.1 : ℕ) = h) (l : Fin (2 ^ h)) :
    v.active l ↔ (l : ℕ) = (v.2 : ℕ) := by
  simp [active, first, last, hd]
  omega

end TreeNode

theorem treeBonusProb_mem {h M U : ℕ} (leaf : Fin (2 ^ h))
    (coin : TreeNode h → Bool) (leafCoin : Bool) (selected : Fin M) (a : TreeAction h M U) :
    treeBonusProb leaf coin leafCoin selected a ∈ Icc (0 : ℝ) 1 := by
  have hz : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have h₁ : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  rcases a with ⟨v, side⟩ | (j | j)
  · have hdepth : (v.1 : ℕ) ≤ h := Nat.le_of_lt_succ v.1.isLt
    have hd : ((v.1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hdepth
    have hh : 0 < treeHeight h := by unfold treeHeight; positivity
    have hfrac : (((v.1 : ℕ) + 1 : ℝ) / (2 * treeHeight h)) ∈ Icc 0 1 := by
      refine ⟨by positivity, (div_le_one (by positivity)).mpr ?_⟩
      unfold treeHeight
      linarith
    simp only [treeBonusProb]
    split_ifs <;> assumption
  · simp only [treeBonusProb]
    split <;> assumption
  · exact hz

theorem treeBonusProb_root_pair {h M U : ℕ} (hh : 0 < h) (leaf : Fin (2 ^ h))
    (coin : TreeNode h → Bool) (leafCoin : Bool) (selected : Fin M) :
    treeBonusProb (U := U) leaf coin leafCoin selected (.inl (TreeNode.root h, false)) +
      treeBonusProb (U := U) leaf coin leafCoin selected (.inl (TreeNode.root h, true)) =
      1 / (2 * treeHeight h) := by
  have hd : ((TreeNode.root h).1 : ℕ) ≠ h := by simpa [TreeNode.root] using hh.ne
  let b := if (leaf : ℕ) < (TreeNode.root h).mid then false else coin (TreeNode.root h)
  change (if (TreeNode.root h).active leaf then
      if ((TreeNode.root h).1 : ℕ) = h then (if false = leafCoin then 1 else 0)
      else if false = b then _ else 0 else 0) + _ = _
  simp only [treeBonusProb, TreeNode.root_active, if_true, hd, if_false]
  change (if false = b then _ else 0) + (if true = b then _ else 0) = _
  cases b <;> simp [TreeNode.root]

theorem feedbackHistory_eq_of_prior_rewards_eq {A : Type*}
    (pick : (t : ℕ) → FeedbackHistory t → A) (y y' : ℕ → A → ℝ) (t : ℕ)
    (h : ∀ s < t, ∀ a, y s a = y' s a) :
    feedbackHistory pick y t = feedbackHistory pick y' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (fun s hs => h s (Nat.lt_succ_of_lt hs))
    simp only [feedbackHistory, he, h t (Nat.lt_succ_self t)]
    rfl

/-- A quantity that is invariant under changing one fair coin has half
its total mass in each value of that coin. -/
theorem sum_on_fair_coin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ι) (b : Bool) (g : (ι → Bool) → ℝ)
    (hg : ∀ c v, g (Function.update c j v) = g c) :
    (∑ c : ι → Bool, if c j = b then g c else 0) = (∑ c, g c) / 2 := by
  let flip (c : ι → Bool) := Function.update c j (! c j)
  have hflip : Function.Involutive flip := by
    intro c
    funext k
    by_cases hk : k = j
    · subst k
      simp [flip]
    · simp [flip, Function.update_of_ne hk]
  let e : (ι → Bool) ≃ (ι → Bool) := ⟨flip, flip, hflip, hflip⟩
  let f (c : ι → Bool) := if c j = b then g c else 0
  have he (c : ι → Bool) : f (e c) = if c j ≠ b then g c else 0 := by
    change (if flip c j = b then g (flip c) else 0) = _
    have hfg : g (flip c) = g c := hg c _
    have hfj : flip c j = ! c j := by simp [flip]
    rw [hfg, hfj]
    cases b <;> cases c j <;> simp
  have hs := e.sum_comp f
  simp_rw [he] at hs
  have hadd (c : ι → Bool) : g c =
      (if c j = b then g c else 0) + (if c j ≠ b then g c else 0) := by
    by_cases h : c j = b <;> simp [h]
  have htotal : (∑ c, g c) = (∑ c, f c) + (∑ c, if c j ≠ b then g c else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => hadd c
  change (∑ c, f c) = _
  linarith only [htotal, hs]

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open Set

/-- Current leaf coin is invisible when the learner chooses its current action. -/
theorem feedbackHistory_update_leafCoin {h M U T : ℕ}
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (coin : TreeNode h → Bool)
    (c : Fin T → Bool) (selected : Fin (2 ^ h) → Fin M)
    (z : ℕ → Icc (0 : ℝ) 1) (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1)
    (t : Fin T) (b : Bool) :
    let payoff (c' : Fin T → Bool) (s : ℕ) :=
      treeReward η (active s) coin (if hs : s < T then c' ⟨s, hs⟩ else false)
        (selected (active s)) (z s) (draw s)
    feedbackHistory pick (payoff (Function.update c t b)) t =
      feedbackHistory pick (payoff c) t := by
  intro payoff
  apply feedbackHistory_eq_of_prior_rewards_eq
  intro s hs a
  have hs' : s < T := hs.trans t.isLt
  have hne : (⟨s, hs'⟩ : Fin T) ≠ t := fun hh => hs.ne (congrArg Fin.val hh)
  simp only [payoff, dif_pos hs', Function.update_of_ne hne]

/-- A leaf action accounts for its full expected play mass up to the factor
(8H); either it is played in the active period or the root pair gains. -/
theorem leaf_coin_sum {h M U N T : ℕ} (hh : 0 < h)
    (e : Fin N ≃ TreeAction h M U) (v : TreeNode h) (hv : (v.1 : ℕ) = h) (side : Bool)
    (active : ℕ → Fin (2 ^ h)) (coin : TreeNode h → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : (Fin T → Bool) → ℕ → Fin N → ℝ)
    (hq : ∀ c t, t < T → ∀ i, 0 ≤ q c t i)
    (hcausal : ∀ (c : Fin T → Bool) (t : Fin T) b i, q (Function.update c t b) t i = q c t i) :
    let i := e.symm (.inl (v, side))
    let u (c : Fin T → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) coin (if ht : t < T then c ⟨t, ht⟩ else false) (selected (active t)) (e j)
    (∑ c, ∑ t ∈ Finset.range T, q c t i) / (8 * treeHeight h) ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by
  classical
  intro i u
  let period := (Finset.range T).filter fun t => v.active (active t)
  let leafAt : Fin (2 ^ h) := ⟨v.2, by simpa only [hv] using v.2.isLt⟩
  let aux := e.symm (.inr (.inl (selected leafAt)))
  let rootA := e.symm (.inl (TreeNode.root h, false))
  let rootB := e.symm (.inl (TreeNode.root h, true))
  have hp : period ⊆ Finset.range T := Finset.filter_subset _ _
  have hcomp (c : Fin T → Bool) :=
    leaf_bestSwapGain (q c) (u c) period hp i aux rootA rootB (treeHeight h)
      (fun t ht => hq c t ht i)
      (fun t _ => (treeBonusProb_mem _ _ _ _ _).1)
      (fun t ht hnot => by
        have hna : ¬v.active (active t) := fun ha => hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, ha⟩)
        simp [u, i, treeBonusProb, hna])
      (fun t ht => by
        have hact := (Finset.mem_filter.mp ht).2
        have heq : active t = leafAt := Fin.ext ((v.active_leaf_iff hv _).mp hact)
        simp [u, aux, treeBonusProb, heq])
      (fun t _ => by
        simpa only [u, rootA, rootB, Equiv.apply_symm_apply] using
          treeBonusProb_root_pair (U := U) hh (active t) coin
            (if ht : t < T then c ⟨t, ht⟩ else false) (selected (active t)))
  have hon (t : ℕ) (ht : t ∈ period) :
      (∑ c : Fin T → Bool, q c t i * u c t i) = (∑ c, q c t i) / 2 := by
    obtain ⟨ht', hact⟩ := Finset.mem_filter.mp ht
    have hlt := Finset.mem_range.mp ht'
    let j : Fin T := ⟨t, hlt⟩
    have hj (c : Fin T → Bool) :
        q c t i * u c t i = if c j = side then q c t i else 0 := by
      by_cases hc : c j = side
      · simp [u, i, treeBonusProb, hact, hv, hlt, ← hc, j]
      · have hn : side ≠ c j := Ne.symm hc
        simp [u, i, treeBonusProb, hact, hv, hlt, hc, hn, j]
    simp_rw [hj]
    exact sum_on_fair_coin j side (fun c => q c t i) (fun c b => hcausal c j b i)
  have he :
      (∑ c : Fin T → Bool, ∑ t ∈ period, q c t i * u c t i) =
        (∑ c : Fin T → Bool, ∑ t ∈ period, q c t i) / 2 := calc
    _ = ∑ t ∈ period, ∑ c : Fin T → Bool, q c t i * u c t i := Finset.sum_comm
    _ = ∑ t ∈ period, (∑ c : Fin T → Bool, q c t i) / 2 :=
      Finset.sum_congr rfl hon
    _ = _ := by rw [← Finset.sum_div, Finset.sum_comm]
  have h₁ : (∑ c : Fin T → Bool, ∑ t ∈ period, q c t i) / 2 ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by
    have hc := Finset.sum_le_sum (s := Finset.univ) fun c _ => (hcomp c).1
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, he] at hc
    linarith only [hc]
  have h₂ : (∑ c : Fin T → Bool, ∑ t ∈ Finset.range T, q c t i) / (4 * treeHeight h) -
      (∑ c : Fin T → Bool, ∑ t ∈ period, q c t i) / 2 ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by
    have hc := Finset.sum_le_sum (s := Finset.univ) fun c _ => (hcomp c).2
    simpa only [Finset.sum_sub_distrib, ← Finset.sum_div, he] using hc
  exact leaf_expected_gain h₁ h₂

theorem treePlayProbability_isProbVec {h M U N : ℕ} (e : Fin N ≃ TreeAction h M U)
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) (t : ℕ) :
    IsProbVec (treePlayProbability e pick active η coin leafCoin selected z draw t) := by
  classical
  unfold treePlayProbability
  dsimp only
  constructor
  · intro i
    dsimp only
    split <;> norm_num
  · let y (s : ℕ) := treeReward η (active s) coin (leafCoin s) (selected (active s)) (z s) (draw s)
    let a := pick t (feedbackHistory pick y t)
    change (∑ i, if a = e i then (1 : ℝ) else 0) = 1
    have he (i : Fin N) : a = e i ↔ i = e.symm a := by
      constructor
      · intro he
        rw [he, Equiv.symm_apply_apply]
      · rintro rfl
        rw [Equiv.apply_symm_apply]
    simp [he]

/-- The averaged leaf comparison for the actual learner with a fixed seed. -/
theorem leaf_coin_sum_policy {h M U N T : ℕ} (hh : 0 < h) (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) = h) (side : Bool)
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (coin : TreeNode h → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) :
    let leafCoin (c : Fin T → Bool) (t : ℕ) := if ht : t < T then c ⟨t, ht⟩ else false
    let i := e.symm (.inl (v, side))
    let q (c : Fin T → Bool) := treePlayProbability e pick active η coin (leafCoin c) selected z draw
    let u (c : Fin T → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) coin (leafCoin c t) (selected (active t)) (e j)
    (∑ c, ∑ t ∈ Finset.range T, q c t i) / (8 * treeHeight h) ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by
  intro leafCoin i q u
  refine leaf_coin_sum hh e v hv side active coin selected q (fun c t _ j => ?_) ?_
  · exact (treePlayProbability_isProbVec e pick active η coin (leafCoin c) selected z draw t).1 j
  · intro c t b j
    have he := feedbackHistory_update_leafCoin pick active η coin c selected z draw t b
    dsimp only at he
    unfold q treePlayProbability leafCoin
    dsimp only
    rw [he]

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.leaf_coin_sum_policy := @CalibeatBandit.leaf_coin_sum_policy
