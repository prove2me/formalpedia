-- Prove2me | solution 1 for CalibeatBandit.deepest_left_coin_sum_policy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T18:47:35.352519+00:00
-- url     : https://prove2.me/submissions/c838c9e8-6cef-46f3-898d-d417767da131

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

theorem bestSwapGain_nonneg {K T : ℕ} (q u : ℕ → Fin K → ℝ) (i : Fin K) :
    0 ≤ bestSwapGain T q u i := by
  simpa [swapGain] using swapGain_le_best (T := T) q u i i

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

/-- Children are numbered consecutively within the next level. -/
def child {h : ℕ} (v : TreeNode h) (hd : (v.1 : ℕ) < h) (right : Bool) : TreeNode h :=
  ⟨⟨(v.1 : ℕ) + 1, by omega⟩, ⟨2 * (v.2 : ℕ) + if right then 1 else 0, by
    have hv := v.2.isLt
    change _ < 2 ^ ((v.1 : ℕ) + 1)
    rw [pow_succ]
    cases right <;> simp <;> omega⟩⟩

theorem child_edges {h : ℕ} (v : TreeNode h) (hd : (v.1 : ℕ) < h) :
    (v.child hd false).first = v.first ∧ (v.child hd false).last = v.mid ∧
      (v.child hd true).first = v.mid ∧ (v.child hd true).last = v.last := by
  have hsub : h - (v.1 : ℕ) = (h - ((v.1 : ℕ) + 1)) + 1 := by omega
  simp only [child, first, last, mid, Bool.false_eq_true, ↓reduceIte, add_zero]
  rw [hsub, pow_succ]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem child_active_iff {h : ℕ} (v : TreeNode h) (hd : (v.1 : ℕ) < h)
    (leaf : Fin (2 ^ h)) :
    ((v.child hd false).active leaf ↔ v.active leaf ∧ (leaf : ℕ) < v.mid) ∧
      ((v.child hd true).active leaf ↔ v.active leaf ∧ v.mid ≤ (leaf : ℕ)) := by
  obtain ⟨hfl, hll, hfr, hlr⟩ := v.child_edges hd
  have hle : v.first ≤ v.mid := Nat.le_add_right _ _
  have hmid : v.mid ≤ v.last := by
    rw [← hfr, ← hlr]
    exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  simp only [active, hfl, hll, hfr, hlr]
  omega

end TreeNode

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

theorem treeBonusProb_leaf_pair {h M U : ℕ} (leaf : Fin (2 ^ h))
    (v : TreeNode h) (hd : (v.1 : ℕ) = h) (ha : v.active leaf)
    (coin : TreeNode h → Bool) (leafCoin : Bool) (selected : Fin M) :
    treeBonusProb (U := U) leaf coin leafCoin selected (.inl (v, false)) +
      treeBonusProb (U := U) leaf coin leafCoin selected (.inl (v, true)) = 1 := by
  cases leafCoin <;> simp [treeBonusProb, ha, hd]

/-- A change of one fixed node coin has no effect before the first leaf
in that node's right subtree. -/
theorem treeBonusProb_update_before_right {h M U : ℕ} (leaf : Fin (2 ^ h))
    (v : TreeNode h) (hleaf : (leaf : ℕ) < v.mid)
    (coin : TreeNode h → Bool) (b leafCoin : Bool) (selected : Fin M) (a : TreeAction h M U) :
    treeBonusProb leaf (Function.update coin v b) leafCoin selected a =
      treeBonusProb leaf coin leafCoin selected a := by
  rcases a with ⟨w, side⟩ | a
  · by_cases hw : w = v
    · subst w
      simp [treeBonusProb, hleaf]
    · simp [treeBonusProb, Function.update_of_ne hw]
  · cases a <;> rfl

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

/-- Changing a node's coin leaves the learner's action unchanged through
the first round that coin can affect. The leaves are visited in order. -/
theorem action_eq_of_update_before_right {h M U : ℕ}
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (v : TreeNode h) (b : Bool)
    (η : ℝ) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) (t : ℕ)
    (hprior : ∀ s < t, (active s : ℕ) < v.mid) :
    let y (c : TreeNode h → Bool) (s : ℕ) :=
      treeReward η (active s) c (leafCoin s) (selected (active s)) (z s) (draw s)
    pick t (feedbackHistory pick (y (Function.update coin v b)) t) =
      pick t (feedbackHistory pick (y coin) t) := by
  intro y
  congr 1
  apply feedbackHistory_eq_of_prior_rewards_eq
  intro s hs a
  dsimp [y, treeReward]
  rw [treeBonusProb_update_before_right (active s) v (hprior s hs)]

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

/-- Cases 2 and 3 use the same inequalities for the relevant groups of
rounds. In Case 3 the second group has zero mass. -/
theorem internal_three_comparisons {H gain total x₁ x₂ x₃ : ℝ}
    (hH : 1 ≤ H) (hg : 0 ≤ gain) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (h₁ : 4 * H ^ 2 * x₁ + 8 * H ^ 2 * x₂ ≤ 16 * H ^ 3 * gain)
    (h₂ : 2 * H * x₃ - 2 * H ^ 2 * (x₁ + x₂) ≤ 4 * H ^ 2 * gain)
    (h₃ : total - 2 * H * (x₁ + x₂ + x₃) ≤ 4 * H * gain) :
    total / (184 * H ^ 5) ≤ gain := by
  have hpos : 0 < H := by linarith
  have hgap : 0 ≤ H - 1 := sub_nonneg.mpr hH
  have hgap' : 0 ≤ 3 * H - 1 := by linarith
  have hsum : total + 2 * H * (H - 1) * x₁ + 2 * H * (3 * H - 1) * x₂ ≤
      (16 * H ^ 3 + 4 * H ^ 2 + 4 * H) * gain := by
    linear_combination h₁ + h₂ + h₃
  have hmass : total ≤ total + 2 * H * (H - 1) * x₁ + 2 * H * (3 * H - 1) * x₂ := by
    have h₁ : 0 ≤ 2 * H * (H - 1) * x₁ := by positivity
    have h₂ : 0 ≤ 2 * H * (3 * H - 1) * x₂ := by positivity
    linarith
  have hcoeff : 16 * H ^ 3 + 4 * H ^ 2 + 4 * H ≤ 184 * H ^ 5 := by
    have p (n : ℕ) (hn : n ≤ 5) : H ^ n ≤ H ^ 5 := pow_le_pow_right₀ hH hn
    nlinarith only [p 3 (by omega), p 2 (by omega), p 1 (by omega),
      show H ^ 1 = H by ring, show 0 ≤ H ^ 5 by positivity]
  exact (div_le_iff₀ (by positivity)).mpr (by
    rw [mul_comm gain]
    exact (hmass.trans hsum).trans (mul_le_mul_of_nonneg_right hcoeff hg))

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open Set

/-- Number of plays of one action while leaves in the indicated subtree
are active, with a fixed private seed and reward tape. -/
noncomputable def subtreePlayMass {h M U : ℕ}
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (w : TreeNode h)
    (η : ℝ) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) (T : ℕ)
    (a : TreeAction h M U) : ℝ :=
  let y (t : ℕ) := treeReward η (active t) coin (leafCoin t) (selected (active t)) (z t) (draw t)
  ∑ t ∈ Finset.range T, if w.active (active t) ∧ pick t (feedbackHistory pick y t) = a then 1 else 0

/-- Play mass accrued in an earlier subtree is invariant under changing
a coin that first influences rewards after that subtree has been visited. -/
theorem subtreePlayMass_update_of_before {h M U : ℕ}
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (ha : Monotone active) (w v : TreeNode h)
    (hbefore : w.last ≤ v.mid)
    (η : ℝ) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) (T : ℕ)
    (a : TreeAction h M U) (b : Bool) :
    subtreePlayMass pick active w η (Function.update coin v b) leafCoin selected z draw T a =
      subtreePlayMass pick active w η coin leafCoin selected z draw T a := by
  classical
  unfold subtreePlayMass
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases ht : w.active (active t)
  · have ht' : (active t : ℕ) < v.mid := lt_of_lt_of_le ht.2 hbefore
    have hprior (s : ℕ) (hs : s < t) : (active s : ℕ) < v.mid := lt_of_le_of_lt (ha hs.le) ht'
    have he := action_eq_of_update_before_right pick active v b η coin leafCoin selected z draw t hprior
    dsimp at he
    rw [he]
  · simp [ht]

private theorem pair_gain_lower {N T : ℕ} (q u : ℕ → Fin N → ℝ) (i a b : Fin N)
    (w : ℕ → ℝ) (hq : ∀ t < T, 0 ≤ q t i)
    (hw : ∀ t < T, w t ≤ (u t a + u t b) / 2 - u t i) :
    (∑ t ∈ Finset.range T, q t i * w t) ≤ bestSwapGain T q u i := by
  have hs := Finset.sum_le_sum (s := Finset.range T) fun t ht =>
    mul_le_mul_of_nonneg_left (hw t (Finset.mem_range.mp ht)) (hq t (Finset.mem_range.mp ht))
  have he : (∑ t ∈ Finset.range T, q t i * ((u t a + u t b) / 2 - u t i)) =
      (swapGain T q u i a + swapGain T q u i b) / 2 := by
    rw [swapGain, swapGain, ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [he] at hs
  linarith only [hs, swapGain_le_best (T := T) q u i a, swapGain_le_best (T := T) q u i b]

/-- The two child comparisons for the left action at depth one above the
leaves. The left comparison uses the event that the parent switches on the right. -/
theorem deepest_left_comparisons {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 = h)
    (active : ℕ → Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : ℕ → Fin N → ℝ)
    (hq : ∀ t < T, ∀ i, 0 ≤ q t i) :
    let i := e.symm (.inl (v, false))
    let l := v.child (by omega) false
    let r := v.child (by omega) true
    let u (t : ℕ) (j : Fin N) := treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    let c := 1 / (2 * treeHeight h)
    (coin v = true →
      (∑ t ∈ Finset.range T, q t i * (if l.active (active t) then c else 0)) ≤ bestSwapGain T q u i) ∧
    (∑ t ∈ Finset.range T, q t i *
      (if r.active (active t) then c else if l.active (active t) then -(1 / 2) else 0))
      ≤ bestSwapGain T q u i := by
  intro i l r u c
  have hd : (v.1 : ℕ) < h := by omega
  have hd' : (((v.1 : ℕ) : ℝ) + 1) = h := by exact_mod_cast hv
  have halg : 1 / 2 - (((v.1 : ℕ) : ℝ) + 1) / (2 * treeHeight h) = c := by
    rw [hd']
    dsimp [c, treeHeight]
    field_simp
    ring
  have haux (t : ℕ) :
      u t i = if v.active (active t) then
        if (active t : ℕ) < v.mid ∨ coin v = false then 1 / 2 - c else 0 else 0 := by
    have hval : (((v.1 : ℕ) : ℝ) + 1) / (2 * treeHeight h) = 1 / 2 - c := by
      linarith only [halg]
    by_cases ha : v.active (active t)
    · by_cases hb : (active t : ℕ) < v.mid
      · simp [u, i, treeBonusProb, hd.ne, ha, hb, hval]
      · cases he : coin v <;> simp [u, i, treeBonusProb, hd.ne, ha, hb, he, hval]
    · simp [u, i, treeBonusProb, ha]
  have hpair (w : TreeNode h) (hw : (w.1 : ℕ) = h) (t : ℕ) :
      u t (e.symm (.inl (w, false))) + u t (e.symm (.inl (w, true))) =
        if w.active (active t) then 1 else 0 := by
    by_cases ha : w.active (active t)
    · simpa [u, ha] using treeBonusProb_leaf_pair (U := U) (active t) w hw ha coin
        (leafCoin t) (selected (active t))
    · simp [u, treeBonusProb, ha]
  have hH : 0 < treeHeight h := by unfold treeHeight; positivity
  have hnonneg : 0 ≤ c := by dsimp [c]; positivity
  have hcle : c ≤ 1 / 2 := by
    have h : 0 ≤ (((v.1 : ℕ) : ℝ) + 1) / (2 * treeHeight h) := by positivity
    linarith only [halg, h]
  have hchild (t : ℕ) :=
    v.child_active_iff hd (active t)
  change (∀ t, ((l.active (active t) ↔ v.active (active t) ∧ (active t : ℕ) < v.mid) ∧
      (r.active (active t) ↔ v.active (active t) ∧ v.mid ≤ (active t : ℕ)))) at hchild
  constructor
  · intro hcoin
    apply pair_gain_lower q u i (e.symm (.inl (l, false))) (e.symm (.inl (l, true))) _
      (fun t ht => hq t ht i)
    intro t _
    rw [hpair l hv, haux t]
    by_cases ha : v.active (active t)
    · by_cases hb : (active t : ℕ) < v.mid
      · simp [(hchild t).1, ha, hb]
      · simp [(hchild t).1, ha, hb, hcoin]
    · simp [(hchild t).1, ha]
  · apply pair_gain_lower q u i (e.symm (.inl (r, false))) (e.symm (.inl (r, true))) _
      (fun t ht => hq t ht i)
    intro t _
    rw [hpair r hv, haux t]
    by_cases ha : v.active (active t)
    · by_cases hb : (active t : ℕ) < v.mid
      · have hc : ¬v.mid ≤ (active t : ℕ) := not_le_of_gt hb
        simp only [(hchild t).1, (hchild t).2, ha, hb, hc, true_and, true_or, if_true, if_false]
        linarith only [hnonneg]
      · have hc := le_of_not_gt hb
        simp only [(hchild t).2, ha, true_and, hc, if_true, hb, false_or]
        split <;> linarith only [hcle]
    · simp [(hchild t).1, (hchild t).2, ha]

/-- Root comparison for either action of an internal node. The left action
can get a bonus anywhere in the node's subtree. The right action can get a
bonus only in the right child's subtree. -/
theorem internal_root_support_gain {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) < h) (side : Bool)
    (active : ℕ → Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : ℕ → Fin N → ℝ)
    (hq : ∀ t < T, ∀ i, 0 ≤ q t i) :
    let i := e.symm (.inl (v, side))
    let w := if side then v.child hv true else v
    let u (t : ℕ) (j : Fin N) := treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    (∑ t ∈ Finset.range T, q t i) / (4 * treeHeight h) -
      (∑ t ∈ Finset.range T, if w.active (active t) then q t i else 0) / 2 ≤ bestSwapGain T q u i := by
  intro i w u
  let a := e.symm (.inl (TreeNode.root h, false))
  let b := e.symm (.inl (TreeNode.root h, true))
  have hh : 0 < h := by omega
  have hH : 0 < treeHeight h := by unfold treeHeight; positivity
  have hdepth : ((v.1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hv.le
  have hfrac : (((v.1 : ℕ) : ℝ) + 1) / (2 * treeHeight h) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    unfold treeHeight
    linarith
  have hr (t : ℕ) (_ht : t < T) : u t a + u t b = 1 / (2 * treeHeight h) := by
    simpa only [u, a, b, Equiv.apply_symm_apply] using
      treeBonusProb_root_pair (U := U) hh (active t) coin (leafCoin t) (selected (active t))
  have hi (t : ℕ) : u t i ≤ if w.active (active t) then 1 / 2 else 0 := by
    by_cases ht : v.active (active t)
    · by_cases he : (active t : ℕ) < v.mid
      · have hx : ¬ (v.child hv true).active (active t) := by
          intro ha
          exact (not_le_of_gt he) ((v.child_active_iff hv (active t)).2.mp ha).2
        cases side
        · simp [w, u, i, treeBonusProb, ht, hv.ne, he]
          simpa only [one_div] using hfrac
        · simp [w, u, i, treeBonusProb, ht, hv.ne, he, hx]
      · have hx : (v.child hv true).active (active t) :=
          (v.child_active_iff hv (active t)).2.mpr ⟨ht, le_of_not_gt he⟩
        cases side <;> cases hcoin : coin v <;>
          simp [w, u, i, treeBonusProb, ht, hv.ne, he, hx, hcoin] <;> simpa only [one_div] using hfrac
    · have hx : ¬ (v.child hv true).active (active t) :=
        fun ha => ht ((v.child_active_iff hv (active t)).2.mp ha).1
      cases side <;> simp [w, u, i, treeBonusProb, ht, hx]
  have hs (t : ℕ) (ht : t < T) :
      q t i * u t i ≤ (if w.active (active t) then q t i else 0) / 2 := by
    by_cases h : w.active (active t)
    · rw [if_pos h]
      have hb := hi t
      rw [if_pos h] at hb
      have he : q t i * (1 / 2) = q t i / 2 := by ring
      exact (mul_le_mul_of_nonneg_left hb (hq t ht i)).trans_eq he
    · rw [if_neg h, zero_div]
      have hh : u t i ≤ 0 := by simpa only [if_neg h] using hi t
      exact mul_nonpos_of_nonneg_of_nonpos (hq t ht i) hh
  have hsum := Finset.sum_le_sum (s := Finset.range T) fun t ht => hs t (Finset.mem_range.mp ht)
  rw [← Finset.sum_div] at hsum
  linarith only [hsum, root_bestSwapGain q u i a b (treeHeight h) hr]

/-- Case 3 of Appendix D.1 after averaging over the finite uniform table
of internal-node coins. The play mass in the left subtree is causal. -/
theorem deepest_left_coin_sum {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 = h)
    (active : ℕ → Fin (2 ^ h)) (leafCoin : ℕ → Bool) (selected : Fin (2 ^ h) → Fin M)
    (q : (TreeNode h → Bool) → ℕ → Fin N → ℝ)
    (hq : ∀ c t, t < T → ∀ i, 0 ≤ q c t i) :
    let i := e.symm (.inl (v, false))
    let l := v.child (by omega) false
    let _r := v.child (by omega) true
    let L (c : TreeNode h → Bool) := ∑ t ∈ Finset.range T, if l.active (active t) then q c t i else 0
    let Q (c : TreeNode h → Bool) := ∑ t ∈ Finset.range T, q c t i
    let u (c : TreeNode h → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) c (leafCoin t) (selected (active t)) (e j)
    (∀ c b, L (Function.update c v b) = L c) →
      (∑ c, Q c) / (184 * treeHeight h ^ 5) ≤ ∑ c, bestSwapGain T (q c) (u c) i := by
  intro i l r L Q u hL
  let R (c : TreeNode h → Bool) := ∑ t ∈ Finset.range T, if r.active (active t) then q c t i else 0
  let G (c : TreeNode h → Bool) := bestSwapGain T (q c) (u c) i
  let H := treeHeight h
  have hH : 1 ≤ H := by dsimp [H, treeHeight]; linarith [Nat.cast_nonneg (α := ℝ) h]
  have hH' : 0 < H := zero_lt_one.trans_le hH
  have hd : (v.1 : ℕ) < h := by omega
  have hl_sum (c : TreeNode h → Bool) :
      (∑ t ∈ Finset.range T, q c t i * (if l.active (active t) then 1 / (2 * H) else 0)) =
        L c / (2 * H) := by
    unfold L
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun t _ => by split <;> simp [div_eq_mul_inv]
  have hsplit (c : TreeNode h → Bool) :
      (∑ t ∈ Finset.range T, if v.active (active t) then q c t i else 0) = L c + R c := by
    unfold L R
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨hl, hr⟩ := v.child_active_iff hd (active t)
    by_cases ha : v.active (active t)
    · by_cases hb : (active t : ℕ) < v.mid
      · simp [l, r, hl, hr, ha, hb, not_le_of_gt hb]
      · simp [l, r, hl, hr, ha, hb, le_of_not_gt hb]
    · simp [l, r, hl, hr, ha]
  have h1' (c : TreeNode h → Bool) : (if c v = true then L c else 0) / (2 * H) ≤ G c := by
    by_cases hc : c v = true
    · rw [if_pos hc, ← hl_sum c]
      exact (deepest_left_comparisons e v hv active c leafCoin selected (q c) (hq c)).1 hc
    · simpa only [if_neg hc, zero_div] using bestSwapGain_nonneg (q c) (u c) i
  have h2' (c : TreeNode h → Bool) : R c / (2 * H) - L c / 2 ≤ G c := by
    have hh := (deepest_left_comparisons e v hv active c leafCoin selected (q c) (hq c)).2
    have he : (∑ t ∈ Finset.range T, q c t i *
        (if r.active (active t) then 1 / (2 * H) else if l.active (active t) then -(1 / 2) else 0)) =
        R c / (2 * H) - L c / 2 := by
      unfold R L
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases hr : r.active (active t)
      · have hl : ¬ l.active (active t) := by
          intro hl
          exact (not_lt_of_ge ((v.child_active_iff hd (active t)).2.mp hr).2)
            ((v.child_active_iff hd (active t)).1.mp hl).2
        simp [hr, hl, div_eq_mul_inv]
      · by_cases hl : l.active (active t) <;> simp [hr, hl, div_eq_mul_inv]
    exact he ▸ hh
  have h3' (c : TreeNode h → Bool) : Q c / (4 * H) - (L c + R c) / 2 ≤ G c := by
    rw [← hsplit c]
    simpa only [Bool.false_eq_true, if_false] using
      internal_root_support_gain e v hd false active c leafCoin selected (q c) (hq c)
  let x := ∑ c, L c
  let y := ∑ c, R c
  let total := ∑ c, Q c
  let gain := ∑ c, G c
  have hE := sum_on_fair_coin v true L hL
  have hl : x / (4 * H) ≤ gain := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (TreeNode h → Bool))) fun c _ => h1' c
    rw [← Finset.sum_div, hE] at hh
    exact (show x / (4 * H) = (x / 2) / (2 * H) by ring).le.trans hh
  have hr : y / (2 * H) - x / 2 ≤ gain := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (TreeNode h → Bool))) fun c _ => h2' c
    simpa only [Finset.sum_sub_distrib, ← Finset.sum_div] using hh
  have hroot : total / (4 * H) - (x + y) / 2 ≤ gain := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (TreeNode h → Bool))) fun c _ => h3' c
    simpa only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib] using hh
  have hx : 0 ≤ x := by
    refine Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun t ht => ?_
    split
    · exact hq c t (Finset.mem_range.mp ht) i
    · rfl
  have hg : 0 ≤ gain := Finset.sum_nonneg fun c _ => bestSwapGain_nonneg (q c) (u c) i
  have h1 : 4 * H ^ 2 * x ≤ 16 * H ^ 3 * gain := by
    have hh := (div_le_iff₀ (show 0 < 4 * H by positivity)).mp hl
    nlinarith only [mul_le_mul_of_nonneg_left hh (show 0 ≤ 4 * H ^ 2 by positivity)]
  have h2 : 2 * H * y - 2 * H ^ 2 * x ≤ 4 * H ^ 2 * gain := by
    have hh := mul_le_mul_of_nonneg_right hr (show 0 ≤ 4 * H ^ 2 by positivity)
    have he : (y / (2 * H) - x / 2) * (4 * H ^ 2) = 2 * H * y - 2 * H ^ 2 * x := by
      field_simp; ring
    rw [he] at hh
    nlinarith only [hh]
  have h3 : total - 2 * H * (x + y) ≤ 4 * H * gain := by
    have hh := mul_le_mul_of_nonneg_right hroot (show 0 ≤ 4 * H by positivity)
    have he : (total / (4 * H) - (x + y) / 2) * (4 * H) = total - 2 * H * (x + y) := by
      field_simp; ring
    rw [he] at hh
    nlinarith only [hh]
  exact internal_three_comparisons (x₂ := 0) (x₃ := y) hH hg hx le_rfl
    (by simpa only [mul_zero, add_zero] using h1)
    (by simpa only [add_zero] using h2)
    (by simpa only [add_zero] using h3)

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

/-- The conditional subtree masses used in the swap comparisons are
causal for the actual fixed-seed policy. -/
theorem treePlayProbability_subtree_independent {h M U N T : ℕ}
    (e : Fin N ≃ TreeAction h M U) (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (ha : Monotone active)
    (w v : TreeNode h) (hbefore : w.last ≤ v.mid) (η : ℝ)
    (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) (i : Fin N) (b : Bool) :
    let Q (c : TreeNode h → Bool) := ∑ t ∈ Finset.range T,
      if w.active (active t) then treePlayProbability e pick active η c leafCoin selected z draw t i else 0
    Q (Function.update coin v b) = Q coin := by
  intro Q
  have he (c : TreeNode h → Bool) :
      Q c = subtreePlayMass pick active w η c leafCoin selected z draw T (e i) := by
    unfold Q treePlayProbability subtreePlayMass
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : w.active (active t) <;> simp [ht]
  rw [he, he]
  exact subtreePlayMass_update_of_before pick active ha w v hbefore
    η coin leafCoin selected z draw T (e i) b

/-- Case 3 of Appendix D.1 for the actual learner with a fixed seed. -/
theorem deepest_left_coin_sum_policy {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 = h)
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (ha : Monotone active) (η : ℝ) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) :
    let i := e.symm (.inl (v, false))
    let q (coin : TreeNode h → Bool) := treePlayProbability e pick active η coin leafCoin selected z draw
    let u (coin : TreeNode h → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    (∑ c, ∑ t ∈ Finset.range T, q c t i) / (184 * treeHeight h ^ 5) ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by
  intro i q u
  refine deepest_left_coin_sum e v hv active leafCoin selected q (fun c t _ j => ?_) ?_
  · exact (treePlayProbability_isProbVec e pick active η c leafCoin selected z draw t).1 j
  · intro c b
    let hd : (v.1 : ℕ) < h := by omega
    exact treePlayProbability_subtree_independent e pick active ha (v.child hd false) v
      (v.child_edges hd).2.1.le η c leafCoin selected z draw i b

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.deepest_left_coin_sum_policy := @CalibeatBandit.deepest_left_coin_sum_policy
