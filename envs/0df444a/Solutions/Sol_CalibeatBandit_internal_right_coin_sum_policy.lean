-- Prove2me | solution 1 for CalibeatBandit.internal_right_coin_sum_policy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T18:47:34.719105+00:00
-- url     : https://prove2.me/submissions/83883a46-10cf-423e-9c98-0c68a754499c

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

/-- The three averaged comparisons for a right action with internal children. -/
theorem internal_right_gain_of_comparisons {H gain total x₁ x₂ x₃ : ℝ}
    (hH : 1 ≤ H) (hg : 0 ≤ gain) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (h₁ : x₂ / (2 * H) + x₁ / (4 * H) ≤ gain)
    (h₂ : x₃ / (2 * H) - (x₁ + x₂) / 2 ≤ gain)
    (h₃ : total / (4 * H) - (x₁ + x₂ + x₃) / 2 ≤ gain) :
    total / (184 * H ^ 5) ≤ gain := by
  have h : 0 < H := by linarith
  refine internal_three_comparisons (x₃ := x₃) hH hg hx₁ hx₂ ?_ ?_ ?_
  · have he : (16 * H ^ 3) * (x₂ / (2 * H) + x₁ / (4 * H)) =
        4 * H ^ 2 * x₁ + 8 * H ^ 2 * x₂ := by
      field_simp [ne_of_gt h]
      ring
    simpa only [he] using mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 16 * H ^ 3 by positivity)
  · have he : (4 * H ^ 2) * (x₃ / (2 * H) - (x₁ + x₂) / 2) =
        2 * H * x₃ - 2 * H ^ 2 * (x₁ + x₂) := by
      field_simp [ne_of_gt h]
      ring
    simpa only [he] using mul_le_mul_of_nonneg_left h₂ (show 0 ≤ 4 * H ^ 2 by positivity)
  · have he : (4 * H) * (total / (4 * H) - (x₁ + x₂ + x₃) / 2) =
        total - 2 * H * (x₁ + x₂ + x₃) := by
      field_simp [ne_of_gt h]
      ring
    simpa only [he] using mul_le_mul_of_nonneg_left h₃ (show 0 ≤ 4 * H by positivity)

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

private theorem weighted_gain_bound {N T : ℕ} (q u : ℕ → Fin N → ℝ) (i j : Fin N)
    (w : ℕ → ℝ) (hq : ∀ t < T, 0 ≤ q t i) (hw : ∀ t < T, w t ≤ u t j - u t i) :
    (∑ t ∈ Finset.range T, q t i * w t) ≤ bestSwapGain T q u i := by
  exact (Finset.sum_le_sum (s := Finset.range T) fun t ht => mul_le_mul_of_nonneg_left
    (hw t (Finset.mem_range.mp ht)) (hq t (Finset.mem_range.mp ht))).trans
      (swapGain_le_best q u i j)

/-- Swapping an internal action to the right child's left action gains
one level of bonus on the right subtree when the child does not switch. -/
theorem internal_right_child_first {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 < h) (side : Bool)
    (active : ℕ → Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : ℕ → Fin N → ℝ)
    (hq : ∀ t < T, ∀ i, 0 ≤ q t i) :
    let i := e.symm (.inl (v, side))
    let w := v.child (by omega) true
    let u (t : ℕ) (j : Fin N) := treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    let c := 1 / (2 * treeHeight h)
    coin w = false →
    (∑ t ∈ Finset.range T, q t i *
      (if w.active (active t) then c
       else if v.active (active t) ∧ side = false then -(1 / 2) else 0)) ≤ bestSwapGain T q u i := by
  intro i w u c hc
  have hd : (v.1 : ℕ) < h := by omega
  have hw : (w.1 : ℕ) < h := hv
  have hH : 0 < treeHeight h := by unfold treeHeight; positivity
  let d : ℝ := ((v.1 : ℕ) : ℝ) + 1
  let d' : ℝ := ((w.1 : ℕ) : ℝ) + 1
  have he : d' = d + 1 := by simp [d', d, w, TreeNode.child]
  have hfrac : d / (2 * treeHeight h) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    dsimp [d, treeHeight]
    have hdepth : ((v.1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hd.le
    linarith
  have hdiff : d' / (2 * treeHeight h) - d / (2 * treeHeight h) = c := by
    rw [← sub_div, he, add_sub_cancel_left]
  apply weighted_gain_bound q u i (e.symm (.inl (w, false))) _ (fun t ht => hq t ht i)
  intro t _
  by_cases hr : w.active (active t)
  · have ha := ((v.child_active_iff hd (active t)).2).mp hr
    have hsource : u t i ≤ d / (2 * treeHeight h) := by
      simp only [u, i, Equiv.apply_symm_apply, treeBonusProb, ha.1, hd.ne, not_lt_of_ge ha.2,
        if_true, if_false]
      split
      · exact le_rfl
      · exact div_nonneg (by unfold d; positivity) (by positivity)
    have htarget : u t (e.symm (.inl (w, false))) = d' / (2 * treeHeight h) := by
      by_cases hwr : (active t : ℕ) < w.mid <;>
        simp [u, treeBonusProb, hr, hw.ne, hwr, hc, d']
    rw [if_pos hr, ← hdiff, htarget]
    exact sub_le_sub_left hsource _
  · rw [if_neg hr]
    have htarget : u t (e.symm (.inl (w, false))) = 0 := by simp [u, treeBonusProb, hr]
    rw [htarget, zero_sub]
    by_cases ha : v.active (active t)
    · have hleft : (active t : ℕ) < v.mid := lt_of_not_ge fun h => hr ((v.child_active_iff hd (active t)).2.mpr ⟨ha, h⟩)
      cases side
      · simpa [u, i, treeBonusProb, ha, hd.ne, hleft, d] using neg_le_neg hfrac
      · simp [u, i, treeBonusProb, ha, hd.ne, hleft]
    · simp [u, i, treeBonusProb, ha]

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

/-- The right child's right action gains one level of bonus on its right
subtree when the child switches there. -/
theorem internal_right_child_second {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 < h) (side : Bool)
    (active : ℕ → Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : ℕ → Fin N → ℝ)
    (hq : ∀ t < T, ∀ i, 0 ≤ q t i) :
    let i := e.symm (.inl (v, side))
    let w := v.child (by omega) true
    let u (t : ℕ) (j : Fin N) := treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    let c := 1 / (2 * treeHeight h)
    (∑ t ∈ Finset.range T, q t i *
      (if w.active (active t) ∧ w.mid ≤ (active t : ℕ) ∧ coin w = true then c
       else if w.active (active t) ∨ (v.active (active t) ∧ side = false) then -(1 / 2)
       else 0)) ≤ bestSwapGain T q u i := by
  intro i w u c
  have hd : (v.1 : ℕ) < h := by omega
  have hw : (w.1 : ℕ) < h := hv
  have hH : 0 < treeHeight h := by unfold treeHeight; positivity
  let d : ℝ := ((v.1 : ℕ) : ℝ) + 1
  let dw : ℝ := ((w.1 : ℕ) : ℝ) + 1
  have he : dw = d + 1 := by simp [dw, d, w, TreeNode.child]
  have hfrac : d / (2 * treeHeight h) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    dsimp [d, treeHeight]
    have hdepth : ((v.1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hd.le
    linarith
  have hdiff : dw / (2 * treeHeight h) - d / (2 * treeHeight h) = c := by
    rw [← sub_div, he, add_sub_cancel_left]
  let j := e.symm (.inl (w, true))
  apply weighted_gain_bound q u i j _ (fun t ht => hq t ht i)
  intro t _
  have hsource : u t i ≤ d / (2 * treeHeight h) := by
    simp only [u, i, Equiv.apply_symm_apply, treeBonusProb, hd.ne, if_false]
    split_ifs <;> first | exact le_rfl | (unfold d; positivity)
  have hj : 0 ≤ u t j := (treeBonusProb_mem _ _ _ _ _).1
  by_cases hr : w.active (active t) ∧ w.mid ≤ (active t : ℕ) ∧ coin w = true
  · have htarget : u t j = dw / (2 * treeHeight h) := by
      simp [u, j, treeBonusProb, hr.1, hw.ne, not_lt_of_ge hr.2.1, hr.2.2, dw]
    rw [if_pos hr, ← hdiff, htarget]
    exact sub_le_sub_left hsource _
  · rw [if_neg hr]
    by_cases hx : w.active (active t) ∨ (v.active (active t) ∧ side = false)
    · rw [if_pos hx]
      linarith only [hsource.trans hfrac, hj]
    · rw [if_neg hx]
      have hzero : u t i = 0 := by
        by_cases ha : v.active (active t)
        · have hside : side = true := by
            cases side
            · exact (hx (Or.inr ⟨ha, rfl⟩)).elim
            · rfl
          have hleft : (active t : ℕ) < v.mid := lt_of_not_ge fun hh =>
            hx (Or.inl ((v.child_active_iff hd (active t)).2.mpr ⟨ha, hh⟩))
          simp [u, i, treeBonusProb, ha, hd.ne, hside, hleft]
        · simp [u, i, treeBonusProb, ha]
      rw [hzero, sub_zero]
      exact hj

/-- Mass in a subtree splits into the two child masses. -/
theorem sum_child_mass {h T : ℕ} (w : TreeNode h) (hw : (w.1 : ℕ) < h)
    (active : ℕ → Fin (2 ^ h)) (p : ℕ → ℝ) :
    (∑ t ∈ Finset.range T, if w.active (active t) then p t else 0) =
      (∑ t ∈ Finset.range T, if (w.child hw false).active (active t) then p t else 0) +
      (∑ t ∈ Finset.range T, if (w.child hw true).active (active t) then p t else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  obtain ⟨hl, hr⟩ := w.child_active_iff hw (active t)
  by_cases ha : w.active (active t)
  · by_cases ht : (active t : ℕ) < w.mid
    · simp [hl, hr, ha, ht, not_le_of_gt ht]
    · simp [hl, hr, ha, ht, le_of_not_gt ht]
  · simp [hl, hr, ha]

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

/-- Case 2 of Appendix D.1. Only play mass in the first grandchild is
independent of the right child's coin, which is revealed later. -/
theorem internal_right_coin_sum {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 < h) (active : ℕ → Fin (2 ^ h))
    (leafCoin : ℕ → Bool) (selected : Fin (2 ^ h) → Fin M)
    (q : (TreeNode h → Bool) → ℕ → Fin N → ℝ)
    (hq : ∀ c t, t < T → ∀ i, 0 ≤ q c t i) :
    let i := e.symm (.inl (v, true))
    let w := v.child (by omega) true
    let l := w.child hv false
    let L (c : TreeNode h → Bool) := ∑ t ∈ Finset.range T, if l.active (active t) then q c t i else 0
    let u (c : TreeNode h → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) c (leafCoin t) (selected (active t)) (e j)
    (∀ c b, L (Function.update c w b) = L c) →
    (∑ c, ∑ t ∈ Finset.range T, q c t i) / (184 * treeHeight h ^ 5) ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by
  classical
  intro i w l L u hL
  let r := w.child hv true
  let R (c : TreeNode h → Bool) := ∑ t ∈ Finset.range T, if r.active (active t) then q c t i else 0
  let W (c : TreeNode h → Bool) := ∑ t ∈ Finset.range T, if w.active (active t) then q c t i else 0
  let G (c : TreeNode h → Bool) := bestSwapGain T (q c) (u c) i
  let H := treeHeight h
  have hH : 1 ≤ H := by dsimp [H, treeHeight]; linarith only [Nat.cast_nonneg (α := ℝ) h]
  let x₁ := ∑ c, L c
  let x₂ := ∑ c, if c w = false then R c else 0
  let x₃ := ∑ c, if c w = true then R c else 0
  have hsplit (c : TreeNode h → Bool) : W c = L c + R c :=
    sum_child_mass w hv active (fun t => q c t i)
  have hRsum : (∑ c, R c) = x₂ + x₃ := by
    dsimp only [x₂, x₃]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by cases c w <;> simp
  have hWsum : (∑ c, W c) = x₁ + x₂ + x₃ := by
    simp_rw [hsplit, Finset.sum_add_distrib, hRsum]
    ring
  have h₁ : x₂ / (2 * H) + x₁ / (4 * H) ≤ ∑ c, G c := by
    have hh (c : TreeNode h → Bool) :
        (if c w = false then W c / (2 * H) else 0) ≤ G c := by
      by_cases hc : c w = false
      · rw [if_pos hc]
        have h := internal_right_child_first e v hv true active c leafCoin selected (q c) (hq c) hc
        convert h using 1
        unfold W H
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro t _
        by_cases ht : w.active (active t)
        · simp [ht, w]
          ring
        · simp [ht, w]
      · rw [if_neg hc]
        exact bestSwapGain_nonneg (q c) (u c) i
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun c _ => hh c
    have hs : (∑ c, if c w = false then W c / (2 * H) else 0) =
        x₂ / (2 * H) + x₁ / (4 * H) := by
      have hg (c : TreeNode h → Bool) :
          (if c w = false then W c / (2 * H) else 0) =
          (if c w = false then L c else 0) / (2 * H) +
          (if c w = false then R c else 0) / (2 * H) := by
        by_cases hc : c w = false
        · simp only [hc, if_true, hsplit, add_div]
        · simp [hc]
      rw [Finset.sum_congr rfl (fun c _ => hg c), Finset.sum_add_distrib,
        ← Finset.sum_div, ← Finset.sum_div, sum_on_fair_coin w false L hL]
      change (x₁ / 2) / (2 * H) + x₂ / (2 * H) = _
      ring
    rwa [hs] at hsum
  have h₂ : x₃ / (2 * H) - (x₁ + x₂) / 2 ≤ ∑ c, G c := by
    have hh (c : TreeNode h → Bool) :
        (if c w = true then R c / (2 * H) else -R c / 2) - L c / 2 ≤ G c := by
      have hp := internal_right_child_second e v hv true active c leafCoin selected (q c) (hq c)
      have he :
          (if c w = true then R c / (2 * H) else -R c / 2) - L c / 2 =
            ∑ t ∈ Finset.range T, q c t i *
              (if w.active (active t) ∧ w.mid ≤ (active t : ℕ) ∧ c w = true then 1 / (2 * H)
               else if w.active (active t) then -(1 / 2) else 0) := by
        have hm (t : ℕ) := w.child_active_iff hv (active t)
        by_cases hc : c w = true
        · rw [if_pos hc]
          unfold R L
          rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun t _ => ?_
          simp only [r, l, (hm t).1, (hm t).2]
          by_cases ha : w.active (active t)
          · by_cases he : (active t : ℕ) < w.mid
            · simp [ha, he, not_le_of_gt he]; ring
            · simp [hc, ha, he, le_of_not_gt he]; ring
          · simp [ha]
        · rw [if_neg hc]
          unfold R L
          rw [← Finset.sum_neg_distrib, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun t _ => ?_
          simp only [r, l, (hm t).1, (hm t).2]
          by_cases ha : w.active (active t)
          · by_cases he : (active t : ℕ) < w.mid
            · simp [ha, he, not_le_of_gt he, hc]; ring
            · simp [ha, he, le_of_not_gt he, hc]; ring
          · simp [ha]
      rw [he]
      simpa only [w, i, u, H, Bool.true_eq_false, and_false, or_false] using hp
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun c _ => hh c
    have hs (c : TreeNode h → Bool) :
        (if c w = true then R c / (2 * H) else -R c / 2) - L c / 2 =
          (if c w = true then R c else 0) / (2 * H) -
          ((if c w = false then R c else 0) + L c) / 2 := by
      cases c w
      · simp
        ring
      · simp
    rw [Finset.sum_congr rfl (fun c _ => hs c), Finset.sum_sub_distrib,
      ← Finset.sum_div, ← Finset.sum_div, Finset.sum_add_distrib] at hsum
    change x₃ / (2 * H) - (x₂ + x₁) / 2 ≤ ∑ c, G c at hsum
    rwa [add_comm x₁ x₂]
  have h₃ : (∑ c, ∑ t ∈ Finset.range T, q c t i) / (4 * H) -
      (x₁ + x₂ + x₃) / 2 ≤ ∑ c, G c := by
    have hh (c : TreeNode h → Bool) :
        (∑ t ∈ Finset.range T, q c t i) / (4 * H) - W c / 2 ≤ G c :=
      internal_root_support_gain e v (by omega) true active c leafCoin selected (q c) (hq c)
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun c _ => hh c
    simpa only [Finset.sum_sub_distrib, ← Finset.sum_div, hWsum] using hsum
  have hLn : ∀ c, 0 ≤ L c := fun c => Finset.sum_nonneg fun t ht => by
    split
    · exact hq c t (Finset.mem_range.mp ht) i
    · exact le_rfl
  have hRn : ∀ c, 0 ≤ R c := fun c => Finset.sum_nonneg fun t ht => by
    split
    · exact hq c t (Finset.mem_range.mp ht) i
    · exact le_rfl
  exact internal_right_gain_of_comparisons hH
    (Finset.sum_nonneg fun c _ => bestSwapGain_nonneg (q c) (u c) i)
    (Finset.sum_nonneg fun c _ => hLn c)
    (Finset.sum_nonneg fun c _ => by split; exact hRn c; exact le_rfl) h₁ h₂ h₃

/-- The right action of a node above the deepest internal level satisfies
its averaged comparison for the actual learner with a fixed seed. -/
theorem internal_right_coin_sum_policy {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 < h)
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (ha : Monotone active) (η : ℝ) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) :
    let i := e.symm (.inl (v, true))
    let q (coin : TreeNode h → Bool) := treePlayProbability e pick active η coin leafCoin selected z draw
    let u (coin : TreeNode h → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    (∑ c, ∑ t ∈ Finset.range T, q c t i) / (184 * treeHeight h ^ 5) ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by
  intro i q u
  refine internal_right_coin_sum e v hv active leafCoin selected q (fun c t _ j => ?_) ?_
  · exact (treePlayProbability_isProbVec e pick active η c leafCoin selected z draw t).1 j
  · intro c b
    let w := v.child (by omega) true
    exact treePlayProbability_subtree_independent e pick active ha (w.child hv false) w
      (w.child_edges hv).2.1.le η c leafCoin selected z draw i b

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.internal_right_coin_sum_policy := @CalibeatBandit.internal_right_coin_sum_policy
