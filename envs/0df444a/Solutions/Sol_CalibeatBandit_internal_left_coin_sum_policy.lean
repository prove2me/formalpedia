-- Prove2me | solution 1 for CalibeatBandit.internal_left_coin_sum_policy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T18:47:33.802619+00:00
-- url     : https://prove2.me/submissions/748916ef-723c-4848-a077-490971dd6140

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

/-- The five weighted comparisons in Appendix D.1, Case 1.
The inputs are the nonnegative play masses in the six subtree events. -/
theorem internal_left_gain {H gain total x₁ x₂ x₃ x₄ x₅ x₆ : ℝ}
    (hH : 1 ≤ H) (hg : 0 ≤ gain)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hx₃ : 0 ≤ x₃)
    (hx₄ : 0 ≤ x₄) (hx₅ : 0 ≤ x₅)
    (h₁ : 16 * H ^ 4 * x₁ + 32 * H ^ 4 * x₂ ≤ 128 * H ^ 5 * gain)
    (h₂ : 8 * H ^ 3 * x₃ - 8 * H ^ 4 * x₂ - 8 * H ^ 4 * x₁ ≤ 32 * H ^ 4 * gain)
    (h₃ : 8 * H ^ 2 * x₅ + 4 * H ^ 2 * x₄ - 4 * H ^ 3 * (x₁ + x₂ + x₃) ≤
      16 * H ^ 3 * gain)
    (h₄ : 2 * H * x₆ - 2 * H ^ 2 * x₅ - 2 * H ^ 2 * x₄ -
      2 * H ^ 2 * (x₁ + x₂ + x₃) ≤ 4 * H ^ 2 * gain)
    (h₅ : total - 2 * H * (x₁ + x₂ + x₃ + x₄ + x₅ + x₆) ≤ 4 * H * gain) :
    total / (184 * H ^ 5) ≤ gain := by
  have hpos : 0 < H := by linarith
  have hgap : 0 ≤ H - 1 := sub_nonneg.mpr hH
  let c₁ := 2 * H * (H - 1) * (4 * H ^ 2 + 2 * H + 1)
  let c₂ := 16 * H ^ 4 + c₁
  let c₃ := 2 * H * (H - 1) * (2 * H + 1)
  let c₄ := 2 * H * (H - 1)
  let c₅ := 2 * H * (3 * H - 1)
  have hc₁ : 0 ≤ c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0 ≤ c₂ := by dsimp [c₂]; positivity
  have hc₃ : 0 ≤ c₃ := by dsimp [c₃]; positivity
  have hc₄ : 0 ≤ c₄ := by dsimp [c₄]; positivity
  have hc₅ : 0 ≤ c₅ := by
    have h : 0 ≤ 3 * H - 1 := by linarith
    dsimp [c₅]
    positivity
  have hsum : total + c₁ * x₁ + c₂ * x₂ + c₃ * x₃ + c₄ * x₄ + c₅ * x₅ ≤
      (128 * H ^ 5 + 32 * H ^ 4 + 16 * H ^ 3 + 4 * H ^ 2 + 4 * H) * gain := by
    dsimp [c₁, c₂, c₃, c₄, c₅]
    linear_combination h₁ + h₂ + h₃ + h₄ + h₅
  have hmass : total ≤ total + c₁ * x₁ + c₂ * x₂ + c₃ * x₃ + c₄ * x₄ + c₅ * x₅ := by
    linarith only [mul_nonneg hc₁ hx₁, mul_nonneg hc₂ hx₂, mul_nonneg hc₃ hx₃,
      mul_nonneg hc₄ hx₄, mul_nonneg hc₅ hx₅]
  have hcoeff : 128 * H ^ 5 + 32 * H ^ 4 + 16 * H ^ 3 + 4 * H ^ 2 + 4 * H ≤
      184 * H ^ 5 := by
    have p (n : ℕ) (hn : n ≤ 5) : H ^ n ≤ H ^ 5 := pow_le_pow_right₀ hH hn
    nlinarith only [p 4 (by omega), p 3 (by omega), p 2 (by omega), p 1 (by omega),
      show H ^ 1 = H by ring]
  apply (div_le_iff₀ (by positivity)).mpr
  calc
    total ≤ _ := hmass.trans hsum
    _ ≤ 184 * H ^ 5 * gain := mul_le_mul_of_nonneg_right hcoeff hg
    _ = gain * (184 * H ^ 5) := mul_comm _ _

/-- The five averaged comparisons for a left action with internal children,
before rescaling to a common denominator. -/
theorem internal_left_gain_of_comparisons {H gain total x₁ x₂ x₃ x₄ x₅ x₆ : ℝ}
    (hH : 1 ≤ H) (hg : 0 ≤ gain)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hx₃ : 0 ≤ x₃)
    (hx₄ : 0 ≤ x₄) (hx₅ : 0 ≤ x₅)
    (h₁ : x₁ / (8 * H) + x₂ / (4 * H) ≤ gain)
    (h₂ : x₃ / (4 * H) - (x₁ + x₂) / 4 ≤ gain)
    (h₃ : x₅ / (2 * H) + x₄ / (4 * H) - (x₁ + x₂ + x₃) / 4 ≤ gain)
    (h₄ : x₆ / (2 * H) - (x₅ + x₄ + x₁ + x₂ + x₃) / 2 ≤ gain)
    (h₅ : total / (4 * H) - (x₁ + x₂ + x₃ + x₄ + x₅ + x₆) / 2 ≤ gain) :
    total / (184 * H ^ 5) ≤ gain := by
  have h : 0 < H := by linarith
  refine internal_left_gain (x₆ := x₆) hH hg hx₁ hx₂ hx₃ hx₄ hx₅ ?_ ?_ ?_ ?_ ?_
  · have he : (128 * H ^ 5) * (x₁ / (8 * H) + x₂ / (4 * H)) =
        16 * H ^ 4 * x₁ + 32 * H ^ 4 * x₂ := by
      field_simp [ne_of_gt h]
      ring
    simpa only [he] using mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 128 * H ^ 5 by positivity)
  · have he : (32 * H ^ 4) * (x₃ / (4 * H) - (x₁ + x₂) / 4) =
        8 * H ^ 3 * x₃ - 8 * H ^ 4 * x₂ - 8 * H ^ 4 * x₁ := by
      field_simp [ne_of_gt h]
      ring
    simpa only [he] using mul_le_mul_of_nonneg_left h₂ (show 0 ≤ 32 * H ^ 4 by positivity)
  · have he : (16 * H ^ 3) * (x₅ / (2 * H) + x₄ / (4 * H) - (x₁ + x₂ + x₃) / 4) =
        8 * H ^ 2 * x₅ + 4 * H ^ 2 * x₄ - 4 * H ^ 3 * (x₁ + x₂ + x₃) := by
      field_simp [ne_of_gt h]
      ring
    simpa only [he] using mul_le_mul_of_nonneg_left h₃ (show 0 ≤ 16 * H ^ 3 by positivity)
  · have he : (4 * H ^ 2) * (x₆ / (2 * H) - (x₅ + x₄ + x₁ + x₂ + x₃) / 2) =
        2 * H * x₆ - 2 * H ^ 2 * x₅ - 2 * H ^ 2 * x₄ - 2 * H ^ 2 * (x₁ + x₂ + x₃) := by
      field_simp [ne_of_gt h]
      ring
    simpa only [he] using mul_le_mul_of_nonneg_left h₄ (show 0 ≤ 4 * H ^ 2 by positivity)
  · have he : (4 * H) * (total / (4 * H) - (x₁ + x₂ + x₃ + x₄ + x₅ + x₆) / 2) =
        total - 2 * H * (x₁ + x₂ + x₃ + x₄ + x₅ + x₆) := by
      field_simp [ne_of_gt h]
      ring
    simpa only [he] using mul_le_mul_of_nonneg_left h₅ (show 0 ≤ 4 * H by positivity)

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

/-- The left-child comparisons for a left action above the deepest
internal level. The event on the parent coin kills its right-subtree bonus. -/
theorem internal_left_child_comparisons {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 < h)
    (active : ℕ → Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : ℕ → Fin N → ℝ)
    (hq : ∀ t < T, ∀ i, 0 ≤ q t i) :
    let i := e.symm (.inl (v, false))
    let w := v.child (by omega) false
    let u (t : ℕ) (j : Fin N) := treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    let c := 1 / (2 * treeHeight h)
    coin v = true →
      (coin w = false →
        (∑ t ∈ Finset.range T, q t i * (if w.active (active t) then c else 0)) ≤ bestSwapGain T q u i) ∧
      (∑ t ∈ Finset.range T, q t i *
        (if w.active (active t) ∧ w.mid ≤ (active t : ℕ) ∧ coin w = true then c
         else if w.active (active t) then -(1 / 2) else 0)) ≤ bestSwapGain T q u i := by
  intro i w u c hc
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
  have hsource (t : ℕ) : u t i = if w.active (active t) then d / (2 * treeHeight h) else 0 := by
    have ha : w.active (active t) ↔ v.active (active t) ∧ (active t : ℕ) < v.mid :=
      (v.child_active_iff hd (active t)).1
    by_cases ht : v.active (active t)
    · by_cases hl : (active t : ℕ) < v.mid
      · have hwa := ha.mpr ⟨ht, hl⟩
        simp [u, i, treeBonusProb, ht, hd.ne, hl, d, hwa]
      · have hnwa : ¬ w.active (active t) := fun hh => hl (ha.mp hh).2
        simp [u, i, treeBonusProb, ht, hd.ne, hl, hc, hnwa]
    · have hnwa : ¬ w.active (active t) := fun hh => ht (ha.mp hh).1
      simp [u, i, treeBonusProb, ht, hnwa]
  constructor
  · intro hwc
    apply weighted_gain_bound q u i (e.symm (.inl (w, false))) _ (fun t ht => hq t ht i)
    intro t _
    rw [hsource t]
    by_cases hr : w.active (active t)
    · have htarget : u t (e.symm (.inl (w, false))) = dw / (2 * treeHeight h) := by
        by_cases hl : (active t : ℕ) < w.mid <;> simp [u, treeBonusProb, hr, hw.ne, hl, hwc, dw]
      rw [htarget]
      simp only [if_pos hr, hdiff]
      exact le_rfl
    · simp [u, treeBonusProb, hr]
  · let j := e.symm (.inl (w, true))
    apply weighted_gain_bound q u i j _ (fun t ht => hq t ht i)
    intro t _
    rw [hsource t]
    by_cases hr : w.active (active t)
    · by_cases hd' : w.mid ≤ (active t : ℕ) ∧ coin w = true
      · have htarget : u t j = dw / (2 * treeHeight h) := by
          simp [u, j, treeBonusProb, hr, hw.ne, not_lt_of_ge hd'.1, hd'.2, dw]
        rw [if_pos ⟨hr, hd'⟩, if_pos hr, htarget, hdiff]
      · have hj : 0 ≤ u t j := (treeBonusProb_mem _ _ _ _ _).1
        rw [if_neg (fun h => hd' h.2), if_pos hr, if_pos hr]
        linarith only [hfrac, hj]
    · simp [u, j, treeBonusProb, hr]

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

/-- Left subtrees finish before the midpoint of the parent and before the
midpoint of its right child. Right subtrees finish at their parent's end. -/
theorem child_timing {h : ℕ} (w : TreeNode h) (hw : (w.1 : ℕ) < h) :
    (w.child hw false).last = w.mid ∧
    (w.child hw true).first = w.mid ∧
    (w.child hw true).last = w.last ∧
    (w.child hw false).mid ≤ w.mid ∧
    w.mid ≤ (w.child hw true).mid := by
  obtain ⟨_, hl, hr, he⟩ := w.child_edges hw
  have hmid (j : TreeNode h) : j.first ≤ j.mid ∧ j.mid ≤ j.last := by
    unfold TreeNode.mid TreeNode.last TreeNode.first
    rw [Nat.add_mul, one_mul]
    exact ⟨Nat.le_add_right _ _, Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) (by omega)) _⟩
  exact ⟨hl, hr, he, (hmid _).2.trans_eq hl, hr.symm.trans_le (hmid _).1⟩

/-- If the weight is unchanged when a coin is updated, a gate on a distinct
coin can be included in that weight before summing over the first coin. -/
theorem sum_on_two_coins {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j k : ι) (hjk : k ≠ j) (b d : Bool) (g : (ι → Bool) → ℝ)
    (hg : ∀ c v, g (Function.update c j v) = g c) :
    (∑ c : ι → Bool, if c j = b ∧ c k = d then g c else 0) =
      (∑ c, if c k = d then g c else 0) / 2 := by
  let f (c : ι → Bool) := if c k = d then g c else 0
  have hf (c : ι → Bool) (v : Bool) : f (Function.update c j v) = f c := by
    simp only [f, Function.update_of_ne hjk, hg c v]
  have hh := sum_on_fair_coin j b f hf
  simpa only [f, ite_and] using hh

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

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open Set

/-- Play mass of one action during the visits to a subtree. -/
private noncomputable def visitMass {h T : ℕ} (active : ℕ → Fin (2 ^ h)) (p : ℕ → ℝ)
    (v : TreeNode h) : ℝ :=
  ∑ t ∈ Finset.range T, if v.active (active t) then p t else 0

private theorem visitMass_nonneg {h T : ℕ} (active : ℕ → Fin (2 ^ h)) (p : ℕ → ℝ)
    (hp : ∀ t < T, 0 ≤ p t) (v : TreeNode h) :
    0 ≤ visitMass (T := T) active p v :=
  Finset.sum_nonneg fun t ht => by
    split
    · exact hp t (Finset.mem_range.mp ht)
    · exact le_rfl

private theorem visitMass_split {h T : ℕ} (active : ℕ → Fin (2 ^ h)) (p : ℕ → ℝ)
    (v : TreeNode h) (hv : (v.1 : ℕ) < h) :
    visitMass (T := T) active p v =
      visitMass (T := T) active p (v.child hv false) + visitMass (T := T) active p (v.child hv true) :=
  sum_child_mass v hv active p

private theorem visitMass_weight {h T : ℕ} (active : ℕ → Fin (2 ^ h)) (p : ℕ → ℝ)
    (v : TreeNode h) (a : ℝ) :
    (∑ t ∈ Finset.range T, p t * (if v.active (active t) then a else 0)) =
      visitMass (T := T) active p v * a := by
  rw [visitMass, Finset.sum_mul]
  exact Finset.sum_congr rfl fun t _ => by split <;> simp [*]

/-- Expand the left-action comparison within an internal child's subtree. -/
private theorem visitMass_child_switch {h T : ℕ} (active : ℕ → Fin (2 ^ h)) (p : ℕ → ℝ)
    (v : TreeNode h) (hv : (v.1 : ℕ) < h) (b : Bool) (a : ℝ) :
    (∑ t ∈ Finset.range T, p t *
      (if v.active (active t) ∧ v.mid ≤ (active t : ℕ) ∧ b = true then a
       else if v.active (active t) then -(1 / 2) else 0)) =
      (if b = true then visitMass (T := T) active p (v.child hv true) else 0) * a -
      ((if b = false then visitMass (T := T) active p (v.child hv true) else 0) +
        visitMass (T := T) active p (v.child hv false)) / 2 := by
  cases b
  · simp only [Bool.false_eq_true, and_false, if_false, if_true]
    rw [visitMass_weight, visitMass_split active p v hv]
    ring
  · simp only [Bool.true_eq_false, and_true, if_true, if_false, zero_add]
    unfold visitMass
    rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨hl, hr⟩ := v.child_active_iff hv (active t)
    by_cases hactive : v.active (active t)
    · by_cases hleft : (active t : ℕ) < v.mid
      · simp [hl, hr, hactive, hleft, not_le_of_gt hleft]
        ring
      · simp [hl, hr, hactive, hleft, le_of_not_gt hleft]
    · simp [hl, hr, hactive]

private theorem visitMass_compare_right {h T : ℕ} (active : ℕ → Fin (2 ^ h)) (p : ℕ → ℝ)
    (v : TreeNode h) (hv : (v.1 : ℕ) < h) (a : ℝ) :
    (∑ t ∈ Finset.range T, p t *
      (if (v.child hv true).active (active t) then a
       else if v.active (active t) then -(1 / 2) else 0)) =
      visitMass (T := T) active p (v.child hv true) * a -
        visitMass (T := T) active p (v.child hv false) / 2 := by
  unfold visitMass
  rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  obtain ⟨hl, hr⟩ := v.child_active_iff hv (active t)
  by_cases hactive : v.active (active t)
  · by_cases hleft : (active t : ℕ) < v.mid
    · simp [hl, hr, hactive, hleft, not_le_of_gt hleft]
      ring
    · simp [hl, hr, hactive, hleft, le_of_not_gt hleft]
  · simp [hl, hr, hactive]

private theorem visitMass_compare_right_switch {h T : ℕ} (active : ℕ → Fin (2 ^ h)) (p : ℕ → ℝ)
    (v : TreeNode h) (hv : (v.1 : ℕ) < h) (w : TreeNode h) (hw : w = v.child hv true)
    (hv' : (w.1 : ℕ) < h) (b : Bool) (a : ℝ) :
    (∑ t ∈ Finset.range T, p t *
      (if w.active (active t) ∧ w.mid ≤ (active t : ℕ) ∧ b = true then a
       else if w.active (active t) ∨ v.active (active t) then -(1 / 2) else 0)) =
      (if b = true then visitMass (T := T) active p (w.child hv' true) else 0) * a -
      ((if b = false then visitMass (T := T) active p (w.child hv' true) else 0) +
        visitMass (T := T) active p (w.child hv' false) +
        visitMass (T := T) active p (v.child hv false)) / 2 := by
  subst w
  let w := v.child hv true
  have hs :=
    visitMass_child_switch (T := T) active p w hv' b a
  calc
    _ = (∑ t ∈ Finset.range T, p t *
          (if w.active (active t) ∧ w.mid ≤ (active t : ℕ) ∧ b = true then a
           else if w.active (active t) then -(1 / 2) else 0)) -
          visitMass (T := T) active p (v.child hv false) / 2 := by
      rw [visitMass, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      obtain ⟨hl, hr⟩ := v.child_active_iff hv (active t)
      by_cases hactive : v.active (active t)
      · by_cases hleft : (active t : ℕ) < v.mid
        · have hright : ¬ w.active (active t) := fun ht => (not_le_of_gt hleft) (hr.mp ht).2
          simp [hl, hactive, hleft, hright, w]
          ring
        · have hright : w.active (active t) := hr.mpr ⟨hactive, le_of_not_gt hleft⟩
          simp only [hl, hactive, hleft, and_false, if_false, hright, or_true, if_true,
            zero_div, sub_zero, w]
      · have hright : ¬ w.active (active t) := fun ht => hactive (hr.mp ht).1
        simp [hl, hactive, hright, w]
    _ = _ := by
      rw [hs]
      ring

private theorem sum_by_bool {A : Type*} [Fintype A] (b : A → Bool) (p : A → ℝ) :
    (∑ x, if b x = false then p x else 0) + (∑ x, if b x = true then p x else 0) =
      ∑ x, p x := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by cases b x <;> simp

/-- Case 1 of Appendix D.1. The four child comparisons and the root comparison
yield the expected gain for a left action above the deepest internal level. -/
theorem internal_left_coin_sum_policy {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 < h)
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (ha : Monotone active) (η : ℝ) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) :
    let i := e.symm (.inl (v, false))
    let q (c : TreeNode h → Bool) := treePlayProbability e pick active η c leafCoin selected z draw
    let u (c : TreeNode h → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) c (leafCoin t) (selected (active t)) (e j)
    (∑ c, ∑ t ∈ Finset.range T, q c t i) / (184 * treeHeight h ^ 5) ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by
  classical
  intro i q u
  let hnode : (v.1 : ℕ) < h := by omega
  let l := v.child hnode false
  let r := v.child hnode true
  have hl : (l.1 : ℕ) < h := hv
  have hr : (r.1 : ℕ) < h := hv
  have hne : l ≠ v := by
    intro he
    have hd := congrArg (fun w : TreeNode h => (w.1 : ℕ)) he
    change (v.1 : ℕ) + 1 = (v.1 : ℕ) at hd
    omega
  let p (c : TreeNode h → Bool) (t : ℕ) := q c t i
  let Q (w : TreeNode h) (c : TreeNode h → Bool) := visitMass (T := T) active (p c) w
  let LL := Q (l.child hl false)
  let LR := Q (l.child hl true)
  let RL := Q (r.child hr false)
  let RR := Q (r.child hr true)
  let G (c : TreeNode h → Bool) := bestSwapGain T (q c) (u c) i
  let H := treeHeight h
  have hH : 1 ≤ H := by dsimp [H, treeHeight]; linarith only [Nat.cast_nonneg (α := ℝ) h]
  let a := 1 / (2 * H)
  let x₁ := ∑ c, LL c
  let x₂ := ∑ c, if c l = false then LR c else 0
  let x₃ := ∑ c, if c l = true then LR c else 0
  let x₄ := ∑ c, RL c
  let x₅ := ∑ c, if c r = false then RR c else 0
  let x₆ := ∑ c, if c r = true then RR c else 0
  have hq (c : TreeNode h → Bool) (t : ℕ) (_ : t < T) (j : Fin N) : 0 ≤ q c t j :=
    (treePlayProbability_isProbVec e pick active η c leafCoin selected z draw t).1 j
  have hn (w : TreeNode h) (c : TreeNode h → Bool) : 0 ≤ Q w c :=
    visitMass_nonneg active (p c) (fun t ht => hq c t ht i) w
  have hg (c : TreeNode h → Bool) : 0 ≤ G c := bestSwapGain_nonneg (q c) (u c) i
  have h_split (w : TreeNode h) (hw : (w.1 : ℕ) < h) (c : TreeNode h → Bool) :
      Q w c = Q (w.child hw false) c + Q (w.child hw true) c :=
    visitMass_split active (p c) w hw
  have hsplit_l (c : TreeNode h → Bool) : Q l c = LL c + LR c := h_split l hl c
  have hsplit_r (c : TreeNode h → Bool) : Q r c = RL c + RR c := h_split r hr c
  have hsum_l : (∑ c, Q l c) = x₁ + x₂ + x₃ := by
    rw [Finset.sum_congr rfl (fun c _ => hsplit_l c), Finset.sum_add_distrib]
    change x₁ + (∑ c, LR c) = x₁ + x₂ + x₃
    rw [← sum_by_bool (fun c : TreeNode h → Bool => c l) LR]
    change x₁ + (x₂ + x₃) = x₁ + x₂ + x₃
    ring
  have hsum_r : (∑ c, Q r c) = x₄ + x₅ + x₆ := by
    rw [Finset.sum_congr rfl (fun c _ => hsplit_r c), Finset.sum_add_distrib]
    change x₄ + (∑ c, RR c) = x₄ + x₅ + x₆
    rw [← sum_by_bool (fun c : TreeNode h → Bool => c r) RR]
    change x₄ + (x₅ + x₆) = x₄ + x₅ + x₆
    ring
  have h_indep (w w' : TreeNode h) (ht : w.last ≤ w'.mid) (c : TreeNode h → Bool) (b : Bool) :
      Q w (Function.update c w' b) = Q w c :=
    treePlayProbability_subtree_independent e pick active ha w w' ht η c leafCoin selected z draw i b
  have hl_end : l.last = v.mid := (child_timing v hnode).1
  have hr_mid : v.mid ≤ r.mid := (child_timing v hnode).2.2.2.2
  have hLL_end : (l.child hl false).last = l.mid := (child_timing l hl).1
  have hLR_end : (l.child hl true).last = l.last := (child_timing l hl).2.2.1
  have hRL_end : (r.child hr false).last = r.mid := (child_timing r hr).1
  have hl_mid : l.mid ≤ v.mid := (child_timing v hnode).2.2.2.1
  have hLL_v := h_indep (l.child hl false) v (hLL_end.trans_le hl_mid)
  have hLL_l := h_indep (l.child hl false) l hLL_end.le
  have hLR_v := h_indep (l.child hl true) v (hLR_end.trans_le hl_end.le)
  have hL_r := h_indep l r (hl_end.trans_le hr_mid)
  have hRL_r := h_indep (r.child hr false) r hRL_end.le
  have hLL_true : (∑ c : TreeNode h → Bool, if c v = true then LL c else 0) = x₁ / 2 :=
    sum_on_fair_coin v true LL hLL_v
  have hLL_true_false :
      (∑ c : TreeNode h → Bool, if c v = true ∧ c l = false then LL c else 0) = x₁ / 4 := by
    rw [sum_on_two_coins v l hne true false LL hLL_v, sum_on_fair_coin l false LL hLL_l]
    change (x₁ / 2) / 2 = x₁ / 4
    ring
  have hLR_true_false :
      (∑ c : TreeNode h → Bool, if c v = true ∧ c l = false then LR c else 0) = x₂ / 2 :=
    sum_on_two_coins v l hne true false LR hLR_v
  have hLR_true_true :
      (∑ c : TreeNode h → Bool, if c v = true ∧ c l = true then LR c else 0) = x₃ / 2 :=
    sum_on_two_coins v l hne true true LR hLR_v
  have hRL_false : (∑ c : TreeNode h → Bool, if c r = false then RL c else 0) = x₄ / 2 :=
    sum_on_fair_coin r false RL hRL_r
  have hL_false : (∑ c : TreeNode h → Bool, if c r = false then Q l c else 0) =
      (x₁ + x₂ + x₃) / 2 := by
    rw [sum_on_fair_coin r false (Q l) hL_r, hsum_l]
  have h₁ : x₁ / (8 * H) + x₂ / (4 * H) ≤ ∑ c, G c := by
    have hc (c : TreeNode h → Bool) :
        ((if c v = true ∧ c l = false then LL c else 0) +
          (if c v = true ∧ c l = false then LR c else 0)) * a ≤ G c := by
      by_cases hcoin : c v = true ∧ c l = false
      · have hb := (internal_left_child_comparisons e v hv active c leafCoin selected (q c) (hq c)
          hcoin.1).1 hcoin.2
        change (∑ t ∈ Finset.range T, p c t * (if l.active (active t) then a else 0)) ≤ G c at hb
        rw [visitMass_weight] at hb
        change Q l c * a ≤ G c at hb
        rwa [if_pos hcoin, if_pos hcoin, ← hsplit_l]
      · simpa only [hcoin, if_false, add_zero, zero_mul] using hg c
    have hs := Finset.sum_le_sum (s := Finset.univ) fun c _ => hc c
    rw [← Finset.sum_mul, Finset.sum_add_distrib, hLL_true_false, hLR_true_false] at hs
    have he : (x₁ / 4 + x₂ / 2) * a = x₁ / (8 * H) + x₂ / (4 * H) := by
      dsimp only [a]
      ring
    exact he ▸ hs
  have h₂ : x₃ / (4 * H) - (x₁ + x₂) / 4 ≤ ∑ c, G c := by
    have hc (c : TreeNode h → Bool) :
        (if c v = true ∧ c l = true then LR c else 0) * a -
          ((if c v = true then LL c else 0) +
            (if c v = true ∧ c l = false then LR c else 0)) / 2 ≤ G c := by
      by_cases hcoin : c v = true
      · have hb := (internal_left_child_comparisons e v hv active c leafCoin selected (q c) (hq c)
          hcoin).2
        change (∑ t ∈ Finset.range T, p c t *
          (if l.active (active t) ∧ l.mid ≤ (active t : ℕ) ∧ c l = true then a
           else if l.active (active t) then -(1 / 2) else 0)) ≤ G c at hb
        rw [visitMass_child_switch active (p c) l hl] at hb
        simpa only [hcoin, true_and, if_true, add_comm, LL, LR, Q] using hb
      · by_cases hc : c l = true
        · simpa [hcoin, hc] using hg c
        · simpa [hcoin, hc] using hg c
    have hs := Finset.sum_le_sum (s := Finset.univ) fun c _ => hc c
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, Finset.sum_add_distrib,
      hLR_true_true, hLL_true, hLR_true_false] at hs
    have he : (x₃ / 2) * a - (x₁ / 2 + x₂ / 2) / 2 = x₃ / (4 * H) - (x₁ + x₂) / 4 := by
      dsimp only [a]
      ring
    exact he ▸ hs
  have h₃ : x₅ / (2 * H) + x₄ / (4 * H) - (x₁ + x₂ + x₃) / 4 ≤ ∑ c, G c := by
    have hc (c : TreeNode h → Bool) :
        ((if c r = false then RL c else 0) + (if c r = false then RR c else 0)) * a -
          (if c r = false then Q l c else 0) / 2 ≤ G c := by
      by_cases hcoin : c r = false
      · have hb := internal_right_child_first e v hv false active c leafCoin selected (q c) (hq c) hcoin
        simp only [and_true] at hb
        change (∑ t ∈ Finset.range T, p c t *
          (if r.active (active t) then a else if v.active (active t) then -(1 / 2) else 0)) ≤ G c at hb
        rw [visitMass_compare_right] at hb
        change Q r c * a - Q l c / 2 ≤ G c at hb
        simpa only [hcoin, if_true, ← hsplit_r] using hb
      · simpa [hcoin] using hg c
    have hs := Finset.sum_le_sum (s := Finset.univ) fun c _ => hc c
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, Finset.sum_add_distrib,
      hRL_false, hL_false] at hs
    change (x₄ / 2 + x₅) * a - ((x₁ + x₂ + x₃) / 2) / 2 ≤ ∑ c, G c at hs
    have he : (x₄ / 2 + x₅) * a - ((x₁ + x₂ + x₃) / 2) / 2 =
        x₅ / (2 * H) + x₄ / (4 * H) - (x₁ + x₂ + x₃) / 4 := by
      dsimp only [a]
      ring
    exact he ▸ hs
  have h₄ : x₆ / (2 * H) - (x₅ + x₄ + x₁ + x₂ + x₃) / 2 ≤ ∑ c, G c := by
    have hc (c : TreeNode h → Bool) :
        (if c r = true then RR c else 0) * a -
          ((if c r = false then RR c else 0) + RL c + Q l c) / 2 ≤ G c := by
      have hb := internal_right_child_second e v hv false active c leafCoin selected (q c) (hq c)
      simp only [and_true] at hb
      change (∑ t ∈ Finset.range T, p c t *
        (if r.active (active t) ∧ r.mid ≤ (active t : ℕ) ∧ c r = true then a
         else if r.active (active t) ∨ v.active (active t) then -(1 / 2) else 0)) ≤ G c at hb
      rw [visitMass_compare_right_switch active (p c) v hnode r rfl hr] at hb
      exact hb
    have hs := Finset.sum_le_sum (s := Finset.univ) fun c _ => hc c
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hsum_l] at hs
    change x₆ * a - (x₅ + x₄ + (x₁ + x₂ + x₃)) / 2 ≤ ∑ c, G c at hs
    have he : x₆ * a - (x₅ + x₄ + (x₁ + x₂ + x₃)) / 2 =
        x₆ / (2 * H) - (x₅ + x₄ + x₁ + x₂ + x₃) / 2 := by
      dsimp only [a]
      ring
    exact he ▸ hs
  have h₅ : (∑ c, ∑ t ∈ Finset.range T, p c t) / (4 * H) -
      (x₁ + x₂ + x₃ + x₄ + x₅ + x₆) / 2 ≤ ∑ c, G c := by
    have hc (c : TreeNode h → Bool) : (∑ t ∈ Finset.range T, p c t) / (4 * H) -
        (Q l c + Q r c) / 2 ≤ G c := by
      rw [← h_split v hnode c]
      exact internal_root_support_gain e v hnode false active c leafCoin selected (q c) (hq c)
    have hs := Finset.sum_le_sum (s := Finset.univ) fun c _ => hc c
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, Finset.sum_add_distrib,
      hsum_l, hsum_r] at hs
    have he : x₁ + x₂ + x₃ + (x₄ + x₅ + x₆) = x₁ + x₂ + x₃ + x₄ + x₅ + x₆ := by ring
    rwa [he] at hs
  have hx₁ : 0 ≤ x₁ := Finset.sum_nonneg fun c _ => hn _ c
  have hx₂ : 0 ≤ x₂ := Finset.sum_nonneg fun c _ => by split; exact hn _ c; exact le_rfl
  have hx₃ : 0 ≤ x₃ := Finset.sum_nonneg fun c _ => by split; exact hn _ c; exact le_rfl
  have hx₄ : 0 ≤ x₄ := Finset.sum_nonneg fun c _ => hn _ c
  have hx₅ : 0 ≤ x₅ := Finset.sum_nonneg fun c _ => by split; exact hn _ c; exact le_rfl
  exact internal_left_gain_of_comparisons hH (Finset.sum_nonneg fun c _ => hg c)
    hx₁ hx₂ hx₃ hx₄ hx₅ h₁ h₂ h₃ h₄ h₅

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.internal_left_coin_sum_policy := @CalibeatBandit.internal_left_coin_sum_policy
