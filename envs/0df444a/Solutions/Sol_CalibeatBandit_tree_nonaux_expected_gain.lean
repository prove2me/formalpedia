-- Prove2me | solution 1 for CalibeatBandit.tree_nonaux_expected_gain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T18:47:38.80097+00:00
-- url     : https://prove2.me/submissions/dcde9af6-2d5c-4e50-a6c6-cbc2046f24c2

import Mathlib
import Definitions.Def_CalibeatBandit_lower_bound_models
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_hard_tree_environment
import Definitions.Def_CalibeatBandit_hard_tree_analysis
import Theorems.Thm_CalibeatBandit_deepest_left_coin_sum_policy
import Theorems.Thm_CalibeatBandit_internal_left_coin_sum_policy
import Theorems.Thm_CalibeatBandit_internal_right_coin_sum_policy
import Theorems.Thm_CalibeatBandit_leaf_coin_sum_policy

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

theorem unnamed_bestSwapGain {K T : ℕ} (q u : ℕ → Fin K → ℝ)
    (i rootA rootB : Fin K) (H : ℝ)
    (hi : ∀ t < T, u t i = 0)
    (hroot : ∀ t < T, u t rootA + u t rootB = 1 / (2 * H)) :
    (∑ t ∈ Finset.range T, q t i) / (4 * H) ≤ bestSwapGain T q u i := by
  have hzero : (∑ t ∈ Finset.range T, q t i * u t i) = 0 :=
    Finset.sum_eq_zero fun t ht => by rw [hi t (Finset.mem_range.mp ht), mul_zero]
  simpa only [hzero, sub_zero] using root_bestSwapGain q u i rootA rootB H hroot

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

theorem treeBonusProb_leaf_pair {h M U : ℕ} (leaf : Fin (2 ^ h))
    (v : TreeNode h) (hd : (v.1 : ℕ) = h) (ha : v.active leaf)
    (coin : TreeNode h → Bool) (leafCoin : Bool) (selected : Fin M) :
    treeBonusProb (U := U) leaf coin leafCoin selected (.inl (v, false)) +
      treeBonusProb (U := U) leaf coin leafCoin selected (.inl (v, true)) = 1 := by
  cases leafCoin <;> simp [treeBonusProb, ha, hd]

/-- The child comparison for a right-action at a deepest internal node
(Case 4 in Appendix D.1). It holds for every realization of the coins. -/
theorem deepest_right_gain {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 = h)
    (active : ℕ → Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : ℕ → Fin N → ℝ)
    (hq : ∀ t < T, ∀ i, 0 ≤ q t i) :
    let i := e.symm (.inl (v, true))
    let w := v.child (by omega) true
    let u (t : ℕ) (j : Fin N) := treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    (∑ t ∈ Finset.range T, if w.active (active t) then q t i else 0) / (2 * treeHeight h)
      ≤ bestSwapGain T q u i := by
  intro i w u
  let a := e.symm (.inl (w, false))
  let b := e.symm (.inl (w, true))
  have hd : (v.1 : ℕ) < h := by omega
  have hw : (w.1 : ℕ) = h := hv
  have hH : 0 < treeHeight h := by unfold treeHeight; positivity
  have hed (t : ℕ) : w.active (active t) ↔ v.active (active t) ∧ v.mid ≤ (active t : ℕ) := by
    exact (v.child_active_iff hd (active t)).2
  have hdepth : (((v.1 : ℕ) : ℝ) + 1) = h := by exact_mod_cast hv
  have hEq : 1 - 2 * ((((v.1 : ℕ) : ℝ) + 1) / (2 * treeHeight h)) = 1 / treeHeight h := by
    rw [hdepth]
    field_simp
    simp [treeHeight]
  have hpoint (t : ℕ) (ht : t < T) :
      (if w.active (active t) then q t i / treeHeight h else 0) ≤
        q t i * (u t a - u t i) + q t i * (u t b - u t i) := by
    by_cases ha : w.active (active t)
    · have hp := (hed t).mp ha
      have hb : u t a + u t b = 1 := by
        simpa [u, a, b] using treeBonusProb_leaf_pair (U := U) (active t) w hw ha coin
          (leafCoin t) (selected (active t))
      have hi : u t i ≤ (((v.1 : ℕ) : ℝ) + 1) / (2 * treeHeight h) := by
        simp only [u, i, Equiv.apply_symm_apply, treeBonusProb, hp.1, if_true, hd.ne, if_false,
          not_lt_of_ge hp.2]
        split
        · exact le_rfl
        · positivity
      rw [if_pos ha]
      have hdiff : 1 / treeHeight h ≤ u t a + u t b - 2 * u t i := by
        rw [hb, ← hEq]
        linarith only [hi]
      have hm := mul_le_mul_of_nonneg_left hdiff (hq t ht i)
      rw [div_eq_mul_inv]
      norm_num [div_eq_mul_inv] at hm
      nlinarith only [hm]
    · rw [if_neg ha]
      have hcase : ¬ v.active (active t) ∨ (active t : ℕ) < v.mid := by
        rw [hed t] at ha
        by_cases hh : v.active (active t)
        · exact Or.inr (lt_of_not_ge fun hk => ha ⟨hh, hk⟩)
        · exact Or.inl hh
      have hi : u t i = 0 := by
        unfold u i
        simp only [Equiv.apply_symm_apply, treeBonusProb, hd.ne, if_false]
        rcases hcase with ho | hp
        · simp [ho]
        · simp [hp]
      have hab : u t a = 0 ∧ u t b = 0 := by simp [u, a, b, treeBonusProb, ha]
      simp [hi, hab.1, hab.2]
  have hs := Finset.sum_le_sum (s := Finset.range T) fun t ht => hpoint t (Finset.mem_range.mp ht)
  rw [Finset.sum_add_distrib] at hs
  change _ ≤ swapGain T q u i a + swapGain T q u i b at hs
  have he : (∑ t ∈ Finset.range T, if w.active (active t) then q t i / treeHeight h else 0) =
      (∑ t ∈ Finset.range T, if w.active (active t) then q t i else 0) / treeHeight h := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun t _ => by split <;> simp
  rw [he] at hs
  rw [show (2 * treeHeight h) = treeHeight h * 2 by ring, ← div_div]
  linarith only [hs, swapGain_le_best (T := T) q u i a, swapGain_le_best (T := T) q u i b]

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

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

/-- Case 4 only compares against the right child and the root. -/
theorem internal_two_comparisons {H gain total right : ℝ}
    (hH : 1 ≤ H) (hg : 0 ≤ gain)
    (h₁ : 2 * H * right ≤ 4 * H ^ 2 * gain)
    (h₂ : total - 2 * H * right ≤ 4 * H * gain) :
    total / (184 * H ^ 5) ≤ gain := by
  have hpos : 0 < H := by linarith
  have hsum : total ≤ (4 * H ^ 2 + 4 * H) * gain := by linear_combination h₁ + h₂
  have hcoeff : 4 * H ^ 2 + 4 * H ≤ 184 * H ^ 5 := by
    have p (n : ℕ) (hn : n ≤ 5) : H ^ n ≤ H ^ 5 := pow_le_pow_right₀ hH hn
    nlinarith only [p 2 (by omega), p 1 (by omega),
      show H ^ 1 = H by ring, show 0 ≤ H ^ 5 by positivity]
  exact (div_le_iff₀ (by positivity)).mpr (by
    rw [mul_comm gain]
    exact hsum.trans (mul_le_mul_of_nonneg_right hcoeff hg))

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open Set

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

/-- Case 4 of Appendix D.1, with both the right-child and root comparisons. -/
theorem deepest_right_bestSwapGain {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 = h)
    (active : ℕ → Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : ℕ → Fin N → ℝ)
    (hq : ∀ t < T, ∀ i, 0 ≤ q t i) :
    let i := e.symm (.inl (v, true))
    let u (t : ℕ) (j : Fin N) := treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    (∑ t ∈ Finset.range T, q t i) / (184 * treeHeight h ^ 5) ≤ bestSwapGain T q u i := by
  intro i u
  let H := treeHeight h
  let Q := ∑ t ∈ Finset.range T, q t i
  let R := ∑ t ∈ Finset.range T, if (v.child (by omega) true).active (active t) then q t i else 0
  let G := bestSwapGain T q u i
  have hH : 1 ≤ H := by dsimp [H, treeHeight]; linarith [Nat.cast_nonneg (α := ℝ) h]
  have hH' : 0 < H := zero_lt_one.trans_le hH
  have hchild : R / (2 * H) ≤ G := deepest_right_gain e v hv active coin leafCoin selected q hq
  have hroot : Q / (4 * H) - R / 2 ≤ G := by
    simpa only [Bool.true_eq, if_true] using
      internal_root_support_gain e v (by omega) true active coin leafCoin selected q hq
  have h1 : 2 * H * R ≤ 4 * H ^ 2 * G := by
    have hm := (div_le_iff₀ (show 0 < 2 * H by positivity)).mp hchild
    nlinarith only [mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * H by positivity)]
  have h2 : Q - 2 * H * R ≤ 4 * H * G := by
    have h := mul_le_mul_of_nonneg_right hroot (show 0 ≤ 4 * H by positivity)
    have he : (Q / (4 * H) - R / 2) * (4 * H) = Q - 2 * H * R := by
      field_simp
      ring
    rw [he] at h
    simpa only [mul_comm G] using h
  exact internal_two_comparisons hH (bestSwapGain_nonneg q u i) h1 h2

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

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open Set

/-- For each nonauxiliary action the coin average accounts for its share of
the time horizon. This holds for a fixed reward tape and auxiliary table. -/
theorem tree_nonaux_coin_sum {h M U N T : ℕ} (hh : 0 < h)
    (e : Fin N ≃ TreeAction h M U)
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (ha : Monotone active) (η : ℝ)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1)
    (i : Fin N) (hi : ∀ j, treeAuxAction e j ≠ i) :
    let leafCoin (b : Fin T → Bool) (t : ℕ) := if ht : t < T then b ⟨t, ht⟩ else false
    let q (b : Fin T → Bool) (c : TreeNode h → Bool) :=
      treePlayProbability e pick active η c (leafCoin b) selected z draw
    let u (b : Fin T → Bool) (c : TreeNode h → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) c (leafCoin b t) (selected (active t)) (e j)
    (∑ b, ∑ c, ∑ t ∈ Finset.range T, q b c t i) / (184 * treeHeight h ^ 5) ≤
      ∑ b, ∑ c, bestSwapGain T (q b c) (u b c) i := by
  classical
  intro leafCoin q u
  let H := treeHeight h
  have hH : 1 ≤ H := by dsimp [H, treeHeight]; linarith only [Nat.cast_nonneg (α := ℝ) h]
  have hH' : 0 < H := zero_lt_one.trans_le hH
  have hhpow : H ≤ H ^ 5 := by simpa only [pow_one] using pow_le_pow_right₀ hH (show 1 ≤ 5 by decide)
  have hq (b : Fin T → Bool) (c : TreeNode h → Bool) (t : ℕ) (j : Fin N) : 0 ≤ q b c t j :=
    (treePlayProbability_isProbVec e pick active η c (leafCoin b) selected z draw t).1 j
  have he : i = e.symm (e i) := (e.symm_apply_apply i).symm
  rcases hcase : e i with ⟨v, side⟩ | (j | j)
  · rw [hcase] at he
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ v.1.isLt) with hv | hv
    · rw [Finset.sum_comm (f := fun b c => ∑ t ∈ Finset.range T, q b c t i),
        Finset.sum_comm (f := fun b c => bestSwapGain T (q b c) (u b c) i), Finset.sum_div]
      refine Finset.sum_le_sum fun c _ => ?_
      have hleaf := leaf_coin_sum_policy (T := T) hh e v hv side pick active η c selected z draw
      rw [he]
      refine le_trans ?_ hleaf
      exact div_le_div_of_nonneg_left
        (Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun t _ => hq b c t _)
        (by positivity : 0 < 8 * H) (by linarith)
    · rw [Finset.sum_div]
      refine Finset.sum_le_sum fun b _ => ?_
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt hv) with hv' | hv'
      · cases side
        · rw [he]
          exact internal_left_coin_sum_policy (T := T) e v hv' pick active ha η (leafCoin b) selected z draw
        · rw [he]
          exact internal_right_coin_sum_policy (T := T) e v hv' pick active ha η (leafCoin b) selected z draw
      · cases side
        · rw [he]
          exact deepest_left_coin_sum_policy (T := T) e v hv' pick active ha η (leafCoin b) selected z draw
        · rw [Finset.sum_div]
          refine Finset.sum_le_sum fun c _ => ?_
          rw [he]
          exact deepest_right_bestSwapGain e v hv' active c (leafCoin b) selected (q b c)
            (fun t _ j' => hq b c t j')
  · exact (hi j (by rw [he, hcase]; rfl)).elim
  · rw [hcase] at he
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun c _ => ?_
    let rootA := e.symm (.inl (TreeNode.root h, false))
    let rootB := e.symm (.inl (TreeNode.root h, true))
    have hroot (t : ℕ) (_ : t < T) : u b c t rootA + u b c t rootB = 1 / (2 * H) := by
      simp only [u, rootA, rootB, Equiv.apply_symm_apply]
      exact treeBonusProb_root_pair hh (active t) c (leafCoin b t) (selected (active t))
    have hzero (t : ℕ) (_ : t < T) : u b c t i = 0 := by simp [u, hcase, treeBonusProb]
    refine le_trans ?_ (unnamed_bestSwapGain (q b c) (u b c) i rootA rootB H hzero hroot)
    exact div_le_div_of_nonneg_left (Finset.sum_nonneg fun t _ => hq b c t i)
      (by positivity : 0 < 4 * H) (by linarith)

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set
open scoped ENNReal

theorem integral_finiteTableLaw {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (f : A → ℝ) :
    (∫ a, f a ∂finiteTableLaw A) = (∑ a, f a) / Fintype.card A := by
  rw [finiteTableLaw, integral_smul_measure, integral_count, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, div_eq_inv_mul]

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

private theorem feedbackHistory_map_actions {A B : Type*} (f : A → B)
    (pick : (t : ℕ) → FeedbackHistory t → A) (y : ℕ → B → ℝ) (t : ℕ) :
    feedbackHistory (fun s x => f (pick s x)) y t =
      feedbackHistory pick (fun s a => y s (f a)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [feedbackHistory, ih]
    rfl

/-- Relate the measurable tape model to the action probabilities used in
the deterministic tree comparison lemmas. -/
theorem treeEnvironmentPlay_eq_treePlayProbability {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (anchor : Fin N) (env : TreeEnvironment h M N T) (t : ℕ) (ht : t < T) (i : Fin N) :
    treeEnvironmentPlay e active η pick anchor env t i =
      treePlayProbability e (fun s p => e (pick s p)) active η env.1.2.1
        (tableLeafCoin env.1.1) env.1.2.2
        (fun s => supportedBase (tapeDraw env.2 s).1)
        (fun s a => supportedThreshold ((tapeDraw env.2 s).2 (e.symm a))) t i := by
  classical
  unfold treeEnvironmentPlay treeEnvironmentAction treePlayProbability
  simp only [dif_pos ht, Pi.single_apply]
  have hy (s : ℕ) (a : TreeAction h M U) :
      treeReward η (active s) env.1.2.1 (tableLeafCoin env.1.1 s)
          (env.1.2.2 (active s)) (supportedBase (tapeDraw env.2 s).1)
          (fun a' => supportedThreshold ((tapeDraw env.2 s).2 (e.symm a'))) a =
        treeEnvironmentReward e active η env s (e.symm a) := by
    simp only [treeEnvironmentReward, boundedRoundReward, tableBonuses, scheduledBonuses,
      Equiv.apply_symm_apply, treeReward]
  have hy' : (fun s a => treeReward η (active s) env.1.2.1 (tableLeafCoin env.1.1 s)
      (env.1.2.2 (active s)) (supportedBase (tapeDraw env.2 s).1)
      (fun a' => supportedThreshold ((tapeDraw env.2 s).2 (e.symm a'))) a) =
      (fun s a => treeEnvironmentReward e active η env s (e.symm a)) := funext fun s => funext (hy s)
  rw [hy', feedbackHistory_map_actions]
  simp only [Equiv.symm_apply_apply]
  rw [rawTapeHistory_eq_feedbackHistory η (tableBonuses e active env.1) pick env.2 t ht.le]
  have hiff : (i = pick t (feedbackHistory pick (treeEnvironmentReward e active η env) t)) ↔
      e (pick t (feedbackHistory pick (treeEnvironmentReward e active η env) t)) = e i := by
    rw [Equiv.apply_eq_iff_eq]
    exact eq_comm
  let a := pick t (feedbackHistory pick (treeEnvironmentReward e active η env) t)
  change (if i = a then (1 : ℝ) else 0) = if e a = e i then 1 else 0
  by_cases hi : i = a
  · rw [if_pos hi, if_pos (hiff.mp hi)]
  · rw [if_neg hi, if_neg (fun he => hi (hiff.mpr he))]

theorem integrable_treeEnvironmentBestGain {h M U N T : ℕ} [Nonempty (Fin M)]
    (e : Fin N ≃ TreeAction h M U) (active : ℕ → Fin (2 ^ h)) (η : ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (anchor i : Fin N) :
    Integrable (fun env : TreeEnvironment h M N T =>
      bestSwapGain T (treeEnvironmentPlay e active η pick anchor env) (tableBonuses e active env.1) i)
      (treeEnvironmentLaw h M N T) := by
  classical
  let q := treeEnvironmentPlay (T := T) e active η pick anchor
  let u (env : TreeEnvironment h M N T) := tableBonuses e active env.1
  have hu (env : TreeEnvironment h M N T) (t : ℕ) (j : Fin N) : u env t j ∈ Icc 0 1 :=
    treeBonusProb_mem _ _ _ _ _
  have hqm (t : ℕ) (k : Fin N) : Measurable (fun env => q env t k) :=
    measurable_treeEnvironmentPlay e active η pick hm anchor t k
  have hum (t : ℕ) (j : Fin N) : Measurable (fun env => u env t j) := by
    apply measurable_with_fixed_table
    intro table
    change Measurable (fun _ : RewardTape N T => tableBonuses e active table t j)
    exact measurable_const
  let _ : Nonempty (Fin N) := ⟨anchor⟩
  unfold bestSwapGain
  apply integrable_finset_max (B := (T : ℝ))
  · intro j
    exact Finset.measurable_sum _ fun t _ => (hqm t i).mul ((hum t j).sub (hum t i))
  · intro j env
    unfold swapGain
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _ ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum fun t _ => by
        have hd : |u env t j - u env t i| ≤ 1 := abs_le.mpr
          ⟨by linarith only [(hu env t j).1, (hu env t i).2],
            by linarith only [(hu env t j).2, (hu env t i).1]⟩
        have hq : |q env t i| ≤ 1 := by
          unfold q treeEnvironmentPlay
          rw [Pi.single_apply]
          split <;> norm_num
        rw [abs_mul]
        exact mul_le_one₀ hq (abs_nonneg _) hd
      _ = _ := by simp

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

private theorem sum_treeTableSum_selected_first {h M T : ℕ} (f : TreeTables h M T → ℝ) :
    (∑ table, f table) = ∑ J : Fin (2 ^ h) → Fin M, ∑ b : Fin T → Bool,
      ∑ c : TreeNode h → Bool, f (b, c, J) := by
  rw [treeTableSum]
  calc
    _ = ∑ b : Fin T → Bool, ∑ J : Fin (2 ^ h) → Fin M, ∑ c : TreeNode h → Bool, f (b, c, J) :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

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

/-- Extend the fixed-tape coin bound to the full distribution. -/
theorem tree_nonaux_expected_gain {h M U N T : ℕ} [Nonempty (Fin M)] (hh : 0 < h)
    (e : Fin N ≃ TreeAction h M U) (active : ℕ → Fin (2 ^ h)) (ha : Monotone active) (η : ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (anchor i : Fin N) (hi : ∀ j, treeAuxAction e j ≠ i) :
    let P := treeEnvironmentLaw h M N T
    let q := treeEnvironmentPlay (T := T) e active η pick anchor
    let u (env : TreeEnvironment h M N T) := tableBonuses e active env.1
    (∫ env, ∑ t ∈ Finset.range T, q env t i ∂P) / (184 * treeHeight h ^ 5) ≤
      ∫ env, bestSwapGain T (q env) (u env) i ∂P := by
  classical
  intro P q u
  let C := TreeTables h M T
  let μ := finiteTableLaw C
  let ν := rewardTapeLaw N T
  let Q (env : C × RewardTape N T) := ∑ t ∈ Finset.range T, q env t i
  let G (env : C × RewardTape N T) := bestSwapGain T (q env) (u env) i
  have hQ : Integrable Q (μ.prod ν) := integrable_treePlayMass e active η pick hm anchor (fun _ _ => i)
  have hG : Integrable G (μ.prod ν) := integrable_treeEnvironmentBestGain e active η pick hm anchor i
  let D := 184 * treeHeight h ^ 5
  have hfixed (tape : RewardTape N T) : (∫ table, Q (table, tape) ∂μ) / D ≤
      ∫ table, G (table, tape) ∂μ := by
    rw [integral_finiteTableLaw, integral_finiteTableLaw]
    rw [show ((∑ table : C, Q (table, tape)) / Fintype.card C) / D =
        ((∑ table : C, Q (table, tape)) / D) / Fintype.card C from by ring]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [sum_treeTableSum_selected_first, sum_treeTableSum_selected_first, Finset.sum_div]
    refine Finset.sum_le_sum fun J _ => ?_
    let z (s : ℕ) := supportedBase (tapeDraw tape s).1
    let draw (s : ℕ) (a : TreeAction h M U) := supportedThreshold ((tapeDraw tape s).2 (e.symm a))
    let q' (b : Fin T → Bool) (c : TreeNode h → Bool) :=
      treePlayProbability e (fun s p => e (pick s p)) active η c (tableLeafCoin b) J z draw
    have hq (b : Fin T → Bool) (c : TreeNode h → Bool) (t : ℕ) (ht : t ∈ Finset.range T) (j : Fin N) :
        q ((b, c, J), tape) t j = q' b c t j :=
      treeEnvironmentPlay_eq_treePlayProbability e active η pick anchor ((b, c, J), tape) t
        (Finset.mem_range.mp ht) j
    have hmass (b : Fin T → Bool) (c : TreeNode h → Bool) :
        Q ((b, c, J), tape) = ∑ t ∈ Finset.range T, q' b c t i :=
      Finset.sum_congr rfl (fun t ht => hq b c t ht i)
    have hgain (b : Fin T → Bool) (c : TreeNode h → Bool) :
        G ((b, c, J), tape) = bestSwapGain T (q' b c) (u ((b, c, J), tape)) i := by
      unfold G bestSwapGain
      congr 1
      funext j
      unfold swapGain
      exact Finset.sum_congr rfl fun t ht => by rw [hq b c t ht i]
    simp only [hmass, hgain]
    exact tree_nonaux_coin_sum (T := T) hh e (fun s p => e (pick s p)) active ha η J z draw i hi
  change (∫ env, Q env ∂μ.prod ν) / D ≤ ∫ env, G env ∂μ.prod ν
  rw [integral_prod_symm Q hQ, integral_prod_symm G hG, ← integral_div]
  exact integral_mono (hQ.swap.integral_prod_left.div_const _) hG.swap.integral_prod_left hfixed

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.tree_nonaux_expected_gain := @CalibeatBandit.tree_nonaux_expected_gain
