-- Prove2me | solution 1 for CalibeatBandit.tree_expected_proxy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T18:47:39.453243+00:00
-- url     : https://prove2.me/submissions/efc34975-f009-43b2-b4bb-c25197b5ecae

import Mathlib
import Definitions.Def_CalibeatBandit_lower_bound_models
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_hard_tree_environment
import Definitions.Def_CalibeatBandit_hard_tree_analysis
import Theorems.Thm_CalibeatBandit_tree_expected_selected_hits
import Theorems.Thm_CalibeatBandit_tree_nonaux_expected_gain

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

/-- The case split of Lemma 4.9 after taking expectations. The two groups
partition the learner's play mass, and their swap gains are nonnegative. -/
theorem aggregate_swap_gain {T auxMass auxGain otherGain H : ℝ}
    (hT : 0 ≤ T) (hH : 1 ≤ H)
    (haux₀ : 0 ≤ auxGain) (hother₀ : 0 ≤ otherGain)
    (haux : auxMass / (4 * H) - T / (64 * H) ≤ auxGain)
    (hother : (T - auxMass) / (184 * H ^ 5) ≤ otherGain) :
    T / (368 * H ^ 5) ≤ auxGain + otherGain := by
  have hH₀ : 0 < H := by linarith
  have hpos : 0 < 184 * H ^ 5 := by positivity
  by_cases h : auxMass ≤ T / 2
  · calc
      _ = (T / 2) / (184 * H ^ 5) := by ring
      _ ≤ (T - auxMass) / (184 * H ^ 5) :=
        div_le_div_of_nonneg_right (by linarith) hpos.le
      _ ≤ otherGain := hother
      _ ≤ _ := le_add_of_nonneg_left haux₀
  · have hh : H ≤ H ^ 5 := by
      calc
        H = H * 1 := (mul_one _).symm
        _ ≤ H * H ^ 4 := mul_le_mul_of_nonneg_left (one_le_pow₀ hH) hH₀.le
        _ = _ := by ring
    have hbig : 64 * H ≤ 368 * H ^ 5 := by linarith
    have hm : T / (368 * H ^ 5) ≤ T / (64 * H) :=
      div_le_div_of_nonneg_left hT (by positivity) hbig
    have haux' : T / (8 * H) ≤ auxMass / (4 * H) := by
      rw [show T / (8 * H) = (T / 2) / (4 * H) by ring]
      exact div_le_div_of_nonneg_right (le_of_not_ge h) (by positivity)
    have heq : T / (8 * H) = 8 * (T / (64 * H)) := by ring
    have hn : 0 ≤ T / (64 * H) := by positivity
    linarith only [hm, haux', heq, hn, haux, hother₀]

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

open Set

/-- Comparing all auxiliary actions with the root pair leaves just the
count of plays of the selected auxiliary action as the loss term. -/
theorem tree_auxiliary_gain {h M U N T : ℕ} (hh : 0 < h) (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (c : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (q : ℕ → Fin N → ℝ) :
    let u (t : ℕ) (i : Fin N) := treeBonusProb (active t) c (leafCoin t) (selected (active t)) (e i)
    let aux := treeAuxAction e
    ((∑ j : Fin M, ∑ t ∈ Finset.range T, q t (aux j)) / (4 * treeHeight h) -
        ∑ t ∈ Finset.range T, q t (aux (selected (active t)))) ≤
      ∑ j : Fin M, bestSwapGain T q u (aux j) := by
  classical
  intro u aux
  let rootA := e.symm (.inl (TreeNode.root h, false))
  let rootB := e.symm (.inl (TreeNode.root h, true))
  have hroot (t : ℕ) (_ : t < T) : u t rootA + u t rootB = 1 / (2 * treeHeight h) := by
    simp only [u, rootA, rootB, Equiv.apply_symm_apply]
    exact treeBonusProb_root_pair hh (active t) c (leafCoin t) (selected (active t))
  have hc (j : Fin M) := root_bestSwapGain q u (aux j) rootA rootB (treeHeight h) hroot
  have hs := Finset.sum_le_sum (s := Finset.univ) fun j _ => hc j
  rw [Finset.sum_sub_distrib, ← Finset.sum_div] at hs
  have he : (∑ j : Fin M, ∑ t ∈ Finset.range T, q t (aux j) * u t (aux j)) =
      ∑ t ∈ Finset.range T, q t (aux (selected (active t))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hu (j : Fin M) : u t (aux j) = if j = selected (active t) then 1 else 0 := by
      change treeBonusProb (U := U) (active t) c (leafCoin t) (selected (active t))
        (e (e.symm (.inr (.inl j)))) = _
      rw [Equiv.apply_symm_apply]
      rfl
    simp only [hu, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rwa [he] at hs

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set
open scoped ENNReal

theorem monotone_blockLeaf (h r : ℕ) : Monotone (blockLeaf h r) := by
  intro s t hst
  exact min_le_min_right _ (Nat.div_le_div_right hst)

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

theorem treeEnvironmentPlay_probVec {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (anchor : Fin N) (env : TreeEnvironment h M N T) (t : ℕ) :
    IsProbVec (treeEnvironmentPlay e active η pick anchor env t) := by
  unfold treeEnvironmentPlay
  constructor
  · intro i
    rw [Pi.single_apply]
    split <;> norm_num
  · simp

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

set_option maxHeartbeats 750000 in
/-- The whole-tree predicted gain. The two groups of source actions
partition all play mass. -/
theorem tree_expected_proxy {h M U N r : ℕ} [Nonempty (Fin M)] (hh : 0 < h)
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (hη : 0 ≤ η) (hη₁ : η < 1)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t)) (anchor : Fin N)
    (hbudget : ((2 ^ h : ℕ) : ℝ) * ((r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))) ≤
      ((2 ^ h * r : ℕ) : ℝ) / (64 * treeHeight h)) :
    let T := 2 ^ h * r
    let active := blockLeaf h r
    let P := treeEnvironmentLaw h M N T
    let q := treeEnvironmentPlay (T := T) e active η pick anchor
    (T : ℝ) / (368 * treeHeight h ^ 5) ≤
      ∫ env, pseudoSwapRegret T (q env) (tableBonuses e active env.1) ∂P := by
  classical
  intro T active P q
  let H := treeHeight h
  let aux := treeAuxAction e
  let A := Finset.univ.map aux
  let u (env : TreeEnvironment h M N T) := tableBonuses e active env.1
  let Q (i : Fin N) (env : TreeEnvironment h M N T) := ∑ t ∈ Finset.range T, q env t i
  let G (i : Fin N) (env : TreeEnvironment h M N T) := bestSwapGain T (q env) (u env) i
  let W (env : TreeEnvironment h M N T) :=
    ∑ t ∈ Finset.range T, q env t (aux (env.1.2.2 (active t)))
  let meanQ (i : Fin N) := ∫ env, Q i env ∂P
  let meanG (i : Fin N) := ∫ env, G i env ∂P
  have hQ (i : Fin N) : Integrable (Q i) P :=
    integrable_treePlayMass e active η pick hm anchor (fun _ _ => i)
  have hG (i : Fin N) : Integrable (G i) P :=
    integrable_treeEnvironmentBestGain e active η pick hm anchor i
  have hW : Integrable W P :=
    integrable_treePlayMass e active η pick hm anchor (fun tb t => aux (tb.2.2 (active t)))
  have htotalQ : (∑ i, meanQ i) = T := by
    dsimp only [meanQ]
    rw [← integral_finsetSum _ (fun i _ => hQ i)]
    have he (env : TreeEnvironment h M N T) : (∑ i, Q i env) = T := by
      unfold Q
      rw [Finset.sum_comm]
      calc
        _ = ∑ _ ∈ Finset.range T, (1 : ℝ) :=
          Finset.sum_congr rfl fun t _ => (treeEnvironmentPlay_probVec e active η pick anchor env t).2
        _ = _ := by simp
    simp only [he, integral_const, probReal_univ, one_smul]
  have hG₀ (i : Fin N) : 0 ≤ meanG i := integral_nonneg fun env =>
    bestSwapGain_nonneg (q env) (u env) i
  have hsub (i : Fin N) (hi : i ∈ Aᶜ) : meanQ i / (184 * H ^ 5) ≤ meanG i := by
    refine tree_nonaux_expected_gain hh e active (monotone_blockLeaf h r) η pick hm anchor i ?_
    intro j hej
    exact (Finset.mem_compl.mp hi) (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, hej⟩)
  have hother : ((T : ℝ) - ∑ i ∈ A, meanQ i) / (184 * H ^ 5) ≤ ∑ i ∈ Aᶜ, meanG i := by
    have hs := Finset.sum_le_sum (s := Aᶜ) (fun i hi => hsub i hi)
    rw [← Finset.sum_div] at hs
    have hsplit := A.sum_add_sum_compl meanQ
    rw [htotalQ] at hsplit
    have he : (∑ i ∈ Aᶜ, meanQ i) = (T : ℝ) - ∑ i ∈ A, meanQ i := by linarith only [hsplit]
    rwa [he] at hs
  have haux : (∑ i ∈ A, meanQ i) / (4 * H) - (T : ℝ) / (64 * H) ≤ ∑ i ∈ A, meanG i := by
    have hpoint (env : TreeEnvironment h M N T) :
        (∑ i ∈ A, Q i env) / (4 * H) - W env ≤ ∑ i ∈ A, G i env := by
      unfold A
      simp only [Finset.sum_map]
      exact tree_auxiliary_gain hh e active env.1.2.1 (tableLeafCoin env.1.1) env.1.2.2 (q env)
    have hi₁ : Integrable (fun env => (∑ i ∈ A, Q i env) / (4 * H)) P :=
      (integrable_finsetSum _ fun i _ => hQ i).div_const _
    have hi₂ : Integrable (fun env => ∑ i ∈ A, G i env) P :=
      integrable_finsetSum _ fun i _ => hG i
    have hs := integral_mono (hi₁.sub hW) hi₂ hpoint
    change (∫ env, (∑ i ∈ A, Q i env) / (4 * H) - W env ∂P) ≤ ∫ env, ∑ i ∈ A, G i env ∂P at hs
    rw [integral_sub hi₁ hW, integral_div, integral_finsetSum _ (fun i _ => hQ i),
      integral_finsetSum _ (fun i _ => hG i)] at hs
    have hw : (∫ env, W env ∂P) ≤ (T : ℝ) / (64 * H) :=
      (tree_expected_selected_hits (r := r) e η hη hη₁ pick hm anchor).trans hbudget
    change (∑ i ∈ A, meanQ i) / (4 * H) - (∫ env, W env ∂P) ≤ ∑ i ∈ A, meanG i at hs
    linarith only [hs, hw]
  have hH : 1 ≤ H := by unfold H treeHeight; linarith only [Nat.cast_nonneg (α := ℝ) h]
  have h := aggregate_swap_gain (Nat.cast_nonneg T) hH
    (Finset.sum_nonneg fun i _ => hG₀ i) (Finset.sum_nonneg fun i _ => hG₀ i) haux hother
  rw [Finset.sum_add_sum_compl A] at h
  rw [← integral_finsetSum _ (fun i _ => hG i)] at h
  simpa only [pseudoSwapRegret_eq_sum_bestSwapGain, G, u] using h

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.tree_expected_proxy := @CalibeatBandit.tree_expected_proxy
