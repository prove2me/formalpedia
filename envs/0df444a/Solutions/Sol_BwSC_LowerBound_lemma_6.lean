-- Prove2me | solution 1 for BwSC.LowerBound.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T03:39:29.398312+00:00
-- url     : https://prove2.me/submissions/7ada039f-7ad3-4602-962b-8bcd972a900f

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound.L6Aux

lemma act_zero {K T : ℕ} (h : BanditHistory K T) : act h 0 = none := by
  simp [act, actA]

lemma act_gt {K T : ℕ} (h : BanditHistory K T) (t : ℕ) (ht : T < t) : act h t = none := by
  simp only [act, actA]; rw [dif_neg (by omega)]

/-- The arms chosen in the window `[lo, hi]`. -/
noncomputable def chosen {K T : ℕ} (h : BanditHistory K T) (lo hi : ℕ) : Finset (Fin K) := by
  classical
  exact Finset.univ.filter (fun k => ∃ t, lo ≤ t ∧ t ≤ hi ∧ act h t = some k)

lemma mem_chosen {K T : ℕ} (h : BanditHistory K T) (lo hi : ℕ) (k : Fin K) :
    k ∈ chosen h lo hi ↔ ∃ t, lo ≤ t ∧ t ≤ hi ∧ act h t = some k := by
  classical
  simp [chosen]

lemma switchCost_mono_right {K T : ℕ} (h : BanditHistory K T) (lo n n' : ℕ) (hn : n ≤ n') :
    switchCost h lo n ≤ switchCost h lo n' := by
  unfold switchCost
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, ht.2.1, by omega, ht.2.2.2⟩

/-- A window with `s` switches contains at most `s + 1` distinct arms. -/
lemma card_chosen_le {K T : ℕ} (h : BanditHistory K T) (lo : ℕ) :
    ∀ hi, (chosen h lo hi).card ≤ switchCost h lo hi + 1 := by
  intro hi
  induction hi with
  | zero =>
    have : chosen h lo 0 = ∅ := by
      ext k; rw [mem_chosen]; simp only [Finset.notMem_empty, iff_false, not_exists, not_and]
      intro t _ ht; have : t = 0 := by omega
      subst this; rw [act_zero]; simp
    rw [this]; simp
  | succ hi ih =>
    -- membership in the next window
    have hsub : chosen h lo (hi + 1) ⊆ chosen h lo hi ∪
        (Finset.univ.filter (fun k => lo ≤ hi + 1 ∧ act h (hi + 1) = some k)) := by
      intro k hk
      rw [mem_chosen] at hk
      obtain ⟨t, ht1, ht2, ht3⟩ := hk
      rcases Nat.lt_or_ge t (hi + 1) with hlt | hge
      · exact Finset.mem_union_left _ ((mem_chosen _ _ _ _).mpr ⟨t, ht1, by omega, ht3⟩)
      · have : t = hi + 1 := by omega
        subst this
        exact Finset.mem_union_right _ (by simp [ht1, ht3])
    have hcard1 : (Finset.univ.filter (fun k : Fin K => lo ≤ hi + 1 ∧ act h (hi + 1) = some k)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      rw [ha.2.2] at hb; exact Option.some_injective _ hb.2.2
    by_cases hB : lo ≤ hi ∧ 1 ≤ hi ∧ hi + 1 ≤ T
    · by_cases hsame : act h hi = act h (hi + 1)
      · -- no new arm
        have hsub' : chosen h lo (hi + 1) ⊆ chosen h lo hi := by
          intro k hk
          have := hsub hk
          rw [Finset.mem_union] at this
          rcases this with h1 | h1
          · exact h1
          · simp only [Finset.mem_filter] at h1
            exact (mem_chosen _ _ _ _).mpr ⟨hi, hB.1, le_rfl, by rw [hsame]; exact h1.2.2⟩
        calc (chosen h lo (hi + 1)).card ≤ (chosen h lo hi).card := Finset.card_le_card hsub'
          _ ≤ switchCost h lo hi + 1 := ih
          _ ≤ switchCost h lo (hi + 1) + 1 := by
              have := switchCost_mono_right h lo hi (hi + 1) (by omega); omega
      · -- a new switch at `(hi, hi+1)`
        have hsw : switchCost h lo hi + 1 ≤ switchCost h lo (hi + 1) := by
          unfold switchCost
          have hins : insert hi ((Finset.range (T + 1)).filter (fun t => lo ≤ t ∧ t + 1 ≤ hi ∧
              1 ≤ t ∧ t + 1 ≤ T ∧ act h t ≠ act h (t + 1))) ⊆
              (Finset.range (T + 1)).filter (fun t => lo ≤ t ∧ t + 1 ≤ hi + 1 ∧ 1 ≤ t ∧
                t + 1 ≤ T ∧ act h t ≠ act h (t + 1)) := by
            intro t ht
            rw [Finset.mem_insert] at ht
            rcases ht with rfl | ht
            · simp only [Finset.mem_filter, Finset.mem_range]
              exact ⟨by omega, hB.1, by omega, hB.2.1, hB.2.2, hsame⟩
            · simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
              exact ⟨ht.1, ht.2.1, by omega, ht.2.2.2⟩
          have hnot : hi ∉ (Finset.range (T + 1)).filter (fun t => lo ≤ t ∧ t + 1 ≤ hi ∧
              1 ≤ t ∧ t + 1 ≤ T ∧ act h t ≠ act h (t + 1)) := by
            simp only [Finset.mem_filter]; omega
          have := Finset.card_le_card hins
          rw [Finset.card_insert_of_notMem hnot] at this
          exact this
        calc (chosen h lo (hi + 1)).card
            ≤ (chosen h lo hi ∪ (Finset.univ.filter
                (fun k => lo ≤ hi + 1 ∧ act h (hi + 1) = some k))).card := Finset.card_le_card hsub
          _ ≤ (chosen h lo hi).card + 1 := (Finset.card_union_le _ _).trans (by omega)
          _ ≤ switchCost h lo (hi + 1) + 1 := by omega
    · have hB' : hi < lo ∨ hi = 0 ∨ T < hi + 1 := by
        by_contra hc; push_neg at hc; exact hB ⟨hc.1, by omega, hc.2.2⟩
      by_cases hT' : T < hi + 1
      · -- the new round does not exist
        have hsub' : chosen h lo (hi + 1) ⊆ chosen h lo hi := by
          intro k hk
          have := hsub hk
          rw [Finset.mem_union] at this
          rcases this with h1 | h1
          · exact h1
          · simp only [Finset.mem_filter] at h1
            rw [act_gt h (hi + 1) hT'] at h1; exact absurd h1.2.2 (by simp)
        calc (chosen h lo (hi + 1)).card ≤ (chosen h lo hi).card := Finset.card_le_card hsub'
          _ ≤ switchCost h lo hi + 1 := ih
          _ ≤ switchCost h lo (hi + 1) + 1 := by
              have := switchCost_mono_right h lo hi (hi + 1) (by omega); omega
      · -- the earlier part of the window is empty
        have hB'' : hi < lo ∨ hi = 0 := by omega
        have hempty : chosen h lo hi = ∅ := by
          ext k; rw [mem_chosen]; simp only [Finset.notMem_empty, iff_false, not_exists, not_and]
          intro t ht1 ht2 ht3
          have : t = 0 := by omega
          subst this; rw [act_zero] at ht3; exact absurd ht3 (by simp)
        have : (chosen h lo (hi + 1)).card ≤ 1 := by
          calc (chosen h lo (hi + 1)).card ≤ (chosen h lo hi ∪ (Finset.univ.filter
                  (fun k => lo ≤ hi + 1 ∧ act h (hi + 1) = some k))).card := Finset.card_le_card hsub
            _ ≤ (chosen h lo hi).card + 1 := (Finset.card_union_le _ _).trans (by omega)
            _ = 1 := by rw [hempty]; simp
        omega


/-- The switch set of a window. -/
def swSet {K T : ℕ} (h : BanditHistory K T) (lo hi : ℕ) : Finset ℕ :=
  (Finset.range (T + 1)).filter
    (fun t => lo ≤ t ∧ t + 1 ≤ hi ∧ 1 ≤ t ∧ t + 1 ≤ T ∧ act h t ≠ act h (t + 1))

lemma switchCost_eq_card {K T : ℕ} (h : BanditHistory K T) (lo hi : ℕ) :
    switchCost h lo hi = (swSet h lo hi).card := rfl

/-- Pigeonhole over windows with monotone end points. -/
lemma sum_window_switch_le {K T : ℕ} (h : BanditHistory K T) (M : ℕ) (t : ℕ → ℕ)
    (ht : ∀ i i', i ≤ i' → t i ≤ t i') :
    ∑ j ∈ Finset.Icc 1 M, switchCost h (t (j - 1)) (t j) ≤ switchCost h 1 T := by
  classical
  simp_rw [switchCost_eq_card]
  rw [← Finset.card_biUnion]
  · apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_biUnion, swSet, Finset.mem_filter] at hx ⊢
    obtain ⟨j, _, hx1, hx2⟩ := hx
    refine ⟨hx1, ?_, ?_, ?_, ?_, hx2.2.2.2.2⟩ <;> omega
  · intro j hj j' hj' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [swSet, Finset.mem_filter] at hx hx'
    simp only [Finset.coe_Icc, Set.mem_Icc] at hj hj'
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := ht j (j' - 1) (by omega); omega
    · have := ht j' (j - 1) (by omega); omega

open Classical in
/-- On a window, the number of arms not chosen is at least `K - 1 - (switches)`. -/
lemma notChosen_count {K T : ℕ} (h : BanditHistory K T) (lo hi : ℕ) :
    (K : ℝ) - 1 - (switchCost h lo hi : ℝ) ≤
      ((Finset.univ.filter (fun k : Fin K => notChosen h k lo hi)).card : ℝ) := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin K))) (p := fun k => notChosen h k lo hi)
  have heq : Finset.univ.filter (fun k : Fin K => ¬ notChosen h k lo hi) = chosen h lo hi := by
    ext k
    rw [mem_chosen]
    simp [notChosen]
  rw [heq, Finset.card_univ, Fintype.card_fin] at hsplit
  have hc := card_chosen_le h lo hi
  have : ((Finset.univ.filter (fun k : Fin K => notChosen h k lo hi)).card : ℝ) +
      ((chosen h lo hi).card : ℝ) = K := by exact_mod_cast hsplit
  have hc' : ((chosen h lo hi).card : ℝ) ≤ (switchCost h lo hi : ℝ) + 1 := by exact_mod_cast hc
  linarith



lemma switchCost_mono1 {K T : ℕ} (h : BanditHistory K T) (n n' : ℕ) (hn : n ≤ n') :
    switchCost h 1 n ≤ switchCost h 1 n' := by
  unfold switchCost
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, ht.2.1, by omega, ht.2.2.2⟩

/-- After the budget is exhausted at `τ`, no further switch happens (given total `≤ S`). -/
lemma no_switch_after {K T : ℕ} (S : ℕ) (h : BanditHistory K T)
    (hsw : switchCost h 1 T ≤ S) (hτ : 1 ≤ stopTime S h ∧ stopTime S h ≤ T) :
    ∀ t, stopTime S h ≤ t → t ≤ T → act h t = act h (stopTime S h) := by
  set τ := stopTime S h with hτdef
  have hne : ((Finset.Icc 1 T).filter (fun t => switchCost h 1 t = S)).Nonempty := by
    by_contra hne
    have : τ = T + 1 := by rw [hτdef]; unfold stopTime; rw [dif_neg hne]
    omega
  have hSτ : switchCost h 1 τ = S := by
    have hmem := Finset.min'_mem _ hne
    have : τ = ((Finset.Icc 1 T).filter (fun t => switchCost h 1 t = S)).min' hne := by
      rw [hτdef]; unfold stopTime; rw [dif_pos hne]
    rw [this]; exact (Finset.mem_filter.mp hmem).2
  have hstep : ∀ t, τ ≤ t → t + 1 ≤ T → act h t = act h (t + 1) := by
    intro t ht1 ht2
    by_contra hneq
    have hsub : insert t ((Finset.range (T + 1)).filter (fun s => 1 ≤ s ∧ s + 1 ≤ τ ∧ 1 ≤ s ∧
        s + 1 ≤ T ∧ act h s ≠ act h (s + 1))) ⊆ (Finset.range (T + 1)).filter (fun s =>
        1 ≤ s ∧ s + 1 ≤ T ∧ 1 ≤ s ∧ s + 1 ≤ T ∧ act h s ≠ act h (s + 1)) := by
      intro s hs
      rw [Finset.mem_insert] at hs
      rcases hs with rfl | hs
      · simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by omega, by omega, by omega, by omega, hneq⟩
      · simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢
        exact ⟨hs.1, hs.2.1, by omega, hs.2.2.2.1, hs.2.2.2.2⟩
    have hnot : t ∉ (Finset.range (T + 1)).filter (fun s => 1 ≤ s ∧ s + 1 ≤ τ ∧ 1 ≤ s ∧
        s + 1 ≤ T ∧ act h s ≠ act h (s + 1)) := by
      simp only [Finset.mem_filter]; omega
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot] at hc
    have e1 : switchCost h 1 τ = ((Finset.range (T + 1)).filter (fun s => 1 ≤ s ∧ s + 1 ≤ τ ∧
        1 ≤ s ∧ s + 1 ≤ T ∧ act h s ≠ act h (s + 1))).card := rfl
    have e2 : switchCost h 1 T = ((Finset.range (T + 1)).filter (fun s => 1 ≤ s ∧ s + 1 ≤ T ∧
        1 ≤ s ∧ s + 1 ≤ T ∧ act h s ≠ act h (s + 1))).card := rfl
    omega
  intro t ht1 ht2
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_or_ge t τ with hlt | hge
    · have : t + 1 = τ := by omega
      rw [this]
    · rw [← hstep t hge (by omega), ih hge (by omega)]

lemma act_stopTime_in {K T : ℕ} (S : ℕ) (h : BanditHistory K T) (k : Fin K)
    (hk : act h (stopTime S h) = some k) : 1 ≤ stopTime S h ∧ stopTime S h ≤ T := by
  by_contra hc
  have : act h (stopTime S h) = none := by simp [act, actA, hc]
  rw [this] at hk; exact absurd hk (by simp)

lemma Kr_bounds {S K : ℕ} (hK : 1 < K) :
    2 ≤ (K : ℝ) - (rIdx S K : ℝ) ∧ (K : ℝ) - (rIdx S K : ℝ) ≤ K + 1 := by
  have h1 : rIdx S K ≤ (K : ℤ) - 2 := by
    unfold rIdx qIdx
    by_cases hS : S = 0
    · subst hS; simp; omega
    · rw [if_neg hS]
      have hdm := Nat.div_add_mod (S - 1) (K - 1)
      have hlt := Nat.mod_lt (S - 1) (by omega : K - 1 > 0)
      have hS1 : ((S - 1 : ℕ) : ℤ) = (S : ℤ) - 1 := by omega
      have hK1 : ((K - 1 : ℕ) : ℤ) = (K : ℤ) - 1 := by omega
      have e : (S : ℤ) - 1 - (((S - 1) / (K - 1) : ℕ) : ℤ) * ((K : ℤ) - 1) =
          (((S - 1) % (K - 1) : ℕ) : ℤ) := by
        rw [← hS1, ← hK1]; push_cast; zify at hdm; linarith
      rw [e]
      zify at hlt; push_cast at hlt ⊢; omega
  have h2 : (-1 : ℤ) ≤ rIdx S K := by
    unfold rIdx qIdx
    by_cases hS : S = 0
    · subst hS; simp
    · rw [if_neg hS]
      have : ((S - 1) / (K - 1)) * (K - 1) ≤ S - 1 := Nat.div_mul_le_self _ _
      have hS1 : ((S - 1 : ℕ) : ℤ) = (S : ℤ) - 1 := by omega
      have hK1 : ((K - 1 : ℕ) : ℤ) = (K : ℤ) - 1 := by omega
      rw [← hK1]
      have h2 : ((((S - 1) / (K - 1)) * (K - 1) : ℕ) : ℤ) ≤ ((S - 1 : ℕ) : ℤ) := by
        exact_mod_cast this
      push_cast at h2
      omega
  have h1' : (rIdx S K : ℝ) ≤ (K : ℝ) - 2 := by exact_mod_cast h1
  have h2' : (-1 : ℝ) ≤ (rIdx S K : ℝ) := by exact_mod_cast h2
  constructor <;> linarith

lemma act_congr {K T : ℕ} {h h' : BanditHistory K T} (e : actions h = actions h') :
    act h = act h' := by
  funext t; simp [act, e]

lemma measurableSet_of_actions {K T : ℕ} (E : Set (BanditHistory K T))
    (hE : ∀ h h', actions h = actions h' → h ∈ E → h' ∈ E) : MeasurableSet E := by
  have : E = actions ⁻¹' (actions '' E) := by
    ext h; constructor
    · intro hh; exact ⟨h, hh, rfl⟩
    · rintro ⟨h', hh', e⟩; exact hE h' h e hh'
  rw [this]; exact measurable_actions (Set.toFinite _).measurableSet

lemma switchCost_congr {K T : ℕ} {h h' : BanditHistory K T} (e : actions h = actions h') :
    switchCost h = switchCost h' := by
  funext n₁ n₂; simp only [switchCost, act_congr e]

lemma stopTime_congr {K T : ℕ} (S : ℕ) {h h' : BanditHistory K T} (e : actions h = actions h') :
    stopTime S h = stopTime S h' := by
  simp only [stopTime, switchCost_congr e]

lemma measurableSet_E1 (S K T j : ℕ) (k : Fin K) : MeasurableSet (E1 S K T j k) := by
  apply measurableSet_of_actions
  intro h h' e hh
  unfold E1 at hh ⊢
  split_ifs at hh ⊢ <;>
  · simp only [Set.mem_setOf_eq, notChosen, act_congr e, stopTime_congr S e] at hh
    simpa only [Set.mem_setOf_eq, notChosen] using hh


lemma t1_mono {S K T : ℕ} (hK : 1 < K) (hKT : 2 * K ≤ T) :
    ∀ i i', i ≤ i' → t1 S K T i ≤ t1 S K T i' := by
  intro i i' hii
  by_cases hi : i = 0
  · subst hi; simp [t1]
  · obtain ⟨hm2, hmK⟩ := Kr_bounds (S := S) hK
    set m : ℝ := (K : ℝ) - (rIdx S K : ℝ) with hm
    have hm0 : (0 : ℝ) < m := by linarith
    have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
    have hmT : m ≤ T := by
      have : (2 * K : ℝ) ≤ T := by exact_mod_cast hKT
      have : (2 : ℝ) ≤ K := by exact_mod_cast hK
      linarith
    unfold t1
    rw [if_neg hi, if_neg (by omega), ← hm]
    apply Nat.floor_le_floor
    have hg : ∀ e : ℝ, m ^ (1 - e) * (T : ℝ) ^ e = m * ((T : ℝ) / m) ^ e := by
      intro e
      rw [Real.div_rpow hT0.le hm0.le, Real.rpow_sub hm0, Real.rpow_one]
      have : 0 < m ^ e := by positivity
      field_simp
    rw [hg, hg]
    apply mul_le_mul_of_nonneg_left _ hm0.le
    apply Real.rpow_le_rpow_of_exponent_le
    · rw [le_div_iff₀ hm0, one_mul]; exact hmT
    · have ha : 0 ≤ aExp (qIdx S K) := by
        unfold aExp
        have : (2 : ℝ) ^ (-((qIdx S K : ℕ) : ℝ)) ≤ 1 := by
          apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
          have : (0 : ℝ) ≤ ((qIdx S K : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        apply div_nonneg zero_le_one; linarith
      apply mul_le_mul_of_nonneg_right _ ha
      have : (2 : ℝ) ^ (1 - (i' : ℝ)) ≤ (2 : ℝ) ^ (1 - (i : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have : (i : ℝ) ≤ i' := by exact_mod_cast hii
        linarith
      linarith

/-- Windows inside `[1, B]` with monotone end points: their switch counts add up to at most
`S(1 : B)`. -/
lemma sum_window_switch_le_upto {K T : ℕ} (h : BanditHistory K T) (M : ℕ) (t : ℕ → ℕ)
    (ht : ∀ i i', i ≤ i' → t i ≤ t i') :
    ∑ j ∈ Finset.Icc 1 M, switchCost h (t (j - 1)) (t j) ≤ switchCost h 1 (t M) := by
  classical
  simp_rw [switchCost_eq_card]
  rw [← Finset.card_biUnion]
  · apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_biUnion, swSet, Finset.mem_filter] at hx ⊢
    obtain ⟨j, hj, hx1, hx2⟩ := hx
    simp only [Finset.mem_Icc] at hj
    have := ht j M hj.2
    refine ⟨hx1, ?_, ?_, ?_, ?_, hx2.2.2.2.2⟩ <;> omega
  · intro j hj j' hj' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [swSet, Finset.mem_filter] at hx hx'
    simp only [Finset.coe_Icc, Set.mem_Icc] at hj hj'
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := ht j (j' - 1) (by omega); omega
    · have := ht j' (j - 1) (by omega); omega

lemma switchCost_add {K T : ℕ} (h : BanditHistory K T) (a b : ℕ) :
    switchCost h 1 a + switchCost h a b ≤ switchCost h 1 (max a b) := by
  classical
  simp_rw [switchCost_eq_card]
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_union, swSet, Finset.mem_filter] at hx ⊢
    rcases hx with hx | hx
    · refine ⟨hx.1, ?_, ?_, ?_, ?_, hx.2.2.2.2.2⟩ <;> omega
    · refine ⟨hx.1, ?_, ?_, ?_, ?_, hx.2.2.2.2.2⟩ <;> omega
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [swSet, Finset.mem_filter] at hx hx'
    omega

lemma stopTime_le_of {K T : ℕ} (S : ℕ) (h : BanditHistory K T) (f : ℕ) (hf1 : 1 ≤ f)
    (hfT : f ≤ T) (hfS : switchCost h 1 f = S) : stopTime S h ≤ f := by
  have hmem : f ∈ (Finset.Icc 1 T).filter (fun t => switchCost h 1 t = S) := by
    simp [hf1, hfT, hfS]
  unfold stopTime
  rw [dif_pos ⟨f, hmem⟩]
  exact Finset.min'_le _ _ hmem


lemma act_valid {K T : ℕ} (h : BanditHistory K T) (t : ℕ) (k : Fin K)
    (hk : act h t = some k) : 1 ≤ t ∧ t ≤ T := by
  by_contra hc
  have : act h t = none := by simp [act, actA, hc]
  rw [this] at hk; exact absurd hk (by simp)

/-- The per-arm step of Lemma 6: an arm that is not among the first `c` distinct arms of
`[t_q, T]` triggers `E_{q+1,k}` or `E_{q+2,k}`. -/
lemma perk {K T : ℕ} (S : ℕ) (h : BanditHistory K T) (hsw : switchCost h 1 T ≤ S)
    (q : ℝ) (hq : 0 ≤ q) (tq mid cN : ℕ) (hc : (S : ℝ) / (q + 1) ≤ cN)
    (hb : q * S / (q + 1) ≤ (switchCost h 1 tq : ℝ)) (k : Fin K)
    (hk : ∀ f, tq ≤ f → f ≤ T → act h f = some k → cN ≤ switchCost h tq f) :
    notChosen h k tq mid ∨
      (stopTime S h ≤ mid ∧ act h (stopTime S h) = some k ∧
        notChosen h k tq (stopTime S h - 1)) := by
  classical
  by_cases hn : notChosen h k tq mid
  · exact Or.inl hn
  · right
    have hex : ∃ t, tq ≤ t ∧ t ≤ mid ∧ act h t = some k := by
      unfold notChosen at hn; push_neg at hn; exact hn
    set f := Nat.find hex with hfdef
    have hf := Nat.find_spec hex
    rw [← hfdef] at hf
    have hmin : ∀ t, t < f → ¬ (tq ≤ t ∧ t ≤ mid ∧ act h t = some k) := fun t ht =>
      Nat.find_min hex ht
    have hfv := act_valid h f k hf.2.2
    have hcf := hk f hf.1 hfv.2 hf.2.2
    -- the budget is exhausted at `f`
    have hadd := switchCost_add h tq f
    rw [max_eq_right hf.1] at hadd
    have hle : switchCost h 1 f ≤ S := (switchCost_mono1 h f T hfv.2).trans hsw
    have hS : switchCost h 1 f = S := by
      have h1 : (S : ℝ) ≤ (switchCost h 1 f : ℝ) := by
        have e : (S : ℝ) = q * S / (q + 1) + (S : ℝ) / (q + 1) := by field_simp
        have : (switchCost h 1 tq : ℝ) + (switchCost h tq f : ℝ) ≤ (switchCost h 1 f : ℝ) := by
          exact_mod_cast hadd
        have : (cN : ℝ) ≤ (switchCost h tq f : ℝ) := by exact_mod_cast hcf
        linarith
      have : S ≤ switchCost h 1 f := by exact_mod_cast h1
      omega
    have hτf := stopTime_le_of S h f hfv.1 hfv.2 hS
    have hτ1 : 1 ≤ stopTime S h := by
      have hmem : f ∈ (Finset.Icc 1 T).filter (fun t => switchCost h 1 t = S) := by
        simp [hfv.1, hfv.2, hS]
      unfold stopTime
      rw [dif_pos ⟨f, hmem⟩]
      exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.min'_mem _ ⟨f, hmem⟩)).1).1
    rcases Nat.lt_or_ge (stopTime S h) f with hlt | hge
    · have hstuck := no_switch_after S h hsw ⟨hτ1, by omega⟩
      have hτk : act h (stopTime S h) = some k := by
        rw [← hstuck f hlt.le hfv.2]; exact hf.2.2
      by_cases htq : tq ≤ stopTime S h
      · exact absurd ⟨htq, by omega, hτk⟩ (hmin _ hlt)
      · refine ⟨by omega, hτk, fun t ht1 ht2 => ?_⟩
        omega
    · have heq : stopTime S h = f := le_antisymm hτf hge
      rw [heq]
      refine ⟨hf.2.1, hf.2.2, fun t ht1 ht2 hc => hmin t (by omega) ⟨ht1, by omega, hc⟩⟩

open Classical in
/-- At most `c` arms appear in `[t_q, T]` before `c` switches have occurred there. -/
lemma card_first_le {K T : ℕ} (h : BanditHistory K T) (tq cN : ℕ) :
    (Finset.univ.filter (fun k : Fin K => ∃ f, tq ≤ f ∧ f ≤ T ∧ act h f = some k ∧
      switchCost h tq f < cN)).card ≤ cN := by
  classical
  set F := Finset.univ.filter (fun k : Fin K => ∃ f, tq ≤ f ∧ f ≤ T ∧ act h f = some k ∧
      switchCost h tq f < cN) with hF
  by_cases hne : F.Nonempty
  · obtain ⟨k0, hk0⟩ := hne
    rw [hF, Finset.mem_filter] at hk0
    obtain ⟨f0, _, hf0T, _, hf0c⟩ := hk0.2
    set g := Nat.findGreatest (fun f => switchCost h tq f < cN) T with hg
    have hgspec : switchCost h tq g < cN :=
      Nat.findGreatest_spec (P := fun f => switchCost h tq f < cN) hf0T hf0c
    have hsub : F ⊆ chosen h tq g := by
      intro k hk
      rw [hF, Finset.mem_filter] at hk
      obtain ⟨f, hf1, hf2, hf3, hf4⟩ := hk.2
      exact (mem_chosen _ _ _ _).mpr ⟨f, hf1,
        Nat.le_findGreatest (P := fun f => switchCost h tq f < cN) hf2 hf4, hf3⟩
    have := card_chosen_le h tq g
    have := Finset.card_le_card hsub
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp


lemma pathwise {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (h : BanditHistory K T)
    (hsw : switchCost h 1 T ≤ S) :
    (K : ℝ) - (⌈(S : ℝ) / ((qIdx S K : ℝ) + 1)⌉ : ℝ) ≤
      ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
        (E1 S K T j k).indicator (fun _ => (1 : ℝ)) h := by
  classical
  set q := qIdx S K with hqdef
  set c := ⌈(S : ℝ) / ((q : ℝ) + 1)⌉ with hcdef
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hc0 : 0 ≤ c := Int.ceil_nonneg (div_nonneg (Nat.cast_nonneg _) (by linarith))
  have hcS : (S : ℝ) / ((q : ℝ) + 1) ≤ c := Int.le_ceil _
  set g : ℕ → ℝ := fun j => ∑ k : Fin K, (E1 S K T j k).indicator (fun _ => (1 : ℝ)) h with hg
  have hg0 : ∀ j, 0 ≤ g j := fun j =>
    Finset.sum_nonneg (fun k _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  change (K : ℝ) - (c : ℝ) ≤ ∑ j ∈ Finset.Icc 1 (q + 2), g j
  by_cases ha : ∃ j ∈ Finset.Icc 1 q,
      (switchCost h (t1 S K T (j - 1)) (t1 S K T j) : ℝ) < (S : ℝ) / ((q : ℝ) + 1)
  · obtain ⟨j, hj, hjs⟩ := ha
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    have hjE : ∀ k, (h ∈ E1 S K T j k ↔ notChosen h k (t1 S K T (j - 1)) (t1 S K T j)) := by
      intro k; unfold E1; rw [if_neg (by omega), if_neg (by omega)]; rfl
    have hgj : g j = ((Finset.univ.filter (fun k : Fin K =>
        notChosen h k (t1 S K T (j - 1)) (t1 S K T j))).card : ℝ) := by
      simp only [hg, Set.indicator_apply, hjE]
      rw [Finset.sum_boole]
    have hcnt := notChosen_count h (t1 S K T (j - 1)) (t1 S K T j)
    have hsc : (switchCost h (t1 S K T (j - 1)) (t1 S K T j) : ℝ) ≤ (c : ℝ) - 1 := by
      have h1 : ((switchCost h (t1 S K T (j - 1)) (t1 S K T j) : ℤ) : ℝ) < (c : ℝ) := by
        push_cast; linarith
      have h2 : (switchCost h (t1 S K T (j - 1)) (t1 S K T j) : ℤ) < c := by exact_mod_cast h1
      have h3 : (switchCost h (t1 S K T (j - 1)) (t1 S K T j) : ℤ) ≤ c - 1 := by omega
      have h4 : ((switchCost h (t1 S K T (j - 1)) (t1 S K T j) : ℤ) : ℝ) ≤ ((c - 1 : ℤ) : ℝ) := by
        exact_mod_cast h3
      push_cast at h4; exact h4
    have hle : g j ≤ ∑ j ∈ Finset.Icc 1 (q + 2), g j :=
      Finset.single_le_sum (fun j _ => hg0 j) (Finset.mem_Icc.mpr ⟨hj1, by omega⟩)
    rw [hgj] at hle
    linarith
  · push_neg at ha
    -- the first `q` windows used at least `q S/(q+1)` switches
    have hsum := sum_window_switch_le_upto h q (t1 S K T) (t1_mono hK hT)
    have hb : (q : ℝ) * S / ((q : ℝ) + 1) ≤ (switchCost h 1 (t1 S K T q) : ℝ) := by
      have h1 : ∑ j ∈ Finset.Icc 1 q, (S : ℝ) / ((q : ℝ) + 1) ≤
          ∑ j ∈ Finset.Icc 1 q, (switchCost h (t1 S K T (j - 1)) (t1 S K T j) : ℝ) :=
        Finset.sum_le_sum ha
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at h1
      have h2 : (∑ j ∈ Finset.Icc 1 q, (switchCost h (t1 S K T (j - 1)) (t1 S K T j) : ℝ)) ≤
          (switchCost h 1 (t1 S K T q) : ℝ) := by exact_mod_cast hsum
      have h3 : ((q + 1 - 1 : ℕ) : ℝ) = (q : ℝ) := by simp
      rw [h3] at h1
      have : (q : ℝ) * ((S : ℝ) / ((q : ℝ) + 1)) = (q : ℝ) * S / ((q : ℝ) + 1) := by ring
      linarith
    set cN := c.toNat with hcNdef
    have hcN : (cN : ℝ) = (c : ℝ) := by
      have : ((c.toNat : ℤ)) = c := Int.toNat_of_nonneg hc0
      rw [hcNdef]; exact_mod_cast this
    set F := Finset.univ.filter (fun k : Fin K => ∃ f, t1 S K T q ≤ f ∧ f ≤ T ∧
      act h f = some k ∧ switchCost h (t1 S K T q) f < cN) with hF
    have hFc := card_first_le h (t1 S K T q) cN
    rw [← hF] at hFc
    have hk : ∀ k, k ∉ F → (h ∈ E1 S K T (q + 1) k ∨ h ∈ E1 S K T (q + 2) k) := by
      intro k hkF
      have := perk S h hsw (q : ℝ) hq0 (t1 S K T q) (mid1 S K T) cN (by rw [hcN]; exact hcS) hb k
        (fun f hf1 hf2 hf3 => by
          by_contra hlt; push_neg at hlt
          exact hkF (Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hf1, hf2, hf3, hlt⟩))
      rcases this with h1 | h1
      · left; unfold E1; rw [if_neg (by omega), if_pos rfl]; exact h1
      · right; unfold E1; rw [if_pos rfl]; exact h1
    -- count arms outside `F`
    have hpair : g (q + 1) + g (q + 2) ≤ ∑ j ∈ Finset.Icc 1 (q + 2), g j := by
      have hsub : ({q + 1, q + 2} : Finset ℕ) ⊆ Finset.Icc 1 (q + 2) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_Icc]; omega
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hg0 j)
      rwa [Finset.sum_pair (by omega)] at this
    have hpt : ∀ k : Fin K, (if k ∈ F then (0 : ℝ) else 1) ≤
        (E1 S K T (q + 1) k).indicator (fun _ => (1 : ℝ)) h +
          (E1 S K T (q + 2) k).indicator (fun _ => (1 : ℝ)) h := by
      intro k
      by_cases hkF : k ∈ F
      · rw [if_pos hkF]
        exact add_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
          (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      · rw [if_neg hkF]
        rcases hk k hkF with h1 | h1
        · rw [Set.indicator_of_mem h1]
          linarith [Set.indicator_nonneg (fun _ _ => zero_le_one) h
            (s := E1 S K T (q + 2) k) (f := fun _ => (1 : ℝ))]
        · rw [Set.indicator_of_mem h1]
          linarith [Set.indicator_nonneg (fun _ _ => zero_le_one) h
            (s := E1 S K T (q + 1) k) (f := fun _ => (1 : ℝ))]
    have hcount : ∑ k : Fin K, (if k ∈ F then (0 : ℝ) else 1) = (K : ℝ) - F.card := by
      have h1 : ∑ k : Fin K, (if k ∈ F then (0 : ℝ) else 1) +
          ∑ k : Fin K, (if k ∈ F then (1 : ℝ) else 0) = K := by
        rw [← Finset.sum_add_distrib]
        have : ∀ k : Fin K, ((if k ∈ F then (0 : ℝ) else 1) + (if k ∈ F then (1 : ℝ) else 0)) = 1 := by
          intro k; split_ifs <;> norm_num
        simp [this]
      have h2 : ∑ k : Fin K, (if k ∈ F then (1 : ℝ) else 0) = F.card := by
        rw [Finset.sum_boole]; simp
      linarith
    have hsumk := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hpt k)
    rw [hcount, Finset.sum_add_distrib] at hsumk
    have hFc' : (F.card : ℝ) ≤ cN := by exact_mod_cast hFc
    rw [hcN] at hFc'
    change (K : ℝ) - F.card ≤ g (q + 1) + g (q + 2) at hsumk
    linarith

end BwSC.LowerBound.L6Aux

open BwSC.LowerBound BwSC.LowerBound.L6Aux in
theorem solution {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π) (μvec : Fin K → ℝ) :
    (K : ℝ) - (⌈(S : ℝ) / ((qIdx S K : ℝ) + 1)⌉ : ℝ) ≤
      ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
        ((banditMeasure (gaussianBandit μvec) π T) (E1 S K T j k)).toReal := by
  set P := banditMeasure (gaussianBandit μvec) π T with hP
  set f : BanditHistory K T → ℝ := fun h => ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
    (E1 S K T j k).indicator (fun _ => (1 : ℝ)) h with hf
  have hint : ∀ j k, Integrable ((E1 S K T j k).indicator (fun _ => (1 : ℝ))) P :=
    fun j k => (integrable_const (1 : ℝ)).indicator (measurableSet_E1 _ _ _ _ _)
  have hrepr : ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K, (P (E1 S K T j k)).toReal =
      ∫ h, f h ∂P := by
    rw [hf, integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_finsetSum _ (fun k _ => hint j k)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [integral_indicator_const _ (measurableSet_E1 _ _ _ _ _)]
    simp [Measure.real]
  rw [hrepr]
  have hbound : ∀ᵐ h ∂P, (K : ℝ) - (⌈(S : ℝ) / ((qIdx S K : ℝ) + 1)⌉ : ℝ) ≤ f h := by
    filter_upwards [hπ μvec] with h hsw
    exact pathwise hK hT h hsw
  have hfint : Integrable f P := integrable_finsetSum _ (fun j _ => integrable_finsetSum _
    (fun k _ => hint j k))
  have := integral_mono_ae (integrable_const _) hfint hbound
  simpa using this
