-- Prove2me | solution 1 for BwSC.LowerBound.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T03:34:59.120351+00:00
-- url     : https://prove2.me/submissions/0f462622-c1f4-428d-92a7-5875b78f6cd7

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound.L7Aux

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


lemma measurableSet_E2 (S K T j : ℕ) (k : Fin K) : MeasurableSet (E2 S K T j k) := by
  have : E2 S K T j k = actions ⁻¹' (actions '' E2 S K T j k) := by
    ext h; constructor
    · intro hh; exact ⟨h, hh, rfl⟩
    · rintro ⟨h', hh', e⟩
      have hact : act h' = act h := by funext t; simp [act, e]
      simp only [E2, notChosen, Set.mem_setOf_eq] at hh' ⊢
      rw [← hact]; exact hh'
  rw [this]; exact measurable_actions (Set.toFinite _).measurableSet

lemma t2_mono {S K T : ℕ} (hK : 0 < K) (hKT : K ≤ T) :
    ∀ i i', i ≤ i' → t2 S K T i ≤ t2 S K T i' := by
  intro i i' hii
  by_cases hi : i = 0
  · subst hi; simp [t2]
  · have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
    have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
    unfold t2
    rw [if_neg hi, if_neg (by omega)]
    apply Nat.floor_le_floor
    have hg : ∀ e : ℝ, (K : ℝ) ^ (1 - e) * (T : ℝ) ^ e = K * ((T : ℝ) / K) ^ e := by
      intro e
      rw [Real.div_rpow hT0.le hK0.le, Real.rpow_sub hK0, Real.rpow_one]
      have : 0 < (K : ℝ) ^ e := by positivity
      field_simp
    rw [hg, hg]
    apply mul_le_mul_of_nonneg_left _ hK0.le
    apply Real.rpow_le_rpow_of_exponent_le
    · rw [le_div_iff₀ hK0, one_mul]; exact_mod_cast hKT
    · have ha : 0 ≤ aExp (qIdx S K + 1) := by
        unfold aExp
        have : (2 : ℝ) ^ (-((qIdx S K + 1 : ℕ) : ℝ)) ≤ 1 := by
          apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
          have : (0 : ℝ) ≤ ((qIdx S K + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        apply div_nonneg zero_le_one; linarith
      apply mul_le_mul_of_nonneg_right _ ha
      have : (2 : ℝ) ^ (1 - (i' : ℝ)) ≤ (2 : ℝ) ^ (1 - (i : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have : (i : ℝ) ≤ i' := by exact_mod_cast hii
        linarith
      linarith

end BwSC.LowerBound.L7Aux

open BwSC.LowerBound BwSC.LowerBound.L7Aux in
theorem solution {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π) (μvec : Fin K → ℝ) :
    (K : ℝ) - 1 - (⌊(S : ℝ) / ((qIdx S K : ℝ) + 2)⌋ : ℝ) ≤
      ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
        ((banditMeasure (gaussianBandit μvec) π T) (E2 S K T j k)).toReal := by
  classical
  set P := banditMeasure (gaussianBandit μvec) π T with hP
  set q := qIdx S K with hq
  set f : BanditHistory K T → ℝ := fun h => ∑ j ∈ Finset.Icc 1 (q + 2), ∑ k : Fin K,
    (E2 S K T j k).indicator (fun _ => (1 : ℝ)) h with hf
  have hint : ∀ j k, Integrable ((E2 S K T j k).indicator (fun _ => (1 : ℝ))) P :=
    fun j k => (integrable_const (1 : ℝ)).indicator (measurableSet_E2 _ _ _ _ _)
  have hrepr : ∑ j ∈ Finset.Icc 1 (q + 2), ∑ k : Fin K, (P (E2 S K T j k)).toReal =
      ∫ h, f h ∂P := by
    rw [hf, integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_finsetSum _ (fun k _ => hint j k)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [integral_indicator_const _ (measurableSet_E2 _ _ _ _ _)]
    simp [Measure.real]
  rw [hrepr]
  set c : ℝ := (K : ℝ) - 1 - (⌊(S : ℝ) / ((q : ℝ) + 2)⌋ : ℝ) with hc
  have hbound : ∀ᵐ h ∂P, c ≤ f h := by
    filter_upwards [hπ μvec] with h hsw
    -- pigeonhole: some window has at most `S / (q+2)` switches
    have hsum := sum_window_switch_le h (q + 2) (t2 S K T) (t2_mono (by omega) (by omega))
    obtain ⟨j, hj, hjs⟩ : ∃ j ∈ Finset.Icc 1 (q + 2),
        switchCost h (t2 S K T (j - 1)) (t2 S K T j) ≤ S / (q + 2) := by
      by_contra hne
      push_neg at hne
      have h1 : ∑ j ∈ Finset.Icc 1 (q + 2), (S / (q + 2) + 1) ≤
          ∑ j ∈ Finset.Icc 1 (q + 2), switchCost h (t2 S K T (j - 1)) (t2 S K T j) :=
        Finset.sum_le_sum (fun j hj => hne j hj)
      rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul] at h1
      have h2 := Nat.lt_mul_div_succ S (by omega : 0 < q + 2)
      have : q + 2 + 1 - 1 = q + 2 := by omega
      rw [this] at h1
      omega
    -- the count on that window
    have hcnt := notChosen_count h (t2 S K T (j - 1)) (t2 S K T j)
    have hfl : (switchCost h (t2 S K T (j - 1)) (t2 S K T j) : ℝ) ≤
        (⌊(S : ℝ) / ((q : ℝ) + 2)⌋ : ℝ) := by
      have h1 : ((switchCost h (t2 S K T (j - 1)) (t2 S K T j) : ℤ) : ℝ) ≤ (S : ℝ) / ((q : ℝ) + 2) := by
        have : ((S / (q + 2) : ℕ) : ℝ) ≤ (S : ℝ) / ((q + 2 : ℕ) : ℝ) := Nat.cast_div_le
        push_cast at this ⊢
        have h3 : (switchCost h (t2 S K T (j - 1)) (t2 S K T j) : ℝ) ≤ ((S / (q + 2) : ℕ) : ℝ) := by
          exact_mod_cast hjs
        linarith
      have := Int.le_floor.mpr h1
      exact_mod_cast this
    have hinner : ((Finset.univ.filter (fun k : Fin K => notChosen h k (t2 S K T (j - 1))
        (t2 S K T j))).card : ℝ) = ∑ k : Fin K, (E2 S K T j k).indicator (fun _ => (1 : ℝ)) h := by
      simp only [Set.indicator_apply, E2, Set.mem_setOf_eq]
      rw [Finset.sum_boole]
    have hle : ∑ k : Fin K, (E2 S K T j k).indicator (fun _ => (1 : ℝ)) h ≤ f h := by
      rw [hf]
      apply Finset.single_le_sum (f := fun j => ∑ k : Fin K,
        (E2 S K T j k).indicator (fun _ => (1 : ℝ)) h) _ hj
      intro j' _
      exact Finset.sum_nonneg (fun k _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    rw [hc]
    linarith
  have hfint : Integrable f P := integrable_finsetSum _ (fun j _ => integrable_finsetSum _
    (fun k _ => hint j k))
  have := integral_mono_ae (integrable_const c) hfint hbound
  simpa using this
