-- Prove2me | solution 1 for AvgCompletionSched.DelayList.no_uncharged_idle
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T12:21:20.764138+00:00
-- url     : https://prove2.me/submissions/dd3c48a8-d59c-4848-95e0-94e4a5692a31

import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model
import Definitions.Def_AvgCompletionSched_DelayList_Algorithm
import Definitions.Def_AvgCompletionSched_DelayList_Analysis



namespace AvgCompletionSched.DelayList

open MeasureTheory

/-- Abstract real-analysis lemma. -/
theorem aux_cl_abs (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hfM : ∀ x, f x ≤ M) (T Z : Set ℝ) (hT : MeasurableSet T) (hZ : MeasurableSet Z)
    (a b : ℝ) (hTab : T ⊆ Set.Icc a b) (c : ℝ) (hc : 0 ≤ c)
    (hTZ : ∫ x in T ∩ Z, f x = 0)
    (h : ∀ s ∈ T, s ∉ Z → 0 < f s → ∫ x in T ∩ Set.Iio s, f x < c) :
    ∫ x in T, f x ≤ c := by
  have hM0 : 0 ≤ M := (hf0 0).trans (hfM 0)
  have hint : ∀ A ⊆ Set.Icc a b, IntegrableOn f A := by
    intro A hA
    refine Measure.integrableOn_of_bounded (M := M) ?_ hf.aestronglyMeasurable ?_
    · exact ne_top_of_le_ne_top (by simp) (measure_mono hA)
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
      exact hfM x
  have hsplit : ∫ x in T, f x = (∫ x in T \ Z, f x) + ∫ x in T ∩ Z, f x := by
    rw [← integral_inter_add_sdiff hZ (hint _ hTab)]
    ring
  rw [hsplit, hTZ, add_zero]
  by_cases hG : ∃ s ∈ T \ Z, 0 < f s
  · set G := {s | s ∈ T \ Z ∧ 0 < f s} with hGdef
    have hGbdd : BddAbove G := ⟨b, fun s hs => (hTab hs.1.1).2⟩
    have hGne : G.Nonempty := by
      obtain ⟨s, hs, hs'⟩ := hG
      exact ⟨s, hs, hs'⟩
    set g := sSup G with hg
    have h1 : ∫ x in T \ Z, f x = ∫ x in (T \ Z) ∩ Set.Iic g, f x := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hT.diff hZ) Set.inter_subset_left
      intro x hx
      by_contra hne
      have hpos : 0 < f x := lt_of_le_of_ne (hf0 x) (Ne.symm hne)
      exact hx.2 ⟨hx.1, le_csSup hGbdd ⟨hx.1, hpos⟩⟩
    rw [h1]
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hδ : 0 < ε / (M + 1) := div_pos hε (by linarith)
    obtain ⟨s, hsG, hs⟩ := exists_lt_of_lt_csSup hGne (show g - ε / (M + 1) < g by linarith)
    have hsg : s ≤ g := le_csSup hGbdd hsG
    have hsplit2 := integral_inter_add_sdiff (μ := volume) (f := f)
      (s := (T \ Z) ∩ Set.Iic g) (t := Set.Iio s) measurableSet_Iio
      (hint _ ((Set.inter_subset_left.trans Set.sdiff_subset).trans hTab))
    rw [← hsplit2]
    have hA : ∫ x in (T \ Z) ∩ Set.Iic g ∩ Set.Iio s, f x < c := by
      refine lt_of_le_of_lt ?_ (h s hsG.1.1 hsG.1.2 hsG.2)
      refine setIntegral_mono_set (hint _ (Set.inter_subset_left.trans hTab))
        (Filter.Eventually.of_forall fun x => hf0 x) (Filter.Eventually.of_forall ?_)
      intro x hx
      exact ⟨hx.1.1.1, hx.2⟩
    have hB : ∫ x in (((T \ Z) ∩ Set.Iic g) \ Set.Iio s), f x ≤ M * (g - s) := by
      have hsub : ((T \ Z) ∩ Set.Iic g) \ Set.Iio s ⊆ Set.Icc s g := by
        intro x hx
        exact ⟨not_lt.mp hx.2, hx.1.2⟩
      calc ∫ x in (((T \ Z) ∩ Set.Iic g) \ Set.Iio s), f x ≤ ∫ x in Set.Icc s g, f x := by
            refine setIntegral_mono_set (hint _ ?_)
              (Filter.Eventually.of_forall fun x => hf0 x) (Filter.Eventually.of_forall hsub)
            intro x hx
            have hxT : s ∈ Set.Icc a b := hTab hsG.1.1
            have hgb : g ≤ b := csSup_le hGne fun y hy => (hTab hy.1.1).2
            exact ⟨le_trans hxT.1 hx.1, le_trans hx.2 hgb⟩
        _ ≤ ‖∫ x in Set.Icc s g, f x‖ := Real.le_norm_self _
        _ ≤ M * volume.real (Set.Icc s g) := by
            apply norm_setIntegral_le_of_norm_le_const (by simp)
            intro x _
            rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
            exact hfM x
        _ = M * (g - s) := by rw [Real.volume_real_Icc_of_le hsg]
    have : M * (g - s) < ε := by
      have h2 : g - s < ε / (M + 1) := by linarith
      calc M * (g - s) ≤ (M + 1) * (g - s) := by nlinarith
        _ < (M + 1) * (ε / (M + 1)) := by
            apply mul_lt_mul_of_pos_left h2; linarith
        _ = ε := by field_simp
    linarith
  · push Not at hG
    have : ∫ x in T \ Z, f x = 0 := by
      rw [setIntegral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun x => hf0 x)
        (hint _ (Set.sdiff_subset.trans hTab))]
      rw [Filter.EventuallyEq, ae_restrict_iff' (hT.diff hZ)]
      exact Filter.Eventually.of_forall fun x hx => le_antisymm (hG x hx) (hf0 x)
    rw [this]; exact hc


section
variable {n m : ℕ} {I : Instance n}

theorem aux_cl_idle_meas (D : DelayListRun I m) : Measurable D.idle := by
  have h : D.idle = fun t => (m : ℝ) -
      ∑ k, (Set.Ico (D.S k) (D.S k + I.p k)).indicator (fun _ => (1 : ℝ)) t := by
    funext t
    unfold DelayListRun.idle
    congr 1
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : D.S k ≤ t ∧ t < D.S k + I.p k
    · rw [if_pos hk, Set.indicator_of_mem (Set.mem_Ico.mpr hk)]
    · rw [if_neg hk]
      simp only [Set.indicator, Set.mem_Ico]
      rw [if_neg hk]
  rw [h]
  exact measurable_const.sub
    (Finset.measurable_sum _ fun k _ => measurable_const.indicator measurableSet_Ico)

theorem aux_cl_idle_nonneg (D : DelayListRun I m)
    (hB : ∀ j k, D.Before k j → D.M k = D.M j → D.S k + I.p k ≤ D.S j) (t : ℝ) :
    0 ≤ D.idle t := by
  unfold DelayListRun.idle
  have key : ∀ s : Finset (Fin n), (∀ k ∈ s, D.S k ≤ t ∧ t < D.S k + I.p k) →
      (s.card : ℝ) ≤ m := by
    intro s hs
    have : s.card ≤ (Finset.univ : Finset (Fin m)).card := by
      refine Finset.card_le_card_of_injOn D.M (fun _ _ => Finset.mem_univ _) ?_
      intro a ha b hb hab
      by_contra hne
      have ha' := hs a ha
      have hb' := hs b hb
      rcases lt_trichotomy (D.ev.symm a) (D.ev.symm b) with h | h | h
      · have := hB b a h hab; linarith [ha'.2, hb'.1]
      · exact hne (D.ev.symm.injective h)
      · have := hB a b h hab.symm; linarith [ha'.1, hb'.2]
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  exact sub_nonneg.mpr (key _ fun k hk => (Finset.mem_filter.mp hk).2)

theorem aux_cl_idle_le (D : DelayListRun I m) (t : ℝ) : D.idle t ≤ m := by
  unfold DelayListRun.idle
  exact sub_le_self _ (Nat.cast_nonneg _)

theorem aux_cl_idle_nonpos (D : DelayListRun I m) (t : ℝ) (h : ¬ D.IdleMachineAt t) :
    D.idle t ≤ 0 := by
  unfold DelayListRun.idle
  unfold DelayListRun.IdleMachineAt at h
  push Not at h
  have key : ∀ s : Finset (Fin n), (∀ k, (D.S k ≤ t ∧ t < D.S k + I.p k) → k ∈ s) →
      (m : ℝ) ≤ s.card := by
    intro s hs
    have hsub : (Finset.univ : Finset (Fin m)) ⊆ s.image D.M := by
      intro μ _
      obtain ⟨k, hk, hr⟩ := h μ
      exact Finset.mem_image.mpr ⟨k, hs k hr, hk⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := s) (f := D.M)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    exact_mod_cast h1.trans h2
  exact sub_nonpos.mpr (key _ fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)

theorem aux_cl_intOn (D : DelayListRun I m)
    (hB : ∀ j k, D.Before k j → D.M k = D.M j → D.S k + I.p k ≤ D.S j)
    (A : Set ℝ) (a b : ℝ) (hA : A ⊆ Set.Icc a b) : IntegrableOn D.idle A := by
  refine Measure.integrableOn_of_bounded (M := m) ?_ (aux_cl_idle_meas D).aestronglyMeasurable ?_
  · exact ne_top_of_le_ne_top (by simp) (measure_mono hA)
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (aux_cl_idle_nonneg D hB x)]
    exact aux_cl_idle_le D x

theorem aux_cl_ready_mono (D : DelayListRun I m) {s s' : ℝ} {k : Fin n} (h : D.Ready s k)
    (hs : s ≤ s') : D.Ready s' k :=
  ⟨h.1.trans hs, fun i hi => (h.2 i hi).trans hs⟩

theorem aux_cl_q_le (D : DelayListRun I m) {s : ℝ} {k : Fin n} (h : D.Ready s k) :
    D.q k ≤ s := by
  unfold DelayListRun.q
  split_ifs with hne
  · exact max_le (Finset.sup'_le _ _ fun i hi => h.2 i (by simpa [Instance.preds] using hi)) h.1
  · exact h.1

theorem aux_cl_ready_of (D : DelayListRun I m) {s : ℝ} {k : Fin n} (h : D.q k ≤ s) :
    D.Ready s k := by
  unfold DelayListRun.q at h
  split_ifs at h with hne
  · refine ⟨(le_max_right _ _).trans h, fun i hi => ?_⟩
    have hi' : i ∈ I.preds k := by simpa [Instance.preds] using hi
    exact ((Finset.le_sup' D.C hi').trans (le_max_left _ _)).trans h
  · exact ⟨h, fun i hi => absurd ⟨i, by simpa [Instance.preds] using hi⟩ hne⟩

theorem aux_cl_r_le_q (D : DelayListRun I m) (k : Fin n) : I.r k ≤ D.q k := by
  unfold DelayListRun.q
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

theorem aux_cl_before_of_lt (D : DelayListRun I m) (h1 : ∀ j k, D.Before k j → D.S k ≤ D.S j)
    {k l : Fin n} (h : D.S k < D.S l) : D.Before k l := by
  unfold DelayListRun.Before
  rcases lt_trichotomy (D.ev.symm k) (D.ev.symm l) with h' | h' | h'
  · exact h'
  · have := D.ev.symm.injective h'
    subst this
    exact absurd h (lt_irrefl _)
  · have := h1 k l h'
    linarith

theorem aux_cl_gc {π : Fin n ≃ Fin n} {β : ℝ} (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) :
    ∀ l, ∫ t in Set.Ioo (D.q l) (D.S l) \ ⋃ k ∈ {k | D.Before k l}, D.window k, D.idle t
      ≤ β * I.p l := by
  obtain ⟨hB1, hB2, hC, hN⟩ := hD
  have hnn := aux_cl_idle_nonneg D hB2
  have hint := aux_cl_intOn D hB2
  suffices H : ∀ a : ℕ, ∀ l, (D.ev.symm l : ℕ) = a →
      ∫ t in Set.Ioo (D.q l) (D.S l) \ ⋃ k ∈ {k | D.Before k l}, D.window k, D.idle t
        ≤ β * I.p l by
    intro l
    exact H _ l rfl
  intro a
  induction a using Nat.strong_induction_on with
  | _ a IH =>
  intro l hl
  have IH' : ∀ k, D.Before k l →
      ∫ t in Set.Ioo (D.q k) (D.S k) \ ⋃ k' ∈ {k' | D.Before k' k}, D.window k', D.idle t
        ≤ β * I.p k := by
    intro k hk
    refine IH _ ?_ k rfl
    rw [← hl]
    exact hk
  have hWm : MeasurableSet (⋃ k ∈ {k | D.Before k l}, D.window k) :=
    MeasurableSet.biUnion (Set.to_countable _) fun k _ => measurableSet_Ioo
  set T := Set.Ioo (D.q l) (D.S l) \ ⋃ k ∈ {k | D.Before k l}, D.window k with hT
  set Z := ⋃ k ∈ {k | D.Before k l}, (Set.Ico (D.q k) (D.S k) \ D.window k) with hZ
  have hTm : MeasurableSet T := measurableSet_Ioo.diff hWm
  have hZm : MeasurableSet Z :=
    MeasurableSet.biUnion (Set.to_countable _) fun k _ => measurableSet_Ico.diff measurableSet_Ioo
  have hTsub : T ⊆ Set.Icc (D.q l) (D.S l) := fun x hx => ⟨hx.1.1.le, hx.1.2.le⟩
  have hq0 : 0 ≤ D.q l := (I.r_nonneg l).trans (aux_cl_r_le_q D l)
  -- Step A
  have hA : ∀ k, D.Before k l →
      ∫ t in T ∩ (Set.Ico (D.q k) (D.S k) \ D.window k), D.idle t = 0 := by
    intro k hk
    refine le_antisymm ?_ (integral_nonneg fun t => hnn t)
    have hsubW : ∀ x, x ∈ T → x ∉ ⋃ k' ∈ {k' | D.Before k' k}, D.window k' := by
      intro x hx hx'
      simp only [Set.mem_iUnion] at hx'
      obtain ⟨k', hk', hxk'⟩ := hx'
      exact hx.2 (Set.mem_biUnion (show D.Before k' l from lt_trans hk' hk) hxk')
    rcases hC k with ⟨_, _, hτ⟩ | ⟨_, _, _, _, _, hτS, hch⟩
    · have hsub : T ∩ (Set.Ico (D.q k) (D.S k) \ D.window k) ⊆ {D.q k} := by
        intro x hx
        simp only [DelayListRun.window, hτ, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_Ico,
          Set.mem_Ioo] at hx
        simp only [Set.mem_singleton_iff]
        by_contra hne
        exact hx.2.2 ⟨lt_of_le_of_ne hx.2.1.1 (Ne.symm hne), hx.2.1.2⟩
      rw [setIntegral_measure_zero _ (measure_mono_null hsub Real.volume_singleton)]
    · by_cases hqτ : D.q k ≤ D.τ k
      · have hAm : MeasurableSet
            (Set.Ioo (D.q k) (D.S k) \ ⋃ k' ∈ {k' | D.Before k' k}, D.window k') :=
          measurableSet_Ioo.diff
            (MeasurableSet.biUnion (Set.to_countable _) fun k _ => measurableSet_Ioo)
        have hAsub : Set.Ioo (D.q k) (D.S k) \ ⋃ k' ∈ {k' | D.Before k' k}, D.window k' ⊆
            Set.Icc (D.q k) (D.S k) := fun x hx => ⟨hx.1.1.le, hx.1.2.le⟩
        have hIHk := IH' k hk
        have hsplitA := integral_inter_add_sdiff (μ := volume) (f := D.idle)
          (s := Set.Ioo (D.q k) (D.S k) \ ⋃ k' ∈ {k' | D.Before k' k}, D.window k')
          (t := D.window k) measurableSet_Ioo (hint _ _ _ hAsub)
        have hAinter : (Set.Ioo (D.q k) (D.S k) \ ⋃ k' ∈ {k' | D.Before k' k}, D.window k') ∩
            D.window k = D.chargedSet k := by
          ext x
          simp only [DelayListRun.chargedSet, DelayListRun.window, Set.mem_inter_iff,
            Set.mem_sdiff, Set.mem_Ioo]
          constructor
          · rintro ⟨⟨_, h2⟩, h3⟩
            exact ⟨h3, h2⟩
          · rintro ⟨h3, h2⟩
            exact ⟨⟨⟨lt_of_le_of_lt hqτ h3.1, h3.2⟩, h2⟩, h3⟩
        rw [hAinter] at hsplitA
        have hch' : ∫ t in D.chargedSet k, D.idle t = β * I.p k := hch
        rw [hch'] at hsplitA
        calc ∫ t in T ∩ (Set.Ico (D.q k) (D.S k) \ D.window k), D.idle t
            ≤ ∫ t in (Set.Ioo (D.q k) (D.S k) \ ⋃ k' ∈ {k' | D.Before k' k}, D.window k') \
                D.window k, D.idle t := by
              refine setIntegral_mono_set (hint _ _ _ (Set.sdiff_subset.trans hAsub))
                (Filter.Eventually.of_forall fun t => hnn t) ?_
              rw [ae_le_set]
              refine measure_mono_null ?_ (Real.volume_singleton (a := D.q k))
              intro x hx
              simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_Ico] at hx
              simp only [Set.mem_singleton_iff]
              by_contra hne
              apply hx.2
              refine ⟨⟨⟨lt_of_le_of_ne hx.1.2.1.1 (Ne.symm hne), hx.1.2.1.2⟩,
                hsubW x hx.1.1⟩, hx.1.2.2⟩
          _ ≤ 0 := by linarith
      · have hsub : T ∩ (Set.Ico (D.q k) (D.S k) \ D.window k) ⊆ {D.q k} := by
          intro x hx
          simp only [DelayListRun.window, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_Ico,
            Set.mem_Ioo] at hx
          exfalso
          apply hx.2.2
          exact ⟨lt_of_lt_of_le (not_le.mp hqτ) hx.2.1.1, hx.2.1.2⟩
        rw [setIntegral_measure_zero _ (measure_mono_null hsub Real.volume_singleton)]
  -- Step B
  have hBz : ∫ t in T ∩ Z, D.idle t = 0 := by
    have hae : ∀ᵐ t ∂(volume.restrict (T ∩ Z)), D.idle t = 0 := by
      have heq : T ∩ Z = ⋃ k ∈ {k | D.Before k l},
          (T ∩ (Set.Ico (D.q k) (D.S k) \ D.window k)) := by
        rw [hZ, Set.inter_iUnion₂]
      rw [heq, ae_restrict_biUnion_iff _ (Set.to_countable _)]
      intro k hk
      have := hA k hk
      rw [setIntegral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun t => hnn t)
        (hint _ _ _ (Set.inter_subset_left.trans hTsub))] at this
      exact this.mono fun x hx => by simpa using hx
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) hae]
    simp
  -- Step C
  have hCstep : ∀ s ∈ T, s ∉ Z → 0 < D.idle s →
      ∫ t in T ∩ Set.Iio s, D.idle t < β * I.p l := by
    intro s hsT hsZ hpos
    have hidle : D.IdleMachineAt s := by
      by_contra hc
      linarith [aux_cl_idle_nonpos D s hc]
    have hs0 : 0 ≤ s := hq0.trans hsT.1.1.le
    have hrl : D.Ready s l := aux_cl_ready_of D hsT.1.1.le
    classical
    obtain ⟨k0, hk0C, hk0min⟩ :=
      (Finset.univ.filter (fun k => s < D.S k ∧ D.Ready s k)).exists_min_image
        (fun k => π.symm k) ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsT.1.2, hrl⟩⟩
    obtain ⟨_, hk0S, hk0R⟩ := Finset.mem_filter.mp hk0C
    have hU := (hN s hs0 hidle).2 k0 hk0S hk0R
      (fun l' h1 h2 => hk0min l' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩))
    have hk0l : k0 = l := by
      by_contra hne
      have hlt : π.symm k0 < π.symm l :=
        lt_of_le_of_ne (hk0min l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsT.1.2, hrl⟩))
          (fun h => hne (π.symm.injective h))
      have hbef : D.Before k0 l := by
        by_contra hnb
        rcases hC l with ⟨h1, _, _⟩ | ⟨_, _, h3, _⟩
        · exact absurd (h1 k0 hnb) (not_le.mpr hlt)
        · exact absurd (h3 k0 hnb (aux_cl_ready_mono D hk0R hsT.1.2.le)) (not_le.mpr hlt)
      have hqk : D.q k0 ≤ s := aux_cl_q_le D hk0R
      have hnotwin : s ∉ D.window k0 := fun h => hsT.2 (Set.mem_biUnion hbef h)
      exact hsZ (Set.mem_biUnion hbef ⟨⟨hqk, hk0S⟩, hnotwin⟩)
    rw [hk0l] at hU
    calc ∫ t in T ∩ Set.Iio s, D.idle t ≤ D.unchargedAfter s := by
          unfold DelayListRun.unchargedAfter
          refine setIntegral_mono_set (hint _ 0 s ?_) (Filter.Eventually.of_forall fun t => hnn t)
            (Filter.Eventually.of_forall ?_)
          · intro x hx
            exact ⟨hx.1.1, hx.1.2.le⟩
          · intro x hx
            refine ⟨⟨hq0.trans hx.1.1.1.le, hx.2⟩, ?_⟩
            intro hx'
            simp only [Set.mem_iUnion] at hx'
            obtain ⟨k', hk', hxk'⟩ := hx'
            have hk'' : D.S k' ≤ s := hk'
            exact hx.1.2 (Set.mem_biUnion
              (aux_cl_before_of_lt D hB1 (lt_of_le_of_lt hk'' hsT.1.2)) hxk')
      _ < β * I.p l := hU
  -- Step D
  exact aux_cl_abs D.idle (aux_cl_idle_meas D) m hnn (aux_cl_idle_le D) T Z hTm hZm _ _ hTsub
    (β * I.p l) (mul_nonneg hβ.le (I.p_pos l).le) hBz hCstep

end

theorem aux_kpl_kappa_eq {n : ℕ} (I : Instance n) (j : Fin n) :
    kappa I j =
      if h : (I.preds j).Nonempty then
        I.p j + max ((I.preds j).attach.sup' (Finset.attach_nonempty_iff.mpr h)
          fun i => kappa I i.1) (I.r j)
      else I.p j + I.r j := by
  unfold kappa
  rw [WellFounded.fix_eq]

theorem aux_kpl_ge {n : ℕ} (I : Instance n) (j : Fin n) : I.p j + I.r j ≤ kappa I j := by
  rw [aux_kpl_kappa_eq]
  split_ifs with h
  · have := le_max_right ((I.preds j).attach.sup' (Finset.attach_nonempty_iff.mpr h)
          fun i => kappa I i.1) (I.r j)
    linarith
  · exact le_refl _

theorem aux_kpl_prec {n : ℕ} (I : Instance n) (a b : Fin n) (hab : I.prec a b) :
    kappa I a + I.p b ≤ kappa I b := by
  have ha : a ∈ I.preds b := by simp [Instance.preds, hab]
  have hne : (I.preds b).Nonempty := ⟨a, ha⟩
  rw [aux_kpl_kappa_eq I b, dif_pos hne]
  have h1 : kappa I a ≤ (I.preds b).attach.sup' (Finset.attach_nonempty_iff.mpr hne)
      (fun i => kappa I i.1) :=
    Finset.le_sup' (f := fun i : {x // x ∈ I.preds b} => kappa I i.1)
      (Finset.mem_attach _ ⟨a, ha⟩)
  have h2 := le_max_left ((I.preds b).attach.sup' (Finset.attach_nonempty_iff.mpr hne)
      (fun i => kappa I i.1)) (I.r b)
  linarith

theorem aux_kpl_chain {n m : ℕ} (I : Instance n) (D : DelayListRun I m) :
    ∀ (l : List (Fin n)) (a : Fin n), List.IsChain D.PathStep (a :: l) →
      kappa I a + (l.map I.p).sum ≤ kappa I ((a :: l).getLast (List.cons_ne_nil _ _)) := by
  intro l
  induction l with
  | nil => intro a _; simp
  | cons b l ih =>
    intro a h
    rw [List.isChain_cons_cons] at h
    obtain ⟨hab, hrest⟩ := h
    have h1 := ih b hrest
    have h2 := aux_kpl_prec I a b hab.1
    rw [List.getLast_cons_cons]
    simp only [List.map_cons, List.sum_cons]
    linarith


section
variable {n m : ℕ} {I : Instance n}

theorem aux_nui_before_total (D : DelayListRun I m) {k l : Fin n} (h : ¬ D.Before k l)
    (hne : k ≠ l) : D.Before l k := by
  unfold DelayListRun.Before at *
  rcases lt_trichotomy (D.ev.symm k) (D.ev.symm l) with h' | h' | h'
  · exact absurd h' h
  · exact absurd (D.ev.symm.injective h') hne
  · exact h'

theorem aux_nui_zero {π : Fin n ≃ Fin n} {β : ℝ} (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i : Fin n) :
    ∫ t in (Set.Ioo (D.q i) (D.S i) \ ⋃ k ∈ {k | D.Before k i}, D.window k) \ D.window i,
      D.idle t = 0 := by
  have hnn := aux_cl_idle_nonneg D hD.2.1
  have hint := aux_cl_intOn D hD.2.1
  by_cases hτq : D.τ i ≤ D.q i
  · have : (Set.Ioo (D.q i) (D.S i) \ ⋃ k ∈ {k | D.Before k i}, D.window k) \ D.window i = ∅ := by
      ext x
      simp only [DelayListRun.window, Set.mem_sdiff, Set.mem_Ioo, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨⟨⟨h1, h2⟩, _⟩, h3⟩
      exact h3 ⟨lt_of_le_of_lt hτq h1, h2⟩
    rw [this]; simp
  · push Not at hτq
    have hch : D.charge i = β * I.p i := by
      rcases hD.2.2.1 i with ⟨_, _, hτ⟩ | ⟨_, _, _, _, _, _, hch⟩
      · rw [hτ] at hτq; exact absurd hτq (lt_irrefl _)
      · exact hch
    set T := Set.Ioo (D.q i) (D.S i) \ ⋃ k ∈ {k | D.Before k i}, D.window k with hT
    have hTsub : T ⊆ Set.Icc (D.q i) (D.S i) := fun x hx => ⟨hx.1.1.le, hx.1.2.le⟩
    have hsplit := integral_inter_add_sdiff (μ := volume) (f := D.idle) (s := T)
      (t := D.window i) measurableSet_Ioo (hint _ _ _ hTsub)
    have hinter : T ∩ D.window i = D.chargedSet i := by
      ext x
      simp only [hT, DelayListRun.chargedSet, DelayListRun.window, Set.mem_inter_iff,
        Set.mem_sdiff, Set.mem_Ioo]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩
        exact ⟨⟨⟨lt_trans hτq h3.1, h3.2⟩, h2⟩, h3⟩
    rw [hinter] at hsplit
    have hch' : ∫ t in D.chargedSet i, D.idle t = β * I.p i := hch
    rw [hch'] at hsplit
    have hgc := aux_cl_gc hβ D hD i
    refine le_antisymm ?_ (integral_nonneg fun t => hnn t)
    have : ∫ t in T, D.idle t ≤ β * I.p i := hgc
    linarith

theorem aux_nui_union (D : DelayListRun I m) (i : Fin n) :
    Set.Ioo (D.q i) (D.S i) \ ⋃ k ∈ {k | D.Before k i ∨ k = i}, D.window k =
      (Set.Ioo (D.q i) (D.S i) \ ⋃ k ∈ {k | D.Before k i}, D.window k) \ D.window i := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun ⟨k, hk, hx⟩ => h2 ⟨k, Or.inl hk, hx⟩⟩, fun hx => h2 ⟨i, Or.inr rfl, hx⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, ?_⟩
    rintro ⟨k, hk | rfl, hx⟩
    · exact h2 ⟨k, hk, hx⟩
    · exact h3 hx

theorem aux_nui_b {π : Fin n ≃ Fin n} {β : ℝ} (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i : Fin n) (k : Fin n) (hk : π.symm i < π.symm k) :
    (∫ t in D.chargedSet k ∩ Set.Ioo (D.q i) (D.S i), D.idle t) = 0 := by
  have hnn := aux_cl_idle_nonneg D hD.2.1
  have hint := aux_cl_intOn D hD.2.1
  have hki : k ≠ i := fun h => by rw [h] at hk; exact lt_irrefl _ hk
  by_cases hb : D.Before k i
  · have hlt : D.S k < D.q i := by
      rcases hD.2.2.1 k with ⟨h1, _, _⟩ | ⟨_, _, h3, _⟩
      · have hni : ¬ D.Before i k := fun h => lt_asymm h hb
        exact absurd (h1 i hni) (not_le.mpr hk)
      · by_contra hle
        push Not at hle
        have hni : ¬ D.Before i k := fun h => lt_asymm h hb
        exact absurd (h3 i hni (aux_cl_ready_of D hle)) (not_le.mpr hk)
    have : D.chargedSet k ∩ Set.Ioo (D.q i) (D.S i) = ∅ := by
      ext x
      simp only [DelayListRun.chargedSet, DelayListRun.window, Set.mem_inter_iff, Set.mem_sdiff,
        Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨⟨_, h2⟩, _⟩, h3, _⟩
      linarith
    rw [this]; simp
  · have hik := aux_nui_before_total D hb hki
    have hsub : D.chargedSet k ∩ Set.Ioo (D.q i) (D.S i) ⊆
        (Set.Ioo (D.q i) (D.S i) \ ⋃ k ∈ {k | D.Before k i}, D.window k) \ D.window i := by
      intro x hx
      simp only [DelayListRun.chargedSet, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_iUnion,
        Set.mem_setOf_eq, exists_prop] at hx ⊢
      obtain ⟨⟨_, hx2⟩, hx3⟩ := hx
      refine ⟨⟨hx3, fun ⟨k', hk', hx'⟩ => hx2 ⟨k', lt_trans hk' hik, hx'⟩⟩,
        fun hx' => hx2 ⟨i, hik, hx'⟩⟩
    refine le_antisymm ?_ (integral_nonneg fun t => hnn t)
    rw [← aux_nui_zero hβ D hD i]
    refine setIntegral_mono_set (hint _ (D.q i) (D.S i) ?_)
      (Filter.Eventually.of_forall fun t => hnn t) (Filter.Eventually.of_forall hsub)
    intro x hx; exact ⟨hx.1.1.1.le, hx.1.1.2.le⟩

theorem nui_core {π : Fin n ≃ Fin n} (β : ℝ) (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i : Fin n) :
    (∫ t in Set.Ioo (D.q i) (D.S i) \ ⋃ k ∈ {k | D.Before k i ∨ k = i}, D.window k,
        D.idle t) = 0 ∧
    ∀ k ∈ listA π i, (∫ t in D.chargedSet k ∩ Set.Ioo (D.q i) (D.S i), D.idle t) = 0 := by
  refine ⟨?_, fun k hk => aux_nui_b hβ D hD i k ?_⟩
  · rw [aux_nui_union]; exact aux_nui_zero hβ D hD i
  · simpa [listA] using hk

end

end AvgCompletionSched.DelayList

open AvgCompletionSched.DelayList
open MeasureTheory

theorem solution {n m : ℕ} (I : Instance n) (hm : 2 ≤ m) (π : Fin n ≃ Fin n)
    (hπ : ObeysPrecedence I π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i : Fin n) :
    (∫ t in Set.Ioo (D.q i) (D.S i) \ ⋃ k ∈ {k | D.Before k i ∨ k = i}, D.window k,
        D.idle t) = 0 ∧
    ∀ k ∈ listA π i, (∫ t in D.chargedSet k ∩ Set.Ioo (D.q i) (D.S i), D.idle t) = 0 := by
  exact nui_core β hβ D hD i
