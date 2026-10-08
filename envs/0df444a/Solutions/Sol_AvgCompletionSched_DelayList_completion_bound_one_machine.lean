-- Prove2me | solution 1 for AvgCompletionSched.DelayList.completion_bound_one_machine
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T12:33:40.045979+00:00
-- url     : https://prove2.me/submissions/6b97d028-708d-4e5f-a3a1-5fd478eea78d

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


section
variable {n m : ℕ} {I : Instance n}

theorem aux_icb_cs_meas (D : DelayListRun I m) (k : Fin n) : MeasurableSet (D.chargedSet k) :=
  measurableSet_Ioo.diff (MeasurableSet.biUnion (Set.to_countable _) fun _ _ => measurableSet_Ioo)

theorem aux_icb_cs_sub (D : DelayListRun I m) (k : Fin n) :
    D.chargedSet k ⊆ Set.Icc (D.τ k) (D.S k) := fun x hx => ⟨hx.1.1.le, hx.1.2.le⟩

theorem aux_icb_mono (D : DelayListRun I m)
    (hB : ∀ j k, D.Before k j → D.M k = D.M j → D.S k + I.p k ≤ D.S j)
    (A : Finset (Fin n)) {T T' : Set ℝ} (h : T ⊆ T') :
    D.chargedToIn A T ≤ D.chargedToIn A T' := by
  unfold DelayListRun.chargedToIn
  refine Finset.sum_le_sum fun k _ => ?_
  refine setIntegral_mono_set
    (aux_cl_intOn D hB _ _ _ (Set.inter_subset_left.trans (aux_icb_cs_sub D k)))
    (Filter.Eventually.of_forall fun t => aux_cl_idle_nonneg D hB t)
    (Filter.Eventually.of_forall fun x hx => ⟨hx.1, h hx.2⟩)

theorem aux_icb_nonneg (D : DelayListRun I m)
    (hB : ∀ j k, D.Before k j → D.M k = D.M j → D.S k + I.p k ≤ D.S j)
    (A : Finset (Fin n)) (T : Set ℝ) : 0 ≤ D.chargedToIn A T :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun t => aux_cl_idle_nonneg D hB t

theorem aux_icb_union (D : DelayListRun I m)
    (hB : ∀ j k, D.Before k j → D.M k = D.M j → D.S k + I.p k ≤ D.S j)
    (A : Finset (Fin n)) {T T' : Set ℝ} (hT : MeasurableSet T) (hT' : MeasurableSet T') :
    D.chargedToIn A (T ∪ T') ≤ D.chargedToIn A T + D.chargedToIn A T' := by
  unfold DelayListRun.chargedToIn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have hint : ∀ X, IntegrableOn D.idle (D.chargedSet k ∩ X) := fun X =>
    aux_cl_intOn D hB _ _ _ (Set.inter_subset_left.trans (aux_icb_cs_sub D k))
  have heq : D.chargedSet k ∩ (T ∪ T') =
      (D.chargedSet k ∩ T) ∪ ((D.chargedSet k ∩ T') \ (D.chargedSet k ∩ T)) := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff]; tauto
  rw [heq, setIntegral_union Set.disjoint_sdiff_right
    (((aux_icb_cs_meas D k).inter hT').diff ((aux_icb_cs_meas D k).inter hT)) (hint T)
    ((hint T').mono_set Set.sdiff_subset)]
  have : ∫ t in (D.chargedSet k ∩ T') \ (D.chargedSet k ∩ T), D.idle t ≤
      ∫ t in D.chargedSet k ∩ T', D.idle t :=
    setIntegral_mono_set (hint T')
      (Filter.Eventually.of_forall fun t => aux_cl_idle_nonneg D hB t)
      (Filter.Eventually.of_forall Set.sdiff_subset)
  linarith

theorem aux_icb_bound (D : DelayListRun I m)
    (hB : ∀ j k, D.Before k j → D.M k = D.M j → D.S k + I.p k ≤ D.S j)
    (A : Finset (Fin n)) (T : Set ℝ) (hT : MeasurableSet T) (a b : ℝ) (hTab : T ⊆ Set.Icc a b) :
    D.chargedToIn A T ≤ (m : ℝ) * volume.real T := by
  unfold DelayListRun.chargedToIn
  have hnn := aux_cl_idle_nonneg D hB
  rw [← integral_biUnion_finset A (fun k _ => (aux_icb_cs_meas D k).inter hT) ?_
    (fun k _ => aux_cl_intOn D hB _ _ _ (Set.inter_subset_left.trans (aux_icb_cs_sub D k)))]
  · have hfin : volume T < ⊤ := lt_of_le_of_lt (measure_mono hTab) (by simp)
    calc ∫ x in ⋃ k ∈ A, D.chargedSet k ∩ T, D.idle x ≤ ∫ x in T, D.idle x := by
          refine setIntegral_mono_set (aux_cl_intOn D hB _ _ _ hTab)
            (Filter.Eventually.of_forall fun t => hnn t) (Filter.Eventually.of_forall ?_)
          intro x hx
          obtain ⟨k, _, hx⟩ := Set.mem_iUnion₂.mp hx
          exact hx.2
      _ ≤ ‖∫ x in T, D.idle x‖ := Real.le_norm_self _
      _ ≤ (m : ℝ) * volume.real T := by
          apply norm_setIntegral_le_of_norm_le_const hfin
          intro x _
          rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
          exact aux_cl_idle_le D x
  · intro k _ k' _ hne
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro x hx hx'
    rcases lt_trichotomy (D.ev.symm k) (D.ev.symm k') with h | h | h
    · exact hx'.1.2 (Set.mem_biUnion (show D.Before k k' from h) hx.1.1)
    · exact hne (D.ev.symm.injective h)
    · exact hx.1.2 (Set.mem_biUnion (show D.Before k' k from h) hx'.1.1)

theorem aux_icb_step_q (D : DelayListRun I m) {a b : Fin n} (h : D.PathStep a b) :
    D.q b ≤ D.C a := by
  obtain ⟨hab, hr, hmax⟩ := h
  unfold DelayListRun.q
  split_ifs with hne
  · refine max_le (Finset.sup'_le _ _ fun c hc => ?_) hr
    have hc' : I.prec c b := by simpa [Instance.preds] using hc
    by_cases hrc : I.r b ≤ D.C c
    · exact hmax c hc' hrc
    · push Not at hrc; linarith
  · exact hr

theorem aux_icb_first_q (D : DelayListRun I m) {j : Fin n} (h : ∀ c, I.prec c j → D.C c < I.r j) :
    D.q j ≤ I.r j := by
  unfold DelayListRun.q
  split_ifs with hne
  · exact max_le (Finset.sup'_le _ _ fun c hc => (h c (by simpa [Instance.preds] using hc)).le)
      le_rfl
  · exact le_rfl

theorem aux_icb_chain_pi {π : Fin n ≃ Fin n} (hπ : ObeysPrecedence I π) (D : DelayListRun I m) :
    ∀ (l : List (Fin n)) (a : Fin n), List.IsChain D.PathStep (a :: l) →
      ∀ j ∈ a :: l, π.symm j ≤ π.symm ((a :: l).getLast (List.cons_ne_nil _ _)) := by
  intro l
  induction l with
  | nil => intro a _ j hj; simp at hj; subst hj; simp
  | cons c l ih =>
    intro a h j hj
    rw [List.isChain_cons_cons] at h
    obtain ⟨hac, hrest⟩ := h
    rw [List.getLast_cons_cons]
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact (hπ _ _ hac.1).le.trans (ih c hrest c List.mem_cons_self)
    · exact ih c hrest j hj'

theorem aux_icb_chain {π : Fin n ≃ Fin n} {β : ℝ} (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (A : Finset (Fin n)) :
    ∀ (l : List (Fin n)) (a : Fin n), List.IsChain D.PathStep (a :: l) →
      (∀ j ∈ a :: l, ∀ k ∈ A, π.symm j < π.symm k) →
      D.chargedToIn A (Set.Ioo (D.q a) (D.S ((a :: l).getLast (List.cons_ne_nil _ _)))) ≤
        (m : ℝ) * (((a :: l).map I.p).sum - I.p ((a :: l).getLast (List.cons_ne_nil _ _))) := by
  have hB := hD.2.1
  have hzero : ∀ a, (∀ k ∈ A, π.symm a < π.symm k) →
      D.chargedToIn A (Set.Ioo (D.q a) (D.S a)) = 0 := by
    intro a ha
    unfold DelayListRun.chargedToIn
    exact Finset.sum_eq_zero fun k hk => aux_nui_b hβ D hD a k (ha k hk)
  intro l
  induction l with
  | nil =>
    intro a _ hA
    simp only [List.getLast_singleton, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, sub_self, mul_zero]
    exact (hzero a (hA a List.mem_cons_self)).le
  | cons c l ih =>
    intro a h hA
    rw [List.isChain_cons_cons] at h
    obtain ⟨hac, hrest⟩ := h
    rw [List.getLast_cons_cons]
    set b := (c :: l).getLast (List.cons_ne_nil _ _) with hb
    have IH := ih c hrest (fun j hj => hA j (List.mem_cons_of_mem _ hj))
    have hq := aux_icb_step_q D hac
    have hsub : Set.Ioo (D.q a) (D.S b) ⊆
        Set.Ioo (D.q a) (D.S a) ∪ (Set.Icc (D.S a) (D.C a) ∪ Set.Ioo (D.q c) (D.S b)) := by
      intro x hx
      by_cases h1 : x < D.S a
      · exact Or.inl ⟨hx.1, h1⟩
      · by_cases h2 : x ≤ D.C a
        · exact Or.inr (Or.inl ⟨not_lt.mp h1, h2⟩)
        · exact Or.inr (Or.inr ⟨lt_of_le_of_lt hq (not_le.mp h2), hx.2⟩)
    have h1 := aux_icb_mono D hB A hsub
    have h2 := aux_icb_union D hB A (T := Set.Ioo (D.q a) (D.S a))
      (T' := Set.Icc (D.S a) (D.C a) ∪ Set.Ioo (D.q c) (D.S b)) measurableSet_Ioo
      (measurableSet_Icc.union measurableSet_Ioo)
    have h3 := aux_icb_union D hB A (T := Set.Icc (D.S a) (D.C a)) measurableSet_Icc
      measurableSet_Ioo (T' := Set.Ioo (D.q c) (D.S b))
    have h4 := aux_icb_bound D hB A _ measurableSet_Icc (D.S a) (D.C a) le_rfl
    have hCa : D.C a = D.S a + I.p a := rfl
    rw [Real.volume_real_Icc_of_le (by rw [hCa]; linarith [I.p_pos a])] at h4
    rw [hzero a (hA a List.mem_cons_self)] at h2
    simp only [List.map_cons, List.sum_cons] at IH ⊢
    have : D.C a - D.S a = I.p a := by rw [hCa]; ring
    rw [this] at h4
    nlinarith

theorem aux_icb_case2 {π : Fin n ≃ Fin n} {β : ℝ} (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i k : Fin n) (hb : D.Before k i)
    (hk : π.symm i < π.symm k) : 0 ≤ D.τ k ∧ D.charge k = β * I.p k := by
  rcases hD.2.2.1 k with ⟨h1, _, _⟩ | ⟨_, _, _, _, h5, _, h7⟩
  · have hni : ¬ D.Before i k := fun h => lt_asymm h hb
    exact absurd (h1 i hni) (not_le.mpr hk)
  · exact ⟨h5, h7⟩

theorem icb_core {π : Fin n ≃ Fin n} (hπ : ObeysPrecedence I π) (β : ℝ) (hβ : 0 < β)
    (D : DelayListRun I m) (hD : IsDelayListSchedule I m π β D) (i j₁ : Fin n)
    (l : List (Fin n)) (hP : D.IsPathPrime i j₁ l) :
    D.chargedToIn (listA π i) (Set.Ioo 0 (D.S i)) ≤ (m : ℝ) * (kappaPrime I j₁ l - I.p i) ∧
    psum I (D.outOfOrder π i) ≤ (m : ℝ) * (kappaPrime I j₁ l - I.p i) / β ∧
    (m : ℝ) * (kappaPrime I j₁ l - I.p i) / β ≤ (m : ℝ) * (kappa I i - I.p i) / β := by
  have hB := hD.2.1
  obtain ⟨hlast, hchain, hfirst⟩ := hP
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have H1 : D.chargedToIn (listA π i) (Set.Ioo 0 (D.S i)) ≤
      (m : ℝ) * (kappaPrime I j₁ l - I.p i) := by
    have hpi := aux_icb_chain_pi hπ D l j₁ hchain
    rw [hlast] at hpi
    have hch := aux_icb_chain hβ D hD (listA π i) l j₁ hchain (fun j hj k hk => by
      have : π.symm i < π.symm k := by simpa [listA] using hk
      exact lt_of_le_of_lt (hpi j hj) this)
    rw [hlast] at hch
    have hq1 := aux_icb_first_q D hfirst
    have hq0 : 0 ≤ D.q j₁ := (I.r_nonneg j₁).trans (aux_cl_r_le_q D j₁)
    have hsub : Set.Ioo 0 (D.S i) ⊆ Set.Ioc 0 (D.q j₁) ∪ Set.Ioo (D.q j₁) (D.S i) := by
      intro x hx
      by_cases h : x ≤ D.q j₁
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨not_le.mp h, hx.2⟩
    have h1 := aux_icb_mono D hB (listA π i) hsub
    have h2 := aux_icb_union D hB (listA π i) (T := Set.Ioc 0 (D.q j₁)) measurableSet_Ioc
      (measurableSet_Ioo (a := D.q j₁) (b := D.S i))
    have h3 := aux_icb_bound D hB (listA π i) _ measurableSet_Ioc 0 (D.q j₁)
      Set.Ioc_subset_Icc_self
    rw [Real.volume_real_Ioc_of_le hq0, sub_zero] at h3
    unfold kappaPrime
    nlinarith
  refine ⟨H1, ?_, ?_⟩
  · rw [le_div_iff₀ hβ]
    refine le_trans ?_ H1
    unfold psum DelayListRun.chargedToIn
    rw [Finset.sum_mul]
    have hsubO : D.outOfOrder π i ⊆ listA π i := by
      classical
      unfold DelayListRun.outOfOrder; convert Finset.filter_subset _ _
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsubO
      fun k _ _ => integral_nonneg fun t => aux_cl_idle_nonneg D hB t)
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' : π.symm i < π.symm k ∧ D.Before k i := by
      simpa [DelayListRun.outOfOrder, listA] using hk
    obtain ⟨hτ, hch⟩ := aux_icb_case2 D hD i k hk'.2 hk'.1
    have hSk := hD.1 i k hk'.2
    have heq : D.chargedSet k ∩ Set.Ioo 0 (D.S i) = D.chargedSet k := by
      refine Set.inter_eq_left.mpr fun x hx => ⟨lt_of_le_of_lt hτ hx.1.1, lt_of_lt_of_le hx.1.2 hSk⟩
    rw [heq]
    have : D.charge k = ∫ t in D.chargedSet k, D.idle t := rfl
    rw [← this, hch, mul_comm]
  · have h1 := aux_kpl_chain I D l j₁ hchain
    rw [hlast] at h1
    have h2 := aux_kpl_ge I j₁
    have hk : kappaPrime I j₁ l ≤ kappa I i := by
      unfold kappaPrime
      simp only [List.map_cons, List.sum_cons]
      linarith
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hm0) hβ.le

end


section
variable {n m : ℕ} {I : Instance n}

theorem aux_cb_intfin (D : DelayListRun I m)
    (hB : ∀ j k, D.Before k j → D.M k = D.M j → D.S k + I.p k ≤ D.S j)
    (S : Set ℝ) (hS : volume S ≠ ⊤) : IntegrableOn D.idle S := by
  refine Measure.integrableOn_of_bounded (M := m) hS (aux_cl_idle_meas D).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (aux_cl_idle_nonneg D hB x)]
  exact aux_cl_idle_le D x

theorem aux_cb_sub_union (D : DelayListRun I m)
    (hB : ∀ j k, D.Before k j → D.M k = D.M j → D.S k + I.p k ≤ D.S j)
    {S S1 S2 : Set ℝ} (h1 : MeasurableSet S1) (h2 : MeasurableSet S2)
    (f1 : volume S1 ≠ ⊤) (f2 : volume S2 ≠ ⊤) (h : S ⊆ S1 ∪ S2) :
    ∫ t in S, D.idle t ≤ (∫ t in S1, D.idle t) + ∫ t in S2, D.idle t := by
  have hnn := aux_cl_idle_nonneg D hB
  have fu : volume (S1 ∪ S2) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨f1, f2⟩) (measure_union_le _ _)
  calc ∫ t in S, D.idle t ≤ ∫ t in S1 ∪ S2, D.idle t :=
        setIntegral_mono_set (aux_cb_intfin D hB _ fu)
          (Filter.Eventually.of_forall fun t => hnn t) (Filter.Eventually.of_forall h)
    _ = ∫ t in S1 ∪ (S2 \ S1), D.idle t := by
        rw [show S1 ∪ S2 \ S1 = S1 ∪ S2 from by
          ext x; simp only [Set.mem_union, Set.mem_sdiff]; tauto]
    _ = (∫ t in S1, D.idle t) + ∫ t in S2 \ S1, D.idle t :=
        setIntegral_union Set.disjoint_sdiff_right (h2.diff h1) (aux_cb_intfin D hB _ f1)
          ((aux_cb_intfin D hB _ f2).mono_set Set.sdiff_subset)
    _ ≤ (∫ t in S1, D.idle t) + ∫ t in S2, D.idle t := by
        have : ∫ t in S2 \ S1, D.idle t ≤ ∫ t in S2, D.idle t :=
          setIntegral_mono_set (aux_cb_intfin D hB _ f2)
            (Filter.Eventually.of_forall fun t => hnn t)
            (Filter.Eventually.of_forall Set.sdiff_subset)
        linarith

theorem aux_cb_super (D : DelayListRun I m)
    (hB : ∀ j k, D.Before k j → D.M k = D.M j → D.S k + I.p k ≤ D.S j)
    (A : Finset (Fin n)) {T T' Y : Set ℝ} (hT' : MeasurableSet T') (hd : Disjoint T T')
    (hsub : T ∪ T' ⊆ Y) :
    D.chargedToIn A T + D.chargedToIn A T' ≤ D.chargedToIn A Y := by
  unfold DelayListRun.chargedToIn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have hint : ∀ X, IntegrableOn D.idle (D.chargedSet k ∩ X) := fun X =>
    aux_cl_intOn D hB _ _ _ (Set.inter_subset_left.trans (aux_icb_cs_sub D k))
  rw [← setIntegral_union (hd.mono Set.inter_subset_right Set.inter_subset_right)
    ((aux_icb_cs_meas D k).inter hT') (hint T) (hint T')]
  refine setIntegral_mono_set (hint Y)
    (Filter.Eventually.of_forall fun t => aux_cl_idle_nonneg D hB t)
    (Filter.Eventually.of_forall ?_)
  rintro x (hx | hx)
  · exact ⟨hx.1, hsub (Or.inl hx.2)⟩
  · exact ⟨hx.1, hsub (Or.inr hx.2)⟩

theorem aux_cb_cov (D : DelayListRun I m) {x : ℝ} {k : Fin n} (hx : x ∈ D.window k) :
    ∃ k', x ∈ D.chargedSet k' := by
  classical
  obtain ⟨k', hk', hmin⟩ := (Finset.univ.filter fun k => x ∈ D.window k).exists_min_image
    (fun k => D.ev.symm k) ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  refine ⟨k', (Finset.mem_filter.mp hk').2, ?_⟩
  intro h
  obtain ⟨k'', hk'', hx''⟩ := Set.mem_iUnion₂.mp h
  have := hmin k'' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx''⟩)
  exact absurd hk'' (not_lt.mpr this)

/-- Idle time in `(q_j, s_j)` is charged to jobs of `B_i`. -/
theorem aux_cb_Z {π : Fin n ≃ Fin n} {β : ℝ} (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i j : Fin n) (hji : π.symm j ≤ π.symm i) :
    ∫ t in Set.Ioo (D.q j) (D.S j), D.idle t ≤
      D.chargedToIn (listB π i) (Set.Ioo (D.q j) (D.S j)) := by
  classical
  have hB := hD.2.1
  have hnn := aux_cl_idle_nonneg D hB
  set T := Set.Ioo (D.q j) (D.S j) with hT
  set N := (T \ ⋃ k ∈ {k | D.Before k j}, D.window k) \ D.window j with hN
  set U := ⋃ k ∈ (Finset.univ : Finset (Fin n)), D.chargedSet k ∩ T with hU
  have hTfin : volume T ≠ ⊤ := by simp [hT]
  have hNm : MeasurableSet N := (measurableSet_Ioo.diff
    (MeasurableSet.biUnion (Set.to_countable _) fun _ _ => measurableSet_Ioo)).diff measurableSet_Ioo
  have hUm : MeasurableSet U :=
    Finset.measurableSet_biUnion _ fun k _ => (aux_icb_cs_meas D k).inter measurableSet_Ioo
  have hcov : T ⊆ N ∪ U := by
    intro x hx
    by_cases hw : x ∈ D.window j ∨ x ∈ ⋃ k ∈ {k | D.Before k j}, D.window k
    · right
      rcases hw with hw | hw
      · obtain ⟨k', hk'⟩ := aux_cb_cov D hw
        exact Set.mem_iUnion₂.mpr ⟨k', Finset.mem_univ _, hk', hx⟩
      · obtain ⟨k, _, hk⟩ := Set.mem_iUnion₂.mp hw
        obtain ⟨k', hk'⟩ := aux_cb_cov D hk
        exact Set.mem_iUnion₂.mpr ⟨k', Finset.mem_univ _, hk', hx⟩
    · push Not at hw
      exact Or.inl ⟨⟨hx, hw.2⟩, hw.1⟩
  have h1 := aux_cb_sub_union D hB hNm hUm
    (ne_top_of_le_ne_top hTfin (measure_mono (Set.sdiff_subset.trans Set.sdiff_subset)))
    (ne_top_of_le_ne_top hTfin (measure_mono (Set.iUnion₂_subset fun k _ => Set.inter_subset_right)))
    hcov
  have h2 : ∫ t in N, D.idle t = 0 := aux_nui_zero hβ D hD j
  have h3 : ∫ t in U, D.idle t = D.chargedToIn Finset.univ T := by
    unfold DelayListRun.chargedToIn
    rw [hU, integral_biUnion_finset _ (fun k _ => (aux_icb_cs_meas D k).inter measurableSet_Ioo)]
    · intro k _ k' _ hne
      simp only [Function.onFun]
      rw [Set.disjoint_left]
      intro x hx hx'
      rcases lt_trichotomy (D.ev.symm k) (D.ev.symm k') with h | h | h
      · exact hx'.1.2 (Set.mem_biUnion (show D.Before k k' from h) hx.1.1)
      · exact hne (D.ev.symm.injective h)
      · exact hx.1.2 (Set.mem_biUnion (show D.Before k' k from h) hx'.1.1)
    · exact fun k _ => aux_cl_intOn D hB _ _ _ (Set.inter_subset_left.trans (aux_icb_cs_sub D k))
  have h4 : D.chargedToIn Finset.univ T ≤ D.chargedToIn (listB π i) T := by
    unfold DelayListRun.chargedToIn
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => π.symm k ≤ π.symm j)]
    have hz : ∑ k ∈ Finset.univ.filter (fun k => ¬ π.symm k ≤ π.symm j),
        ∫ t in D.chargedSet k ∩ T, D.idle t = 0 :=
      Finset.sum_eq_zero fun k hk => aux_nui_b hβ D hD j k
        (not_le.mp (Finset.mem_filter.mp hk).2)
    rw [hz, add_zero]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun k _ _ => integral_nonneg fun t => hnn t)
    intro k hk
    have := (Finset.mem_filter.mp hk).2
    simp only [listB, Finset.mem_filter, Finset.mem_univ, true_and]
    exact this.trans hji
  linarith

theorem aux_cb_ready_start {π : Fin n ≃ Fin n} {β : ℝ} (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (j : Fin n) : D.Ready (D.S j) j := by
  rcases hD.2.2.1 j with h | h
  · exact h.2.1
  · exact h.2.1

theorem aux_cb_chain_S {π : Fin n ≃ Fin n} {β : ℝ} (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) :
    ∀ (l : List (Fin n)) (a : Fin n), List.IsChain D.PathStep (a :: l) →
      D.S a ≤ D.S ((a :: l).getLast (List.cons_ne_nil _ _)) := by
  intro l
  induction l with
  | nil => intro a _; simp
  | cons c l ih =>
    intro a h
    rw [List.isChain_cons_cons] at h
    obtain ⟨hac, hrest⟩ := h
    rw [List.getLast_cons_cons]
    have h1 := ih c hrest
    have h2 := (aux_cb_ready_start D hD c).2 a hac.1
    have h3 : D.C a = D.S a + I.p a := rfl
    linarith [I.p_pos a]

theorem aux_cb_chain {π : Fin n ≃ Fin n} {β : ℝ} (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i : Fin n) :
    ∀ (l : List (Fin n)) (a : Fin n), List.IsChain D.PathStep (a :: l) →
      (∀ j ∈ a :: l, π.symm j ≤ π.symm i) →
      ∫ t in Set.Ioo (D.q a) (D.S ((a :: l).getLast (List.cons_ne_nil _ _))), D.idle t ≤
        (m : ℝ) * (((a :: l).map I.p).sum - I.p ((a :: l).getLast (List.cons_ne_nil _ _))) +
        D.chargedToIn (listB π i)
          (Set.Ioo (D.q a) (D.S ((a :: l).getLast (List.cons_ne_nil _ _)))) := by
  have hB := hD.2.1
  have hnn := aux_cl_idle_nonneg D hB
  intro l
  induction l with
  | nil =>
    intro a _ hA
    simp only [List.getLast_singleton, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, sub_self, mul_zero, zero_add]
    exact aux_cb_Z hβ D hD i a (hA a List.mem_cons_self)
  | cons c l ih =>
    intro a h hA
    rw [List.isChain_cons_cons] at h
    obtain ⟨hac, hrest⟩ := h
    rw [List.getLast_cons_cons]
    set b := (c :: l).getLast (List.cons_ne_nil _ _) with hb
    have IH := ih c hrest (fun j hj => hA j (List.mem_cons_of_mem _ hj))
    have hq := aux_icb_step_q D hac
    have hCa : D.C a = D.S a + I.p a := rfl
    have hpa := I.p_pos a
    have hCq : D.C a ≤ D.q c := by
      have hr : D.Ready (D.q c) c := aux_cl_ready_of D le_rfl
      exact hr.2 a hac.1
    have hsub : Set.Ioo (D.q a) (D.S b) ⊆
        Set.Ioo (D.q a) (D.S a) ∪ (Set.Icc (D.S a) (D.C a) ∪ Set.Ioo (D.q c) (D.S b)) := by
      intro x hx
      by_cases h1 : x < D.S a
      · exact Or.inl ⟨hx.1, h1⟩
      · by_cases h2 : x ≤ D.C a
        · exact Or.inr (Or.inl ⟨not_lt.mp h1, h2⟩)
        · exact Or.inr (Or.inr ⟨lt_of_le_of_lt hq (not_le.mp h2), hx.2⟩)
    have e1 := aux_cb_sub_union D hB measurableSet_Ioo (measurableSet_Icc.union measurableSet_Ioo)
      (by simp) (ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨by simp, by simp⟩)
        (measure_union_le (Set.Icc (D.S a) (D.C a)) (Set.Ioo (D.q c) (D.S b)))) hsub
    have e2 := aux_cb_sub_union D hB measurableSet_Icc measurableSet_Ioo (by simp) (by simp)
      (le_refl (Set.Icc (D.S a) (D.C a) ∪ Set.Ioo (D.q c) (D.S b)))
    have e3 : ∫ t in Set.Icc (D.S a) (D.C a), D.idle t ≤ (m : ℝ) * I.p a := by
      calc ∫ t in Set.Icc (D.S a) (D.C a), D.idle t ≤ ‖∫ t in Set.Icc (D.S a) (D.C a), D.idle t‖ :=
            Real.le_norm_self _
        _ ≤ (m : ℝ) * volume.real (Set.Icc (D.S a) (D.C a)) := by
            apply norm_setIntegral_le_of_norm_le_const (by simp)
            intro x _
            rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
            exact aux_cl_idle_le D x
        _ = (m : ℝ) * I.p a := by
            rw [Real.volume_real_Icc_of_le (by linarith), hCa]; ring
    have hSab : D.S a ≤ D.S b := by
      have h1 := aux_cb_chain_S D hD l c hrest
      have h2 := aux_cl_q_le D (aux_cb_ready_start D hD c)
      rw [← hb] at h1
      linarith
    have hqac : D.q a ≤ D.q c := by
      have := aux_cl_q_le D (aux_cb_ready_start D hD a)
      linarith
    have e4 := aux_cb_Z hβ D hD i a (hA a List.mem_cons_self)
    have e5 := aux_cb_super D hB (listB π i) (T := Set.Ioo (D.q a) (D.S a))
      (T' := Set.Ioo (D.q c) (D.S b)) (Y := Set.Ioo (D.q a) (D.S b)) measurableSet_Ioo
      (by
        rw [Set.disjoint_left]
        intro x hx hx'
        linarith [hx.2, hx'.1])
      (by
        rintro x (hx | hx)
        · exact ⟨hx.1, lt_of_lt_of_le hx.2 hSab⟩
        · exact ⟨lt_of_le_of_lt hqac hx.1, hx.2⟩)
    simp only [List.map_cons, List.sum_cons] at IH ⊢
    linarith

end


section
variable {n m : ℕ} {I : Instance n}

theorem aux_cb_idle_eq (D : DelayListRun I m) : D.idle = fun t => (m : ℝ) -
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

theorem aux_cb_charge_le {π : Fin n ≃ Fin n} {β : ℝ} (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i : Fin n) : D.charge i ≤ β * I.p i := by
  rcases hD.2.2.1 i with ⟨_, _, hτ⟩ | ⟨_, _, _, _, _, _, hch⟩
  · unfold DelayListRun.charge DelayListRun.chargedSet
    rw [show D.window i = Set.Ioo (D.q i) (D.S i) by simp [DelayListRun.window, hτ]]
    exact aux_cl_gc hβ D hD i
  · rw [hch]

theorem aux_cb_busy {π : Fin n ≃ Fin n} {β : ℝ} (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i : Fin n) (hS0 : 0 ≤ D.S i) :
    (m : ℝ) * D.S i - ∫ t in Set.Ioo 0 (D.S i), D.idle t ≤
      psum I (listB π i) - I.p i + psum I (D.outOfOrder π i) := by
  classical
  set X := Set.Ioo 0 (D.S i) with hX
  have hXf : volume X ≠ ⊤ := by simp [hX]
  have hint_ind : ∀ k, IntegrableOn
      ((Set.Ico (D.S k) (D.S k + I.p k)).indicator (fun _ => (1 : ℝ))) X := by
    intro k
    exact (integrableOn_const hXf).indicator measurableSet_Ico
  have hval : ∫ t in X, D.idle t = (m : ℝ) * D.S i -
      ∑ k, volume.real (X ∩ Set.Ico (D.S k) (D.S k + I.p k)) := by
    rw [aux_cb_idle_eq D, integral_sub (show Integrable (fun _ : ℝ => (m : ℝ)) (volume.restrict X)
      from integrableOn_const (C := (m : ℝ)) hXf)
      (integrable_finsetSum _ fun k _ => hint_ind k), integral_finset_sum _ fun k _ => hint_ind k]
    congr 1
    · rw [setIntegral_const, smul_eq_mul, hX, Real.volume_real_Ioo_of_le hS0, sub_zero, mul_comm]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [setIntegral_indicator measurableSet_Ico, setIntegral_const, smul_eq_mul, mul_one]
  rw [hval]
  have hk : ∀ k, volume.real (X ∩ Set.Ico (D.S k) (D.S k + I.p k)) ≤
      if D.Before k i then I.p k else 0 := by
    intro k
    split_ifs with hb
    · calc volume.real (X ∩ Set.Ico (D.S k) (D.S k + I.p k))
            ≤ volume.real (Set.Ico (D.S k) (D.S k + I.p k)) :=
              measureReal_mono Set.inter_subset_right (by simp)
        _ = I.p k := by rw [Real.volume_real_Ico_of_le (by linarith [I.p_pos k])]; ring
    · have hle : D.S i ≤ D.S k := by
        by_cases hki : k = i
        · rw [hki]
        · exact hD.1 k i (aux_nui_before_total D hb hki)
      have : X ∩ Set.Ico (D.S k) (D.S k + I.p k) = ∅ := by
        ext x
        simp only [hX, Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ico, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨⟨_, h1⟩, h2, _⟩
        linarith
      rw [this]; simp
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hk k
  rw [← Finset.sum_filter] at hsum
  have hsub : Finset.univ.filter (fun k => D.Before k i) ⊆
      (listB π i).erase i ∪ D.outOfOrder π i := by
    intro k hk'
    have hb := (Finset.mem_filter.mp hk').2
    have hki : k ≠ i := fun h => by rw [h] at hb; exact lt_irrefl _ hb
    rcases le_or_gt (π.symm k) (π.symm i) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hki, by simp [listB, h]⟩)
    · apply Finset.mem_union_right
      unfold DelayListRun.outOfOrder
      simp only [listA, Finset.mem_filter, Finset.mem_univ, true_and]
      convert And.intro h hb
  have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := I.p) (fun k _ _ => (I.p_pos k).le)
  have h3 := Finset.sum_union_inter (s₁ := (listB π i).erase i) (s₂ := D.outOfOrder π i)
    (f := I.p)
  have h3' : 0 ≤ ∑ k ∈ (listB π i).erase i ∩ D.outOfOrder π i, I.p k :=
    Finset.sum_nonneg fun k _ => (I.p_pos k).le
  have h4 : ∑ k ∈ (listB π i).erase i, I.p k = psum I (listB π i) - I.p i := by
    unfold psum
    rw [Finset.sum_erase_eq_sub (by simp [listB])]
  unfold psum at h4 ⊢
  linarith

theorem cb_core {π : Fin n ≃ Fin n} (hm : 2 ≤ m) (hπ : ObeysPrecedence I π) (β : ℝ)
    (hβ : 0 < β) (D : DelayListRun I m) (hD : IsDelayListSchedule I m π β D) (i j₁ : Fin n)
    (l : List (Fin n)) (hP : D.IsPathPrime i j₁ l) :
    D.C i ≤ (1 + β) * psum I (listB π i) / m + (1 + 1 / β) * kappaPrime I j₁ l
      - I.p i / β := by
  have hB := hD.2.1
  have hnn := aux_cl_idle_nonneg D hB
  have hO := (icb_core hπ β hβ D hD i j₁ l hP).2.1
  obtain ⟨hlast, hchain, hfirst⟩ := hP
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hS0 : 0 ≤ D.S i := (I.r_nonneg i).trans (aux_cb_ready_start D hD i).1
  -- idle bound
  have hpi := aux_icb_chain_pi hπ D l j₁ hchain
  rw [hlast] at hpi
  have hch := aux_cb_chain hβ D hD i l j₁ hchain hpi
  rw [hlast] at hch
  have hq1 := aux_icb_first_q D hfirst
  have hq0 : 0 ≤ D.q j₁ := (I.r_nonneg j₁).trans (aux_cl_r_le_q D j₁)
  have hsub : Set.Ioo 0 (D.S i) ⊆ Set.Ioc 0 (D.q j₁) ∪ Set.Ioo (D.q j₁) (D.S i) := by
    intro x hx
    by_cases h : x ≤ D.q j₁
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨not_le.mp h, hx.2⟩
  have e1 := aux_cb_sub_union D hB measurableSet_Ioc measurableSet_Ioo (by simp) (by simp) hsub
  have e2 : ∫ t in Set.Ioc 0 (D.q j₁), D.idle t ≤ (m : ℝ) * D.q j₁ := by
    calc ∫ t in Set.Ioc 0 (D.q j₁), D.idle t ≤ ‖∫ t in Set.Ioc 0 (D.q j₁), D.idle t‖ :=
          Real.le_norm_self _
      _ ≤ (m : ℝ) * volume.real (Set.Ioc 0 (D.q j₁)) := by
          apply norm_setIntegral_le_of_norm_le_const (by simp)
          intro x _
          rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
          exact aux_cl_idle_le D x
      _ = (m : ℝ) * D.q j₁ := by rw [Real.volume_real_Ioc_of_le hq0, sub_zero]
  have e3 : D.chargedToIn (listB π i) (Set.Ioo (D.q j₁) (D.S i)) ≤ β * psum I (listB π i) := by
    unfold DelayListRun.chargedToIn psum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    refine le_trans ?_ (aux_cb_charge_le hβ D hD k)
    exact setIntegral_mono_set
      (aux_cl_intOn D hB _ _ _ (aux_icb_cs_sub D k))
      (Filter.Eventually.of_forall fun t => hnn t)
      (Filter.Eventually.of_forall Set.inter_subset_left)
  have e4 := aux_cb_busy D hD i hS0
  -- algebra
  set K := kappaPrime I j₁ l - I.p i with hK
  have hKdef : kappaPrime I j₁ l = I.r j₁ + ((j₁ :: l).map I.p).sum := rfl
  have hidle : ∫ t in Set.Ioo 0 (D.S i), D.idle t ≤ (m : ℝ) * K + β * psum I (listB π i) := by
    have : (m : ℝ) * D.q j₁ ≤ (m : ℝ) * I.r j₁ := mul_le_mul_of_nonneg_left hq1 hm0.le
    rw [hK, hKdef]
    nlinarith
  have hmain : (m : ℝ) * D.S i ≤ (m : ℝ) * K + (1 + β) * psum I (listB π i) - I.p i +
      (m : ℝ) * K / β := by
    nlinarith
  have hpi0 := I.p_pos i
  have hC : D.C i = D.S i + I.p i := rfl
  have hgoal : D.S i ≤ K + (1 + β) * psum I (listB π i) / m - I.p i / m + K / β := by
    have : D.S i = ((m : ℝ) * D.S i) / m := by field_simp
    rw [this]
    have h' : ((m : ℝ) * K + (1 + β) * psum I (listB π i) - I.p i + (m : ℝ) * K / β) / m =
        K + (1 + β) * psum I (listB π i) / m - I.p i / m + K / β := by
      field_simp
    rw [← h']
    exact div_le_div_of_nonneg_right hmain hm0.le
  have hpm : 0 ≤ I.p i / m := div_nonneg hpi0.le hm0.le
  have hfin : (1 + 1 / β) * kappaPrime I j₁ l - I.p i / β = K + K / β + I.p i := by
    rw [hK]; field_simp; ring
  rw [hC]
  linarith

end


section
variable {n m : ℕ} {I : Instance n}

theorem aux_om_path (D : DelayListRun I m) (i : Fin n) :
    ∃ j₁ l, D.IsPathPrime i j₁ l := by
  classical
  induction i using I.prec_wf.induction with
  | _ i IH =>
  by_cases h : ∃ c, I.prec c i ∧ I.r i ≤ D.C c
  · obtain ⟨c0, hc0⟩ := h
    obtain ⟨a, ha, hmax⟩ := (Finset.univ.filter fun c => I.prec c i ∧ I.r i ≤ D.C c).exists_max_image
      D.C ⟨c0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc0⟩⟩
    obtain ⟨_, hap, har⟩ := Finset.mem_filter.mp ha
    have hstep : D.PathStep a i :=
      ⟨hap, har, fun c hc hrc => hmax c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hrc⟩)⟩
    obtain ⟨j₁, l, hlast, hchain, hfirst⟩ := IH a hap
    refine ⟨j₁, l ++ [i], ?_, ?_, hfirst⟩
    · simp
    · rw [← List.cons_append]
      refine hchain.append (List.isChain_singleton _) ?_
      intro x hx y hy
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      rw [List.getLast?_eq_getLast (List.cons_ne_nil _ _)] at hx
      simp only [Option.mem_def, Option.some.injEq] at hx
      rw [← hx, hlast]
      exact hstep
  · push Not at h
    exact ⟨i, [], by simp, List.isChain_singleton _, h⟩

theorem aux_om_obeys {S1 : Schedule I 1} {π : Fin n ≃ Fin n} (hπ : IsCompletionOrder S1 π) :
    ObeysPrecedence I π := by
  intro i j hij
  by_contra h
  push Not at h
  have h1 := hπ _ _ h
  simp only [Equiv.apply_symm_apply] at h1
  have h2 := S1.precedence i j hij
  have h3 : S1.C j = S1.S j + I.p j := rfl
  have h4 : S1.C i = S1.S i + I.p i := rfl
  linarith [I.p_pos j]

theorem aux_om_psum {S1 : Schedule I 1} {π : Fin n ≃ Fin n} (hπ : IsCompletionOrder S1 π)
    (i : Fin n) : psum I (listB π i) ≤ S1.C i := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑(listB π i) : Set (Fin n))
      (fun k => Set.Ico (S1.S k) (S1.S k + I.p k)) := by
    intro a _ b _ hab
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro x hx hx'
    rcases S1.noOverlap a b (Subsingleton.elim _ _) hab with h | h
    · linarith [hx.2, hx'.1]
    · linarith [hx.1, hx'.2]
  have hsub : (⋃ k ∈ listB π i, Set.Ico (S1.S k) (S1.S k + I.p k)) ⊆ Set.Icc 0 (S1.C i) := by
    intro x hx
    obtain ⟨k, hk, hx⟩ := Set.mem_iUnion₂.mp hx
    have hk' : π.symm k ≤ π.symm i := by simpa [listB] using hk
    have h1 := hπ _ _ hk'
    simp only [Equiv.apply_symm_apply] at h1
    have h2 : S1.C k = S1.S k + I.p k := rfl
    exact ⟨(I.r_nonneg k).trans ((S1.released k).trans hx.1), by linarith [hx.2]⟩
  have hm := measureReal_mono (μ := volume) hsub (by simp)
  rw [measureReal_biUnion_finset hdisj (fun k _ => measurableSet_Ico) (fun k _ => by simp),
    Real.volume_real_Icc] at hm
  unfold psum
  calc ∑ k ∈ listB π i, I.p k = ∑ k ∈ listB π i, volume.real (Set.Ico (S1.S k) (S1.S k + I.p k)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Real.volume_real_Ico_of_le (by linarith [I.p_pos k])]; ring
    _ ≤ max (S1.C i - 0) 0 := hm
    _ = S1.C i := by
        have : 0 ≤ S1.C i := by
          have h2 : S1.C i = S1.S i + I.p i := rfl
          linarith [I.r_nonneg i, S1.released i, I.p_pos i]
        rw [sub_zero, max_eq_left this]

theorem om_core (hm : 2 ≤ m) (β : ℝ)
    (hβ : 0 < β) (S1 : Schedule I 1) (π : Fin n ≃ Fin n) (hπ : IsCompletionOrder S1 π)
    (D : DelayListRun I m) (hD : IsDelayListSchedule I m π β D) (i : Fin n) :
    D.C i ≤ (1 + β) * S1.C i / m + (1 + 1 / β) * kappa I i := by
  obtain ⟨j₁, l, hP⟩ := aux_om_path D i
  have hob := aux_om_obeys hπ
  have h1 := cb_core hm hob β hβ D hD i j₁ l hP
  have hk : kappaPrime I j₁ l ≤ kappa I i := by
    obtain ⟨hlast, hchain, _⟩ := hP
    have h1 := aux_kpl_chain I D l j₁ hchain
    rw [hlast] at h1
    have h2 := aux_kpl_ge I j₁
    unfold kappaPrime
    simp only [List.map_cons, List.sum_cons]
    linarith
  have hpsum := aux_om_psum hπ i
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have e1 : (1 + β) * psum I (listB π i) / m ≤ (1 + β) * S1.C i / m :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpsum (by linarith)) hm0.le
  have e2 : (1 + 1 / β) * kappaPrime I j₁ l ≤ (1 + 1 / β) * kappa I i :=
    mul_le_mul_of_nonneg_left hk (by positivity)
  have e3 : 0 ≤ I.p i / β := div_nonneg (I.p_pos i).le hβ.le
  linarith

end

end AvgCompletionSched.DelayList

open AvgCompletionSched.DelayList


theorem solution {n m : ℕ} (I : Instance n) (hm : 2 ≤ m) (β : ℝ)
    (hβ : 0 < β) (S1 : Schedule I 1) (π : Fin n ≃ Fin n) (hπ : IsCompletionOrder S1 π)
    (D : DelayListRun I m) (hD : IsDelayListSchedule I m π β D) (i : Fin n) :
    D.C i ≤ (1 + β) * S1.C i / m + (1 + 1 / β) * kappa I i := by
  exact om_core hm β hβ S1 π hπ D hD i
