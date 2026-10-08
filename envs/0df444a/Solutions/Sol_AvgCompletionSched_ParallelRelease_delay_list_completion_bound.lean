-- Prove2me | solution 1 for AvgCompletionSched.ParallelRelease.delay_list_completion_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T12:47:42.297989+00:00
-- url     : https://prove2.me/submissions/339f7270-914e-4ac2-84bc-8c31fa7f35a6

import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model
import Definitions.Def_AvgCompletionSched_ParallelRelease_DelayList



namespace AvgCompletionSched.ParallelRelease

open MeasureTheory

/-- Abstract real-analysis lemma. -/
theorem aux_dlb_abs (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hf0 : ∀ x, 0 ≤ f x)
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
variable {n m : ℕ} {I : Instance n m}

theorem aux_dlb_idle_meas (D : DelayListRun I) : Measurable D.idle := by
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

theorem aux_dlb_busy_eq (D : DelayListRun I) (t : ℝ) : (m : ℝ) - D.idle t =
      ∑ k, (Set.Ico (D.S k) (D.S k + I.p k)).indicator (fun _ => (1 : ℝ)) t := by
  unfold DelayListRun.idle
  rw [sub_sub_cancel, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : D.S k ≤ t ∧ t < D.S k + I.p k
  · rw [if_pos hk, Set.indicator_of_mem (Set.mem_Ico.mpr hk)]
  · rw [if_neg hk]
    simp only [Set.indicator, Set.mem_Ico]
    rw [if_neg hk]

theorem aux_dlb_idle_nonneg (D : DelayListRun I)
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

theorem aux_dlb_idle_le (D : DelayListRun I) (t : ℝ) : D.idle t ≤ m := by
  unfold DelayListRun.idle
  exact sub_le_self _ (Nat.cast_nonneg _)

theorem aux_dlb_idle_nonpos (D : DelayListRun I) (t : ℝ)
    (h : ¬ ∃ μ : Fin m, ∀ k, D.M k = μ → ¬ (D.S k ≤ t ∧ t < D.S k + I.p k)) :
    D.idle t ≤ 0 := by
  unfold DelayListRun.idle
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

theorem aux_dlb_intOn (D : DelayListRun I)
    (hB : ∀ j k, D.Before k j → D.M k = D.M j → D.S k + I.p k ≤ D.S j)
    (A : Set ℝ) (a b : ℝ) (hA : A ⊆ Set.Icc a b) : IntegrableOn D.idle A := by
  refine Measure.integrableOn_of_bounded (M := m) ?_ (aux_dlb_idle_meas D).aestronglyMeasurable ?_
  · exact ne_top_of_le_ne_top (by simp) (measure_mono hA)
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (aux_dlb_idle_nonneg D hB x)]
    exact aux_dlb_idle_le D x

theorem aux_dlb_before_of_lt (D : DelayListRun I) (h1 : ∀ j k, D.Before k j → D.S k ≤ D.S j)
    {k l : Fin n} (h : D.S k < D.S l) : D.Before k l := by
  unfold DelayListRun.Before
  rcases lt_trichotomy (D.ev.symm k) (D.ev.symm l) with h' | h' | h'
  · exact h'
  · have := D.ev.symm.injective h'
    subst this
    exact absurd h (lt_irrefl _)
  · have := h1 k l h'
    linarith

theorem aux_dlb_gc {π : Fin n ≃ Fin n} {β : ℝ} (hβ : 0 < β) (D : DelayListRun I)
    (hD : IsDelayListSchedule I π β D) :
    ∀ l, ∫ t in Set.Ioo (I.r l) (D.S l) \ ⋃ k ∈ {k | D.Before k l}, D.window k, D.idle t
      ≤ β * I.p l := by
  obtain ⟨_, hB1, hB2, hC, hN⟩ := hD
  have hnn := aux_dlb_idle_nonneg D hB2
  have hint := aux_dlb_intOn D hB2
  suffices H : ∀ a : ℕ, ∀ l, (D.ev.symm l : ℕ) = a →
      ∫ t in Set.Ioo (I.r l) (D.S l) \ ⋃ k ∈ {k | D.Before k l}, D.window k, D.idle t
        ≤ β * I.p l by
    intro l
    exact H _ l rfl
  intro a
  induction a using Nat.strong_induction_on with
  | _ a IH =>
  intro l hl
  have IH' : ∀ k, D.Before k l →
      ∫ t in Set.Ioo (I.r k) (D.S k) \ ⋃ k' ∈ {k' | D.Before k' k}, D.window k', D.idle t
        ≤ β * I.p k := by
    intro k hk
    refine IH _ ?_ k rfl
    rw [← hl]
    exact hk
  have hWm : MeasurableSet (⋃ k ∈ {k | D.Before k l}, D.window k) :=
    MeasurableSet.biUnion (Set.to_countable _) fun k _ => measurableSet_Ioo
  set T := Set.Ioo (I.r l) (D.S l) \ ⋃ k ∈ {k | D.Before k l}, D.window k with hT
  set Z := ⋃ k ∈ {k | D.Before k l}, (Set.Ico (I.r k) (D.S k) \ D.window k) with hZ
  have hTm : MeasurableSet T := measurableSet_Ioo.diff hWm
  have hZm : MeasurableSet Z :=
    MeasurableSet.biUnion (Set.to_countable _) fun k _ => measurableSet_Ico.diff measurableSet_Ioo
  have hTsub : T ⊆ Set.Icc (I.r l) (D.S l) := fun x hx => ⟨hx.1.1.le, hx.1.2.le⟩
  have hq0 : 0 ≤ I.r l := I.r_nonneg l
  -- Step A
  have hA : ∀ k, D.Before k l →
      ∫ t in T ∩ (Set.Ico (I.r k) (D.S k) \ D.window k), D.idle t = 0 := by
    intro k hk
    refine le_antisymm ?_ (integral_nonneg fun t => hnn t)
    have hsubW : ∀ x, x ∈ T → x ∉ ⋃ k' ∈ {k' | D.Before k' k}, D.window k' := by
      intro x hx hx'
      simp only [Set.mem_iUnion] at hx'
      obtain ⟨k', hk', hxk'⟩ := hx'
      exact hx.2 (Set.mem_biUnion (show D.Before k' l from lt_trans hk' hk) hxk')
    rcases hC k with ⟨_, hτ⟩ | ⟨_, _, _, _, _, hch⟩
    · have hsub : T ∩ (Set.Ico (I.r k) (D.S k) \ D.window k) ⊆ {I.r k} := by
        intro x hx
        simp only [DelayListRun.window, hτ, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_Ico,
          Set.mem_Ioo] at hx
        simp only [Set.mem_singleton_iff]
        by_contra hne
        exact hx.2.2 ⟨lt_of_le_of_ne hx.2.1.1 (Ne.symm hne), hx.2.1.2⟩
      rw [setIntegral_measure_zero _ (measure_mono_null hsub Real.volume_singleton)]
    · by_cases hqτ : I.r k ≤ D.τ k
      · have hAsub : Set.Ioo (I.r k) (D.S k) \ ⋃ k' ∈ {k' | D.Before k' k}, D.window k' ⊆
            Set.Icc (I.r k) (D.S k) := fun x hx => ⟨hx.1.1.le, hx.1.2.le⟩
        have hIHk := IH' k hk
        have hsplitA := integral_inter_add_sdiff (μ := volume) (f := D.idle)
          (s := Set.Ioo (I.r k) (D.S k) \ ⋃ k' ∈ {k' | D.Before k' k}, D.window k')
          (t := D.window k) measurableSet_Ioo (hint _ _ _ hAsub)
        have hAinter : (Set.Ioo (I.r k) (D.S k) \ ⋃ k' ∈ {k' | D.Before k' k}, D.window k') ∩
            D.window k = D.window k \ ⋃ k' ∈ {k' | D.Before k' k}, D.window k' := by
          ext x
          simp only [DelayListRun.window, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_Ioo]
          constructor
          · rintro ⟨⟨_, h2⟩, h3⟩
            exact ⟨h3, h2⟩
          · rintro ⟨h3, h2⟩
            exact ⟨⟨⟨lt_of_le_of_lt hqτ h3.1, h3.2⟩, h2⟩, h3⟩
        rw [hAinter] at hsplitA
        have hch' : ∫ t in D.window k \ ⋃ k' ∈ {k' | D.Before k' k}, D.window k', D.idle t
            = β * I.p k := hch
        rw [hch'] at hsplitA
        calc ∫ t in T ∩ (Set.Ico (I.r k) (D.S k) \ D.window k), D.idle t
            ≤ ∫ t in (Set.Ioo (I.r k) (D.S k) \ ⋃ k' ∈ {k' | D.Before k' k}, D.window k') \
                D.window k, D.idle t := by
              refine setIntegral_mono_set (hint _ _ _ (Set.sdiff_subset.trans hAsub))
                (Filter.Eventually.of_forall fun t => hnn t) ?_
              rw [ae_le_set]
              refine measure_mono_null ?_ (Real.volume_singleton (a := I.r k))
              intro x hx
              simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_Ico] at hx
              simp only [Set.mem_singleton_iff]
              by_contra hne
              apply hx.2
              refine ⟨⟨⟨lt_of_le_of_ne hx.1.2.1.1 (Ne.symm hne), hx.1.2.1.2⟩,
                hsubW x hx.1.1⟩, hx.1.2.2⟩
          _ ≤ 0 := by linarith
      · have hsub : T ∩ (Set.Ico (I.r k) (D.S k) \ D.window k) ⊆ {I.r k} := by
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
          (T ∩ (Set.Ico (I.r k) (D.S k) \ D.window k)) := by
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
    have hidle : ∃ μ : Fin m, ∀ k, D.M k = μ → ¬ (D.S k ≤ s ∧ s < D.S k + I.p k) := by
      by_contra hc
      linarith [aux_dlb_idle_nonpos D s hc]
    have hs0 : 0 ≤ s := hq0.trans hsT.1.1.le
    have hrl : I.r l ≤ s := hsT.1.1.le
    classical
    obtain ⟨k0, hk0C, hk0min⟩ :=
      (Finset.univ.filter (fun k => s < D.S k ∧ I.r k ≤ s)).exists_min_image
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
        rcases hC l with ⟨h1, _⟩ | ⟨_, h3, _⟩
        · exact absurd (h1 k0 hnb) (not_le.mpr hlt)
        · exact absurd (h3 k0 hnb (hk0R.trans hsT.1.2.le)) (not_le.mpr hlt)
      have hnotwin : s ∉ D.window k0 := fun h => hsT.2 (Set.mem_biUnion hbef h)
      exact hsZ (Set.mem_biUnion hbef ⟨⟨hk0R, hk0S⟩, hnotwin⟩)
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
              (aux_dlb_before_of_lt D hB1 (lt_of_le_of_lt hk'' hsT.1.2)) hxk')
      _ < β * I.p l := hU
  -- Step D
  exact aux_dlb_abs D.idle (aux_dlb_idle_meas D) m hnn (aux_dlb_idle_le D) T Z hTm hZm _ _ hTsub
    (β * I.p l) (mul_nonneg hβ.le (I.p_pos l).le) hBz hCstep

end


section
variable {n m : ℕ} {I : Instance n m}

/-- The union of the windows of the jobs scheduled before `j`. -/
def aux_dlb_W (D : DelayListRun I) (j : Fin n) : Set ℝ := ⋃ k ∈ {k | D.Before k j}, D.window k

/-- The set of times whose idle time is charged to `j`. -/
def aux_dlb_cs (D : DelayListRun I) (j : Fin n) : Set ℝ := D.window j \ aux_dlb_W D j

theorem aux_dlb_cs_meas (D : DelayListRun I) (j : Fin n) : MeasurableSet (aux_dlb_cs D j) :=
  measurableSet_Ioo.diff (MeasurableSet.biUnion (Set.to_countable _) fun _ _ => measurableSet_Ioo)

theorem aux_dlb_cs_disj (D : DelayListRun I) {j k : Fin n} (h : j ≠ k) :
    Disjoint (aux_dlb_cs D j) (aux_dlb_cs D k) := by
  rw [Set.disjoint_left]
  intro x hxj hxk
  rcases lt_trichotomy (D.ev.symm j) (D.ev.symm k) with h' | h' | h'
  · exact hxk.2 (Set.mem_biUnion (show D.Before j k from h') hxj.1)
  · exact h (D.ev.symm.injective h')
  · exact hxj.2 (Set.mem_biUnion (show D.Before k j from h') hxk.1)

theorem aux_dlb_cs_min (D : DelayListRun I) {i : Fin n} {x : ℝ} (hx : x ∈ aux_dlb_W D i) :
    ∃ k, D.Before k i ∧ x ∈ aux_dlb_cs D k := by
  classical
  have hne : (Finset.univ.filter (fun k => D.Before k i ∧ x ∈ D.window k)).Nonempty := by
    simp only [aux_dlb_W, Set.mem_iUnion] at hx
    obtain ⟨k, hk, hxk⟩ := hx
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hxk⟩⟩
  obtain ⟨k, hkC, hkmin⟩ := Finset.exists_min_image _ (fun k => D.ev.symm k) hne
  obtain ⟨_, hki, hxk⟩ := Finset.mem_filter.mp hkC
  refine ⟨k, hki, hxk, ?_⟩
  intro hx'
  simp only [aux_dlb_W, Set.mem_iUnion] at hx'
  obtain ⟨k', hk', hxk'⟩ := hx'
  have hk'i : D.Before k' i := lt_trans (show D.ev.symm k' < D.ev.symm k from hk') hki
  have := hkmin k' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'i, hxk'⟩)
  exact absurd (show D.ev.symm k' < D.ev.symm k from hk') (not_lt.mpr this)

theorem aux_dlb_charge_le {π : Fin n ≃ Fin n} {β : ℝ} (hβ : 0 < β) (D : DelayListRun I)
    (hD : IsDelayListSchedule I π β D) (k : Fin n) :
    ∫ t in aux_dlb_cs D k, D.idle t ≤ β * I.p k := by
  rcases hD.2.2.2.1 k with ⟨_, hτ⟩ | ⟨_, _, _, _, _, hch⟩
  · have hw : D.window k = Set.Ioo (I.r k) (D.S k) := by simp [DelayListRun.window, hτ]
    have : aux_dlb_cs D k =
        Set.Ioo (I.r k) (D.S k) \ ⋃ k' ∈ {k' | D.Before k' k}, D.window k' := by
      simp only [aux_dlb_cs, aux_dlb_W]
      rw [hw]
    rw [this]
    exact aux_dlb_gc hβ D hD k
  · exact hch.le

theorem aux_dlb_out {π : Fin n ≃ Fin n} {β : ℝ} (D : DelayListRun I)
    (hD : IsDelayListSchedule I π β D) {k i : Fin n} (hki : D.Before k i)
    (hπ : π.symm i < π.symm k) :
    D.S k < I.r i ∧ 0 ≤ D.τ k ∧ D.charge k = β * I.p k := by
  have hni : ¬ D.Before i k := fun h =>
    lt_asymm (show D.ev.symm i < D.ev.symm k from h) (show D.ev.symm k < D.ev.symm i from hki)
  rcases hD.2.2.2.1 k with ⟨h1, _⟩ | ⟨_, h3, _, hτ0, _, hch⟩
  · exact absurd (h1 i hni) (not_le.mpr hπ)
  · refine ⟨?_, hτ0, hch⟩
    by_contra hle
    exact absurd (h3 i hni (not_lt.mp hle)) (not_le.mpr hπ)

theorem aux_dlb_ind_int (a b : ℝ) :
    Integrable ((Set.Ico a b).indicator (fun _ => (1 : ℝ))) := by
  refine (integrable_indicator_iff measurableSet_Ico).2 ?_
  exact integrableOn_const (by simp [Real.volume_Ico])

theorem aux_dlb_cs_sub (D : DelayListRun I) (j : Fin n) :
    aux_dlb_cs D j ⊆ Set.Icc (D.τ j) (D.S j) := fun _ hx => ⟨hx.1.1.le, hx.1.2.le⟩

end


section
variable {n m : ℕ} {I : Instance n m}

theorem aux_dlb_job {π : Fin n ≃ Fin n} {β : ℝ} (hβ : 0 < β) (D : DelayListRun I)
    (hD : IsDelayListSchedule I π β D) (i : Fin n) :
    (m : ℝ) * D.S i ≤ (1 + β) * (∑ k ∈ Finset.univ.filter (fun k => π.symm k ≤ π.symm i), I.p k)
      + (m : ℝ) * I.r i + (m : ℝ) * I.r i / β := by
  classical
  have hR := hD.1
  have hB1 := hD.2.1
  have hB2 := hD.2.2.1
  set B := Finset.univ.filter (fun k => π.symm k ≤ π.symm i) with hBdef
  set L := Finset.univ.filter (fun k => π.symm k < π.symm i) with hLdef
  set O := Finset.univ.filter (fun k => D.S k < D.S i ∧ π.symm i < π.symm k) with hOdef
  have hnn := aux_dlb_idle_nonneg D hB2
  have hint := aux_dlb_intOn D hB2
  have hri : 0 ≤ I.r i := I.r_nonneg i
  have hSi : I.r i ≤ D.S i := hR i
  have hS0 : 0 ≤ D.S i := hri.trans hSi
  -- busy time
  have hbusy : ∫ t in Set.Ico 0 (D.S i), ((m : ℝ) - D.idle t) ≤
      (∑ k ∈ B, I.p k) + ∑ k ∈ O, I.p k := by
    simp_rw [aux_dlb_busy_eq D]
    rw [integral_finsetSum _ (fun k _ => (aux_dlb_ind_int _ _).integrableOn)]
    calc ∑ k, ∫ t in Set.Ico 0 (D.S i),
            (Set.Ico (D.S k) (D.S k + I.p k)).indicator (fun _ => (1 : ℝ)) t
        ≤ ∑ k, ((if π.symm k ≤ π.symm i then I.p k else 0) +
            (if D.S k < D.S i ∧ π.symm i < π.symm k then I.p k else 0)) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have hp := (I.p_pos k).le
          by_cases hk : D.S k < D.S i
          · have h1 : ∫ t in Set.Ico 0 (D.S i),
                (Set.Ico (D.S k) (D.S k + I.p k)).indicator (fun _ => (1 : ℝ)) t ≤ I.p k := by
              refine (setIntegral_le_integral (aux_dlb_ind_int _ _)
                (Filter.Eventually.of_forall fun t => ?_)).trans ?_
              · exact Set.indicator_nonneg (fun _ _ => zero_le_one) t
              · rw [integral_indicator_const _ measurableSet_Ico,
                  Real.volume_real_Ico_of_le (by linarith)]
                simp
            rcases le_or_gt (π.symm k) (π.symm i) with h | h
            · rw [if_pos h]
              have : (0 : ℝ) ≤ if D.S k < D.S i ∧ π.symm i < π.symm k then I.p k else 0 := by
                split_ifs <;> linarith
              linarith
            · rw [if_pos (show D.S k < D.S i ∧ π.symm i < π.symm k from ⟨hk, h⟩)]
              have : (0 : ℝ) ≤ if π.symm k ≤ π.symm i then I.p k else 0 := by
                split_ifs <;> linarith
              linarith
          · rw [setIntegral_eq_zero_of_forall_eq_zero]
            · have h1 : (0 : ℝ) ≤ if π.symm k ≤ π.symm i then I.p k else 0 := by
                split_ifs <;> linarith
              have h2 : (0 : ℝ) ≤ if D.S k < D.S i ∧ π.symm i < π.symm k then I.p k else 0 := by
                split_ifs <;> linarith
              linarith
            · intro x hx
              apply Set.indicator_of_notMem
              intro hx'
              exact hk (lt_of_le_of_lt hx'.1 hx.2)
      _ = (∑ k ∈ B, I.p k) + ∑ k ∈ O, I.p k := by
          rw [Finset.sum_add_distrib, hBdef, hOdef, Finset.sum_filter, Finset.sum_filter]
  -- total machine time
  have htot : (m : ℝ) * D.S i = (∫ t in Set.Ico 0 (D.S i), ((m : ℝ) - D.idle t))
      + ∫ t in Set.Ico 0 (D.S i), D.idle t := by
    have hc1 : IntegrableOn (fun _ : ℝ => (m : ℝ)) (Set.Ico 0 (D.S i)) :=
      integrableOn_const (by simp [Real.volume_Ico])
    have hc2 := hint _ 0 (D.S i) Set.Ico_subset_Icc_self
    have e : (∫ t in Set.Ico 0 (D.S i), ((m : ℝ) - D.idle t)) =
        (∫ t in Set.Ico 0 (D.S i), (m : ℝ)) - ∫ t in Set.Ico 0 (D.S i), D.idle t :=
      integral_sub hc1 hc2
    rw [e, setIntegral_const, Real.volume_real_Ico_of_le hS0]
    simp only [smul_eq_mul, sub_zero]
    ring
  -- split the idle time at r_i
  have hsplit : ∫ t in Set.Ico 0 (D.S i), D.idle t =
      (∫ t in Set.Ico 0 (I.r i), D.idle t) + ∫ t in Set.Ico (I.r i) (D.S i), D.idle t := by
    rw [← Set.Ico_union_Ico_eq_Ico hri hSi]
    exact setIntegral_union (Set.Ico_disjoint_Ico_same) measurableSet_Ico
      (hint _ 0 (I.r i) Set.Ico_subset_Icc_self) (hint _ (I.r i) (D.S i) Set.Ico_subset_Icc_self)
  -- idle time before r_i
  have hI0 : ∫ t in Set.Ico 0 (I.r i), D.idle t ≤ (m : ℝ) * I.r i := by
    calc ∫ t in Set.Ico 0 (I.r i), D.idle t ≤ ∫ t in Set.Ico 0 (I.r i), (m : ℝ) := by
          refine setIntegral_mono_on (hint _ 0 (I.r i) Set.Ico_subset_Icc_self)
            (integrableOn_const (by simp [Real.volume_Ico])) measurableSet_Ico
            (fun t _ => aux_dlb_idle_le D t)
      _ = (m : ℝ) * I.r i := by
          rw [setIntegral_const, Real.volume_real_Ico_of_le hri]
          simp only [smul_eq_mul, sub_zero]
          ring
  -- out-of-order jobs are paid for by idle time before r_i
  have hOinfo : ∀ k ∈ O, D.S k < I.r i ∧ 0 ≤ D.τ k ∧ D.charge k = β * I.p k := by
    intro k hk
    obtain ⟨_, hk1, hk2⟩ := Finset.mem_filter.mp hk
    exact aux_dlb_out D hD (aux_dlb_before_of_lt D hB1 hk1) hk2
  have hO : β * ∑ k ∈ O, I.p k ≤ ∫ t in Set.Ico 0 (I.r i), D.idle t := by
    calc β * ∑ k ∈ O, I.p k = ∑ k ∈ O, ∫ t in aux_dlb_cs D k, D.idle t := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          exact ((hOinfo k hk).2.2).symm
      _ = ∫ t in ⋃ k ∈ O, aux_dlb_cs D k, D.idle t := by
          rw [integral_biUnion_finset O (fun k _ => aux_dlb_cs_meas D k)
            (fun a _ b _ hab => aux_dlb_cs_disj D hab)
            (fun k _ => hint _ _ _ (aux_dlb_cs_sub D k))]
      _ ≤ ∫ t in Set.Ico 0 (I.r i), D.idle t := by
          have hsub : (⋃ k ∈ O, aux_dlb_cs D k) ⊆ Set.Ico 0 (I.r i) := by
            intro x hx
            simp only [Set.mem_iUnion] at hx
            obtain ⟨k, hk, hxk⟩ := hx
            obtain ⟨h1, h2, _⟩ := hOinfo k hk
            exact ⟨h2.trans hxk.1.1.le, hxk.1.2.trans h1⟩
          exact setIntegral_mono_set (hint _ 0 (I.r i) Set.Ico_subset_Icc_self)
            (Filter.Eventually.of_forall fun t => hnn t) (Filter.Eventually.of_forall hsub)
  -- idle time after r_i
  have hLbound : ∫ t in Set.Ico (I.r i) (D.S i), D.idle t ≤ β * I.p i + ∑ k ∈ L, β * I.p k := by
    set A := Set.Ioo (I.r i) (D.S i) \ aux_dlb_W D i with hA
    set Cs := ⋃ k ∈ L, aux_dlb_cs D k with hCs
    have hAm : MeasurableSet A :=
      measurableSet_Ioo.diff (MeasurableSet.biUnion (Set.to_countable _) fun _ _ => measurableSet_Ioo)
    have hCm : MeasurableSet Cs :=
      Finset.measurableSet_biUnion L (fun k _ => aux_dlb_cs_meas D k)
    have hAint : IntegrableOn D.idle A := hint _ (I.r i) (D.S i) (fun x hx => ⟨hx.1.1.le, hx.1.2.le⟩)
    have hCint : IntegrableOn D.idle Cs :=
      integrableOn_finset_iUnion.2 (fun k _ => hint _ _ _ (aux_dlb_cs_sub D k))
    have hsub : Set.Ioo (I.r i) (D.S i) ⊆ A ∪ Cs := by
      intro x hx
      by_cases hxW : x ∈ aux_dlb_W D i
      · right
        obtain ⟨k, hki, hxk⟩ := aux_dlb_cs_min D hxW
        simp only [hCs, Set.mem_iUnion]
        refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hxk⟩
        by_contra hnl
        have hne : k ≠ i := by
          rintro rfl
          exact lt_irrefl _ (show D.ev.symm k < D.ev.symm k from hki)
        have hlt : π.symm i < π.symm k :=
          lt_of_le_of_ne (not_lt.mp hnl) (fun h => hne (π.symm.injective h).symm)
        obtain ⟨h1, _, _⟩ := aux_dlb_out D hD hki hlt
        linarith [hxk.1.2, hx.1]
      · left
        exact ⟨hx, hxW⟩
    calc ∫ t in Set.Ico (I.r i) (D.S i), D.idle t = ∫ t in Set.Ioo (I.r i) (D.S i), D.idle t :=
          setIntegral_congr_set Ioo_ae_eq_Ico.symm
      _ ≤ ∫ t in A ∪ Cs, D.idle t :=
          setIntegral_mono_set (hAint.union hCint) (Filter.Eventually.of_forall fun t => hnn t)
            (Filter.Eventually.of_forall hsub)
      _ = (∫ t in A, D.idle t) + ∫ t in Cs \ A, D.idle t := by
          rw [← Set.union_sdiff_self]
          exact setIntegral_union Set.disjoint_sdiff_right (hCm.diff hAm) hAint
            (hCint.mono_set Set.sdiff_subset)
      _ ≤ (∫ t in A, D.idle t) + ∫ t in Cs, D.idle t := by
          have := setIntegral_mono_set (s := Cs \ A) hCint
            (Filter.Eventually.of_forall fun t => hnn t) (Set.sdiff_subset (s := Cs) (t := A)).eventuallyLE
          linarith
      _ ≤ β * I.p i + ∑ k ∈ L, β * I.p k := by
          have h1 : ∫ t in A, D.idle t ≤ β * I.p i := aux_dlb_gc hβ D hD i
          have h2 : ∫ t in Cs, D.idle t ≤ ∑ k ∈ L, β * I.p k := by
            rw [hCs, integral_biUnion_finset L (fun k _ => aux_dlb_cs_meas D k)
              (fun a _ b _ hab => aux_dlb_cs_disj D hab)
              (fun k _ => hint _ _ _ (aux_dlb_cs_sub D k))]
            exact Finset.sum_le_sum fun k _ => aux_dlb_charge_le hβ D hD k
          linarith
  -- B = insert i L
  have hBL : B = insert i L := by
    ext k
    simp only [hBdef, hLdef, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inr h'
      · exact Or.inl (π.symm.injective h')
    · rintro (rfl | h)
      · exact le_rfl
      · exact h.le
  have hiL : i ∉ L := by simp [hLdef]
  have hsumB : ∑ k ∈ B, I.p k = I.p i + ∑ k ∈ L, I.p k := by
    rw [hBL, Finset.sum_insert hiL]
  have hLβ : ∑ k ∈ L, β * I.p k = β * ∑ k ∈ L, I.p k := by rw [Finset.mul_sum]
  have hOle : ∑ k ∈ O, I.p k ≤ (m : ℝ) * I.r i / β := by
    rw [le_div_iff₀ hβ]
    linarith
  rw [htot, hsplit]
  nlinarith

end


section
variable {n m : ℕ} {I : Instance n m}

theorem aux_dlb_done_mono (P : RelaxSchedule I) (k : Fin n) {s t : ℝ} (h : s ≤ t) :
    P.done k s ≤ P.done k t := by
  unfold RelaxSchedule.done
  exact setIntegral_mono_set (P.integrable k).integrableOn
    (Filter.Eventually.of_forall fun x => P.nonneg k x) (Set.Iio_subset_Iio h).eventuallyLE

theorem aux_dlb_done_nonempty (P : RelaxSchedule I) (k : Fin n) :
    {t | I.p k / m ≤ P.done k t}.Nonempty := by
  obtain ⟨T, hT⟩ := P.bounded k
  refine ⟨T, ?_⟩
  show I.p k / m ≤ P.done k T
  unfold RelaxSchedule.done
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, P.total k]
  intro x hx
  exact hT x (not_lt.mp hx)

theorem aux_dlb_done_zero (P : RelaxSchedule I) (k : Fin n) {t : ℝ} (ht : t ≤ 0) :
    P.done k t = 0 := by
  unfold RelaxSchedule.done
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  exact P.released k x (lt_of_lt_of_le hx (ht.trans (I.r_nonneg k)))

theorem aux_dlb_sum_done (P : RelaxSchedule I) (B : Finset (Fin n)) (t : ℝ) (ht : 0 < t) :
    ∑ k ∈ B, P.done k t ≤ t := by
  unfold RelaxSchedule.done
  rw [← integral_finsetSum B (fun k _ => (P.integrable k).integrableOn)]
  have hvan : ∀ x ∈ Set.Iio t \ Set.Ico 0 t, ∑ k ∈ B, P.ρ k x = 0 := by
    intro x hx
    have hx0 : x < 0 := by
      by_contra h
      exact hx.2 ⟨not_lt.mp h, hx.1⟩
    exact Finset.sum_eq_zero fun k _ => P.released k x (lt_of_lt_of_le hx0 (I.r_nonneg k))
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iio
    (fun x hx => hx.2) hvan]
  calc ∫ x in Set.Ico 0 t, ∑ k ∈ B, P.ρ k x ≤ ∫ x in Set.Ico 0 t, (1 : ℝ) := by
        refine setIntegral_mono_on ?_ (integrableOn_const (by simp [Real.volume_Ico]))
          measurableSet_Ico ?_
        · exact (integrable_finsetSum B (fun k _ => P.integrable k)).integrableOn
        · intro x _
          calc ∑ k ∈ B, P.ρ k x ≤ ∑ k, P.ρ k x :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
                  (fun k _ _ => P.nonneg k x)
            _ ≤ 1 := P.capacity x
    _ = t := by
        rw [setIntegral_const, Real.volume_real_Ico_of_le ht.le]
        simp

theorem aux_dlb_relax (P : RelaxSchedule I) (B : Finset (Fin n)) (i : Fin n) (hi : i ∈ B)
    (hc : ∀ k ∈ B, P.CP k ≤ P.CP i) :
    (∑ k ∈ B, I.p k) / m ≤ P.CP i := by
  have hm : (0 : ℝ) < m := by exact_mod_cast I.m_pos
  refine le_of_forall_gt_imp_ge_of_dense fun t ht => ?_
  have hk : ∀ k ∈ B, I.p k / m ≤ P.done k t := by
    intro k hkB
    have hlt : sInf {t | I.p k / m ≤ P.done k t} < t := lt_of_le_of_lt (hc k hkB) ht
    obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt (aux_dlb_done_nonempty P k) hlt
    exact le_trans hs (aux_dlb_done_mono P k hst.le)
  have ht0 : 0 < t := by
    by_contra h
    have h1 := hk i hi
    rw [aux_dlb_done_zero P i (not_lt.mp h)] at h1
    have : 0 < I.p i / m := div_pos (I.p_pos i) hm
    linarith
  calc (∑ k ∈ B, I.p k) / m = ∑ k ∈ B, I.p k / m := Finset.sum_div _ _ _
    _ ≤ ∑ k ∈ B, P.done k t := Finset.sum_le_sum hk
    _ ≤ t := aux_dlb_sum_done P B t ht0

end

/-- The number of jobs running at time `t` in a nonpreemptive schedule is at most `m`. -/
theorem aux_dlb_rlb_card {n m : ℕ} (I : Instance n m) (N : Schedule I) (t : ℝ) :
    (Finset.univ.filter (fun j => t ∈ Set.Ico (N.S j) (N.S j + I.p j))).card ≤ m := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter
      (fun j => t ∈ Set.Ico (N.S j) (N.S j + I.p j))) (t := (Finset.univ : Finset (Fin m)))
      N.M (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
  · simpa using h
  · intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      Set.mem_Ico] at hi hj
    by_contra hne
    rcases N.noOverlap i j hij hne with h1 | h1
    · linarith [hi.1, hi.2, hj.1, hj.2]
    · linarith [hi.1, hi.2, hj.1, hj.2]

/-- The time-sliced relaxation schedule obtained from a nonpreemptive schedule. -/
noncomputable def aux_dlb_rlb_relax {n m : ℕ} (I : Instance n m) (N : Schedule I) :
    RelaxSchedule I where
  ρ j := (Set.Ico (N.S j) (N.S j + I.p j)).indicator (fun _ => (1 / (m : ℝ)))
  measurable j := (measurable_const).indicator measurableSet_Ico
  integrable j := by
    refine (integrable_indicator_iff measurableSet_Ico).2 ?_
    exact integrableOn_const (by simp [Real.volume_Ico])
  nonneg j t := by
    apply Set.indicator_nonneg
    intro _ _
    positivity
  capacity t := by
    have hm : (0 : ℝ) < m := by exact_mod_cast I.m_pos
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc := aux_dlb_rlb_card I N t
    have hc' : ((Finset.univ.filter (fun j => t ∈ Set.Ico (N.S j) (N.S j + I.p j))).card : ℝ)
        ≤ m := by exact_mod_cast hc
    calc _ ≤ (m : ℝ) * (1 / (m : ℝ)) := by
          apply mul_le_mul_of_nonneg_right hc'
          positivity
      _ = 1 := by field_simp
  released j t ht := by
    apply Set.indicator_of_notMem
    intro hmem
    have := N.released j
    have := hmem.1
    linarith
  total j := by
    rw [integral_indicator_const _ measurableSet_Ico,
      Real.volume_real_Ico_of_le (by linarith [I.p_pos j])]
    simp only [smul_eq_mul]
    ring
  bounded j := by
    refine ⟨N.S j + I.p j, fun t ht => ?_⟩
    apply Set.indicator_of_notMem
    intro hmem
    have := hmem.2
    linarith

theorem aux_dlb_rlb_CP_le {n m : ℕ} (I : Instance n m) (N : Schedule I) (j : Fin n) :
    (aux_dlb_rlb_relax I N).CP j ≤ N.C j := by
  unfold RelaxSchedule.CP
  by_cases hb : BddBelow {t | I.p j / m ≤ (aux_dlb_rlb_relax I N).done j t}
  · apply csInf_le hb
    show I.p j / m ≤ (aux_dlb_rlb_relax I N).done j (N.S j + I.p j)
    unfold RelaxSchedule.done
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rw [(aux_dlb_rlb_relax I N).total j]
    · intro x hx
      show (Set.Ico (N.S j) (N.S j + I.p j)).indicator (fun _ => (1 / (m : ℝ))) x = 0
      apply Set.indicator_of_notMem
      intro hmem
      exact hx hmem.2
  · rw [Real.sInf_of_not_bddBelow hb]
    unfold Schedule.C
    linarith [N.released j, I.r_nonneg j, I.p_pos j]

theorem aux_dlb_rlb {n m : ℕ} (I : Instance n m) (P1 : RelaxSchedule I)
    (hP1 : P1.IsOptimal) (Nstar : Schedule I) :
    ∑ j, P1.CP j ≤ ∑ j, Nstar.C j := by
  calc ∑ j, P1.CP j ≤ ∑ j, (aux_dlb_rlb_relax I Nstar).CP j := hP1 _
    _ ≤ ∑ j, Nstar.C j := Finset.sum_le_sum (fun j _ => aux_dlb_rlb_CP_le I Nstar j)

theorem aux_dlb_jobC {n m : ℕ} (I : Instance n m) (P1 : RelaxSchedule I) (π : Fin n ≃ Fin n)
    (hπ : IsCompletionOrder P1 π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I)
    (hD : IsDelayListSchedule I π β D) (i : Fin n) :
    D.C i ≤ (1 + β) * P1.CP i + I.r i + I.r i / β + I.p i := by
  have hm : (0 : ℝ) < m := by exact_mod_cast I.m_pos
  set X := ∑ k ∈ Finset.univ.filter (fun k => π.symm k ≤ π.symm i), I.p k with hX
  have h1 : (m : ℝ) * D.S i ≤ (1 + β) * X + (m : ℝ) * I.r i + (m : ℝ) * I.r i / β :=
    aux_dlb_job hβ D hD i
  have h2 : X / m ≤ P1.CP i := by
    refine aux_dlb_relax P1 _ i (by simp) (fun k hk => ?_)
    have hle := (Finset.mem_filter.mp hk).2
    have h := hπ (π.symm k) (π.symm i) hle
    simpa using h
  have h3 : D.S i ≤ (1 + β) * (X / m) + I.r i + I.r i / β := by
    have e : (m : ℝ) * ((1 + β) * (X / m) + I.r i + I.r i / β) =
        (1 + β) * X + (m : ℝ) * I.r i + (m : ℝ) * I.r i / β := by
      field_simp
    have h4 : (m : ℝ) * D.S i ≤ (m : ℝ) * ((1 + β) * (X / m) + I.r i + I.r i / β) := by
      rw [e]; exact h1
    exact le_of_mul_le_mul_left h4 hm
  have h5 : (1 + β) * (X / m) ≤ (1 + β) * P1.CP i :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  unfold DelayListRun.C
  linarith


/-- One step of the list scheduling recursion, with the chosen machine made explicit. -/
lemma aux_lsa_step {n m : ℕ} (I : Instance n m) (π : Fin n ≃ Fin n) (k : ℕ) (h : k < n) :
    ∃ μ : Fin m, (∀ ν, (listRun I π k).1 μ ≤ (listRun I π k).1 ν) ∧
      listRun I π (k + 1) =
        (Function.update (listRun I π k).1 μ
          (max (max (I.r (π ⟨k, h⟩)) (listRun I π k).2) ((listRun I π k).1 μ) + I.p (π ⟨k, h⟩)),
         max (max (I.r (π ⟨k, h⟩)) (listRun I π k).2) ((listRun I π k).1 μ)) := by
  refine ⟨Classical.choose (Finset.exists_min_image Finset.univ (listRun I π k).1
    ⟨⟨0, I.m_pos⟩, Finset.mem_univ _⟩), fun ν => (Classical.choose_spec
      (Finset.exists_min_image Finset.univ (listRun I π k).1
    ⟨⟨0, I.m_pos⟩, Finset.mem_univ _⟩)).2 ν (Finset.mem_univ _), ?_⟩
  rw [listRun.eq_2, dif_pos h]

/-- Invariant of list scheduling with respect to a threshold `T` that dominates the release
dates of the jobs scheduled so far. -/
lemma aux_lsa_inv {n m : ℕ} (I : Instance n m) (π : Fin n ≃ Fin n) (T : ℝ) (hT0 : 0 ≤ T) :
    ∀ k : ℕ, (∀ i : Fin n, (i : ℕ) < k → I.r (π i) ≤ T) →
      (∀ ν, (listRun I π k).2 ≤ max T ((listRun I π k).1 ν)) ∧
      ∑ ν, max ((listRun I π k).1 ν) T ≤
        m * T + ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), I.p (π i) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun ν => ?_, ?_⟩
    · simp [listRun, hT0]
    · simp [listRun, hT0]
  | succ k ih =>
    intro hr
    obtain ⟨ha, hb⟩ := ih (fun i hi => hr i (by omega))
    by_cases h : k < n
    · obtain ⟨μ, hμ, he⟩ := aux_lsa_step I π k h
      rw [he]
      set f := (listRun I π k).1 with hf
      set L := (listRun I π k).2 with hL
      set j := π ⟨k, h⟩ with hj
      have hrj : I.r j ≤ T := hr ⟨k, h⟩ (by simp)
      have hpj : 0 < I.p j := I.p_pos j
      set s := max (max (I.r j) L) (f μ) with hs_def
      have hs : s ≤ max T (f μ) := by
        have := ha μ
        refine max_le (max_le ?_ this) (le_max_right _ _)
        exact hrj.trans (le_max_left _ _)
      refine ⟨fun ν => ?_, ?_⟩
      · dsimp only
        by_cases hν : ν = μ
        · subst hν
          rw [Function.update_self]
          exact le_max_of_le_right (by linarith)
        · rw [Function.update_of_ne hν]
          exact hs.trans (max_le_max le_rfl (hμ ν))
      · dsimp only
        have e1 : ∑ ν, max (Function.update f μ (s + I.p j) ν) T
            = max (s + I.p j) T + ∑ ν ∈ Finset.univ.erase μ, max (f ν) T := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ μ), Function.update_self]
          congr 1
          apply Finset.sum_congr rfl
          intro ν hν
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hν)]
        have e2 : ∑ ν, max (f ν) T = max (f μ) T + ∑ ν ∈ Finset.univ.erase μ, max (f ν) T :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ μ)).symm
        have hfil : Finset.univ.filter (fun i : Fin n => (i : ℕ) < k + 1)
            = insert ⟨k, h⟩ (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          omega
        have hnot : (⟨k, h⟩ : Fin n) ∉ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k) := by
          simp
        rw [hfil, Finset.sum_insert hnot, e1]
        rw [e2] at hb
        have hmx : max (s + I.p j) T ≤ max (f μ) T + I.p j := by
          refine max_le ?_ ?_
          · have : max T (f μ) = max (f μ) T := max_comm _ _
            linarith
          · linarith [le_max_right (f μ) T]
        linarith
    · have he : listRun I π (k + 1) = listRun I π k := by
        rw [listRun.eq_2, dif_neg h]
      rw [he]
      refine ⟨ha, hb.trans ?_⟩
      have : ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), I.p (π i)
          ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k + 1), I.p (π i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        · intro i _ _
          exact (I.p_pos _).le
      linarith

/-- Bound on the start time of the `k`-th job of the list. -/
lemma aux_lsa_start {n m : ℕ} (I : Instance n m) (π : Fin n ≃ Fin n) (k : Fin n) (T : ℝ)
    (hT0 : 0 ≤ T) (hr : ∀ i : Fin n, i ≤ k → I.r (π i) ≤ T) :
    listStart I π (π k) ≤
      T + (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), I.p (π i)) / m := by
  have hm : (0 : ℝ) < m := by exact_mod_cast I.m_pos
  unfold listStart
  rw [Equiv.symm_apply_apply]
  obtain ⟨μ, hμ, he⟩ := aux_lsa_step I π k k.isLt
  obtain ⟨ha, hb⟩ := aux_lsa_inv I π T hT0 k
    (fun i hi => hr i (Fin.le_iff_val_le_val.mpr hi.le))
  rw [he]
  simp only [Fin.eta]
  set f := (listRun I π k).1 with hf
  set L := (listRun I π k).2 with hL
  have hrk : I.r (π k) ≤ T := hr k le_rfl
  have hs : max (max (I.r (π k)) L) (f μ) ≤ max T (f μ) := by
    have := ha μ
    refine max_le (max_le ?_ this) (le_max_right _ _)
    exact hrk.trans (le_max_left _ _)
  have hmin : (m : ℝ) * max (f μ) T ≤ ∑ ν, max (f ν) T := by
    calc (m : ℝ) * max (f μ) T = ∑ _ν : Fin m, max (f μ) T := by simp
    _ ≤ _ := Finset.sum_le_sum (fun ν _ => max_le_max (hμ ν) le_rfl)
  have h2 : max (f μ) T ≤ T +
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), I.p (π i)) / m := by
    rw [← sub_nonneg]
    have h3 : (m : ℝ) * (max (f μ) T) ≤ m * T +
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), I.p (π i) := hmin.trans hb
    have h4 : T + (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), I.p (π i)) / m
        - max (f μ) T = (m * T +
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), I.p (π i)
          - m * max (f μ) T) / m := by
      field_simp
    rw [h4]
    apply div_nonneg _ hm.le
    linarith
  have : max T (f μ) = max (f μ) T := max_comm _ _
  linarith

lemma aux_lsa_done_zero {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) (t : ℝ)
    (ht : t ≤ I.r j) : P.done j t = 0 := by
  unfold RelaxSchedule.done
  exact setIntegral_eq_zero_of_forall_eq_zero
    (fun s hs => P.released j s (lt_of_lt_of_le (Set.mem_Iio.mp hs) ht))

lemma aux_lsa_done_total {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) (T : ℝ)
    (hT : ∀ t, T ≤ t → P.ρ j t = 0) : P.done j T = I.p j / m := by
  unfold RelaxSchedule.done
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun t ht => hT t (not_lt.mp (by simpa using ht))), P.total j]

lemma aux_lsa_done_mono {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n)
    {a b : ℝ} (hab : a ≤ b) : P.done j a ≤ P.done j b := by
  unfold RelaxSchedule.done
  exact setIntegral_mono_set (P.integrable j).integrableOn
    (Filter.Eventually.of_forall (fun t => P.nonneg j t))
    (Set.Iio_subset_Iio hab).eventuallyLE

lemma aux_lsa_mem_gt {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) (t : ℝ)
    (h : I.p j / m ≤ P.done j t) : I.r j < t := by
  by_contra hc
  push Not at hc
  rw [aux_lsa_done_zero P j t hc] at h
  have : 0 < I.p j / m := div_pos (I.p_pos j) (by exact_mod_cast I.m_pos)
  linarith

lemma aux_lsa_nonempty {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) :
    Set.Nonempty {t | I.p j / m ≤ P.done j t} := by
  obtain ⟨T, hT⟩ := P.bounded j
  exact ⟨T, (aux_lsa_done_total P j T hT).ge⟩

lemma aux_lsa_bdd {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) :
    BddBelow {t | I.p j / m ≤ P.done j t} :=
  ⟨I.r j, fun t ht => (aux_lsa_mem_gt P j t ht).le⟩

lemma aux_lsa_CP_ge {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) :
    I.r j ≤ P.CP j := by
  unfold RelaxSchedule.CP
  exact le_csInf (aux_lsa_nonempty P j) (fun t ht => (aux_lsa_mem_gt P j t ht).le)

lemma aux_lsa_CP_le {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) (t : ℝ)
    (ht : I.p j / m ≤ P.done j t) : P.CP j ≤ t :=
  csInf_le (aux_lsa_bdd P j) ht

lemma aux_lsa_exists_lt {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) (ε : ℝ)
    (hε : 0 < ε) : ∃ t, t < P.CP j + ε ∧ I.p j / m ≤ P.done j t := by
  have h1 : sInf {t | I.p j / m ≤ P.done j t} < P.CP j + ε := by
    show P.CP j < P.CP j + ε
    linarith
  obtain ⟨t, ht, hlt⟩ := exists_lt_of_csInf_lt (aux_lsa_nonempty P j) h1
  exact ⟨t, hlt, ht⟩

/-- In a relaxation schedule, the jobs of `S` (all completed by time `c`) have total
processing `∑ p_j / m` at most `c`. -/
lemma aux_lsa_sum_le {n m : ℕ} {I : Instance n m} (P : RelaxSchedule I) (π : Fin n ≃ Fin n)
    (S : Finset (Fin n)) (c : ℝ) (hc0 : 0 ≤ c) (hc : ∀ i ∈ S, P.CP (π i) ≤ c) :
    ∑ i ∈ S, I.p (π i) / m ≤ c := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hsum : ∑ i ∈ S, I.p (π i) / m ≤ ∑ i ∈ S, P.done (π i) (c + ε) := by
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨t, ht1, ht2⟩ := aux_lsa_exists_lt P (π i) ε hε
    exact ht2.trans (aux_lsa_done_mono P (π i) (by linarith [hc i hi]))
  refine hsum.trans ?_
  unfold RelaxSchedule.done
  rw [← integral_finsetSum S (fun i _ => (P.integrable (π i)).integrableOn)]
  have hg0 : ∀ s, 0 ≤ ∑ i ∈ S, P.ρ (π i) s :=
    fun s => Finset.sum_nonneg (fun i _ => P.nonneg _ s)
  have hg1 : ∀ s, ∑ i ∈ S, P.ρ (π i) s ≤ 1 := by
    intro s
    calc ∑ i ∈ S, P.ρ (π i) s ≤ ∑ i, P.ρ (π i) s :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            (fun i _ _ => P.nonneg _ s)
      _ = ∑ j, P.ρ j s := Equiv.sum_comp π (fun j => P.ρ j s)
      _ ≤ 1 := P.capacity s
  have hgz : ∀ s, s < 0 → ∑ i ∈ S, P.ρ (π i) s = 0 :=
    fun s hs => Finset.sum_eq_zero
      (fun i _ => P.released _ s (lt_of_lt_of_le hs (I.r_nonneg _)))
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Set.Ico 0 (c + ε)) measurableSet_Iio
    (fun s hs => hs.2) (fun s hs => hgz s (by
      rcases hs with ⟨h1, h2⟩
      simp only [Set.mem_Iio, Set.mem_Ico, not_and, not_lt] at h1 h2
      by_contra hc'
      push Not at hc'
      linarith [h2 hc']))]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ico (0 : ℝ) (c + ε))
    (f := fun s => ∑ i ∈ S, P.ρ (π i) s) (C := 1) measure_Ico_lt_top
    (fun s _ => by rw [Real.norm_eq_abs, abs_of_nonneg (hg0 s)]; exact hg1 s)
  rw [Real.volume_real_Ico_of_le (by linarith), one_mul, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (by linarith)

/-- The preemptive one-machine schedule obtained from a nonpreemptive schedule by processing each
job at rate `1/m` during its execution interval. -/
noncomputable def aux_lsa_Q {n m : ℕ} (I : Instance n m) (N : Schedule I) : RelaxSchedule I where
  ρ j := Set.indicator (Set.Ico (N.S j) (N.C j)) (fun _ => (1 : ℝ) / m)
  measurable j := measurable_const.indicator measurableSet_Ico
  integrable j := by
    rw [integrable_indicator_iff measurableSet_Ico]
    exact integrableOn_const measure_Ico_lt_top.ne
  nonneg j t := Set.indicator_nonneg (fun _ _ => by positivity) t
  capacity t := by
    classical
    have hm : (0 : ℝ) < m := by exact_mod_cast I.m_pos
    simp only [Set.indicator_apply]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter (fun j => t ∈ Set.Ico (N.S j) (N.C j))).card ≤ m := by
      calc _ ≤ (Finset.univ : Finset (Fin m)).card :=
            Finset.card_le_card_of_injOn N.M (fun _ _ => Finset.mem_univ _) ?_
        _ = m := by simp
      intro i hi j hj hij
      by_contra hne
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Set.mem_Ico] at hi hj
      unfold Schedule.C at hi hj
      rcases N.noOverlap i j hij hne with h | h <;> linarith [hi.1, hi.2, hj.1, hj.2]
    calc ((Finset.univ.filter (fun j => t ∈ Set.Ico (N.S j) (N.C j))).card : ℝ) * (1 / m)
        ≤ m * (1 / m) := by
          gcongr
      _ = 1 := by field_simp
  released j t ht := Set.indicator_of_notMem (fun h : t ∈ Set.Ico (N.S j) (N.C j) => by
    have := N.released j
    have := h.1
    linarith) _
  total j := by
    have hm : (0 : ℝ) < m := by exact_mod_cast I.m_pos
    rw [integral_indicator measurableSet_Ico, setIntegral_const,
      Real.volume_real_Ico_of_le (by unfold Schedule.C; linarith [I.p_pos j]), smul_eq_mul]
    unfold Schedule.C
    field_simp
    ring
  bounded j := ⟨N.C j, fun t ht => Set.indicator_of_notMem
    (fun h : t ∈ Set.Ico (N.S j) (N.C j) => by
    have := h.2
    linarith) _⟩

lemma aux_lsa_Q_CP {n m : ℕ} (I : Instance n m) (N : Schedule I) (j : Fin n) :
    (aux_lsa_Q I N).CP j ≤ N.C j :=
  aux_lsa_CP_le _ j _ (aux_lsa_done_total _ j (N.C j) (fun t ht => by
    show Set.indicator (Set.Ico (N.S j) (N.C j)) (fun _ => (1 : ℝ) / m) t = 0
    exact Set.indicator_of_notMem (fun h : t ∈ Set.Ico (N.S j) (N.C j) => by
      have := h.2
      linarith) _)).ge


theorem dlcb_core {n m : ℕ} (I : Instance n m)
    (π : Fin n ≃ Fin n) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I)
    (hD : IsDelayListSchedule I π β D) (i : Fin n) :
    D.C i ≤ (1 + β) * (∑ k ∈ Finset.univ.filter (fun k => π.symm k ≤ π.symm i), I.p k) / m
      + (1 + 1 / β) * (I.r i + I.p i) - I.p i / β := by
  have hm : (0 : ℝ) < m := by exact_mod_cast I.m_pos
  set X := ∑ k ∈ Finset.univ.filter (fun k => π.symm k ≤ π.symm i), I.p k with hX
  have h1 : (m : ℝ) * D.S i ≤ (1 + β) * X + (m : ℝ) * I.r i + (m : ℝ) * I.r i / β :=
    aux_dlb_job hβ D hD i
  have h3 : D.S i ≤ (1 + β) * X / m + I.r i + I.r i / β := by
    have e : (m : ℝ) * ((1 + β) * X / m + I.r i + I.r i / β) =
        (1 + β) * X + (m : ℝ) * I.r i + (m : ℝ) * I.r i / β := by
      field_simp
    have h4 : (m : ℝ) * D.S i ≤ (m : ℝ) * ((1 + β) * X / m + I.r i + I.r i / β) := by
      rw [e]; exact h1
    exact le_of_mul_le_mul_left h4 hm
  have e2 : (1 + 1 / β) * (I.r i + I.p i) - I.p i / β = I.r i + I.r i / β + I.p i := by
    field_simp; ring
  unfold DelayListRun.C
  linarith

theorem dlrb_core {n m : ℕ} (I : Instance n m)
    (P1 : RelaxSchedule I) (hP1 : P1.IsOptimal) (π : Fin n ≃ Fin n)
    (hπ : IsCompletionOrder P1 π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I)
    (hD : IsDelayListSchedule I π β D) (Nstar : Schedule I) :
    ∑ j, D.C j ≤ (2 + β) * ∑ j, Nstar.C j + 1 / β * ∑ j, I.r j := by
  have hsum : ∑ j, D.C j ≤ (1 + β) * ∑ j, P1.CP j + ∑ j, I.r j + (∑ j, I.r j) / β
      + ∑ j, I.p j := by
    calc ∑ j, D.C j ≤ ∑ j, ((1 + β) * P1.CP j + I.r j + I.r j / β + I.p j) :=
          Finset.sum_le_sum fun j _ => aux_dlb_jobC I P1 π hπ β hβ D hD j
      _ = (1 + β) * ∑ j, P1.CP j + ∑ j, I.r j + (∑ j, I.r j) / β + ∑ j, I.p j := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.mul_sum, Finset.sum_div]
  have hCP := aux_dlb_rlb I P1 hP1 Nstar
  have hrp : ∑ j, I.r j + ∑ j, I.p j ≤ ∑ j, Nstar.C j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => by
      unfold Schedule.C
      linarith [Nstar.released j]
  have hb : (1 + β) * ∑ j, P1.CP j ≤ (1 + β) * ∑ j, Nstar.C j :=
    mul_le_mul_of_nonneg_left hCP (by linarith)
  have e : (∑ j, I.r j) / β = 1 / β * ∑ j, I.r j := by ring
  nlinarith

theorem lsa_sum_core {n m : ℕ} (I : Instance n m) (P1 : RelaxSchedule I)
    (hP1 : P1.IsOptimal) (π : Fin n ≃ Fin n) (hπ : IsCompletionOrder P1 π)
    (Nstar : Schedule I) :
    ∑ j, listCompletion I π j ≤ 2 * ∑ j, Nstar.C j + ∑ j, I.p j := by
  classical
  have hm : (0 : ℝ) < m := by exact_mod_cast I.m_pos
  have hjob : ∀ k : Fin n,
      listCompletion I π (π k) ≤ 2 * P1.CP (π k) + (1 - 1 / (m : ℝ)) * I.p (π k) := by
    intro k
    have hT0 : 0 ≤ P1.CP (π k) := (I.r_nonneg _).trans (aux_lsa_CP_ge P1 _)
    have hr : ∀ i : Fin n, i ≤ k → I.r (π i) ≤ P1.CP (π k) :=
      fun i hi => (aux_lsa_CP_ge P1 _).trans (hπ i k hi)
    have hst := aux_lsa_start I π k _ hT0 hr
    have hsum := aux_lsa_sum_le P1 π (Finset.univ.filter (fun i : Fin n => i ≤ k)) _ hT0
      (fun i hi => hπ i k (by simpa using hi))
    have hfil : Finset.univ.filter (fun i : Fin n => i ≤ k)
        = insert k (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff,
        Fin.le_iff_val_le_val]
      omega
    rw [hfil, Finset.sum_insert (by simp)] at hsum
    rw [Finset.sum_div] at hst
    unfold listCompletion
    have : (1 - 1 / (m : ℝ)) * I.p (π k) = I.p (π k) - I.p (π k) / m := by ring
    linarith
  have hQ : ∑ j, P1.CP j ≤ ∑ j, Nstar.C j :=
    (hP1 (aux_lsa_Q I Nstar)).trans (Finset.sum_le_sum (fun j _ => aux_lsa_Q_CP I Nstar j))
  have h1m : 1 - 1 / (m : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (m : ℝ) := by positivity
    linarith
  have hp0 : 0 ≤ ∑ j, I.p j := Finset.sum_nonneg (fun j _ => (I.p_pos j).le)
  calc ∑ j, listCompletion I π j = ∑ k, listCompletion I π (π k) := (Equiv.sum_comp π _).symm
    _ ≤ ∑ k, (2 * P1.CP (π k) + (1 - 1 / (m : ℝ)) * I.p (π k)) :=
        Finset.sum_le_sum (fun k _ => hjob k)
    _ = 2 * ∑ k, P1.CP (π k) + (1 - 1 / (m : ℝ)) * ∑ k, I.p (π k) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = 2 * ∑ j, P1.CP j + (1 - 1 / (m : ℝ)) * ∑ j, I.p j := by
        rw [Equiv.sum_comp π P1.CP, Equiv.sum_comp π I.p]
    _ ≤ 2 * ∑ j, Nstar.C j + 1 * ∑ j, I.p j := by
        gcongr
    _ = 2 * ∑ j, Nstar.C j + ∑ j, I.p j := by ring

theorem tsta_core {n m : ℕ} (I : Instance n m) (P1 : RelaxSchedule I)
    (hP1 : P1.IsOptimal) (π : Fin n ≃ Fin n) (hπ : IsCompletionOrder P1 π)
    (D : DelayListRun I) (hD : IsDelayListSchedule I π (Real.sqrt (3 - 2 * Real.sqrt 2)) D)
    (Nstar : Schedule I) :
    min (∑ j, listCompletion I π j) (∑ j, D.C j) ≤ 2 * Real.sqrt 2 * ∑ j, Nstar.C j := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2p : 1 < Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hβeq : Real.sqrt (3 - 2 * Real.sqrt 2) = Real.sqrt 2 - 1 := by
    rw [show 3 - 2 * Real.sqrt 2 = (Real.sqrt 2 - 1) ^ 2 by nlinarith]
    exact Real.sqrt_sq (by linarith)
  rw [hβeq] at hD
  set s := Real.sqrt 2 with hs
  have hβ : 0 < s - 1 := by linarith
  have hC0 : 0 ≤ ∑ j, Nstar.C j := Finset.sum_nonneg (fun j _ => by
    unfold Schedule.C; linarith [Nstar.released j, I.r_nonneg j, I.p_pos j])
  rcases le_or_gt (∑ j, I.p j) ((2 * s - 2) * ∑ j, Nstar.C j) with h | h
  · refine (min_le_left _ _).trans ?_
    have := lsa_sum_core I P1 hP1 π hπ Nstar
    linarith
  · refine (min_le_right _ _).trans ?_
    have h1 := dlrb_core I P1 hP1 π hπ (s - 1) hβ D hD Nstar
    have hrp : ∑ j, I.r j + ∑ j, I.p j ≤ ∑ j, Nstar.C j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j _ => by
        unfold Schedule.C
        linarith [Nstar.released j]
    have hr : ∑ j, I.r j ≤ (3 - 2 * s) * ∑ j, Nstar.C j := by linarith
    have hr' : 1 / (s - 1) * ∑ j, I.r j ≤ (s - 1) * ∑ j, Nstar.C j := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hβ]
      have : (3 - 2 * s) = (s - 1) * (s - 1) := by nlinarith
      rw [this] at hr
      linarith
    linarith

end AvgCompletionSched.ParallelRelease

open AvgCompletionSched.ParallelRelease


theorem solution {n m : ℕ} (I : Instance n m) (hm : 2 ≤ m)
    (π : Fin n ≃ Fin n) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I)
    (hD : IsDelayListSchedule I π β D) (i : Fin n) :
    D.C i ≤ (1 + β) * (∑ k ∈ Finset.univ.filter (fun k => π.symm k ≤ π.symm i), I.p k) / m
      + (1 + 1 / β) * (I.r i + I.p i) - I.p i / β := by
  exact dlcb_core I π β hβ D hD i
