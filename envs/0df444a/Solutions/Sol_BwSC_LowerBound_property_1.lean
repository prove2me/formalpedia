-- Prove2me | solution 1 for BwSC.LowerBound.property_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T03:16:43.855137+00:00
-- url     : https://prove2.me/submissions/461fb0c0-c3f5-4a04-8987-3e7393e907ee

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound.P1Aux

lemma act_of_out {K T : ℕ} (h : BanditHistory K T) (t : ℕ) (ht : ¬ (1 ≤ t ∧ t ≤ T)) :
    act h t = none := by
  simp [act, actA, ht]

lemma act_of_in {K T : ℕ} (h : BanditHistory K T) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ T) :
    act h t = some ((h ⟨t - 1, by omega⟩).1) := by
  simp [act, actA, ht, actions]

/-- The stopped record, read round by round. -/
lemma act_censor {K T : ℕ} (lo hi : ℕ) (k : Fin K) (h : BanditHistory K T) (t : ℕ)
    (ht : 1 ≤ t ∧ t ≤ T) :
    act (stopCensor lo hi k h) t =
      if (t < lo ∨ (t ≤ hi ∧ act h t ≠ some k ∧ ∀ s, lo ≤ s → s < t → act h s ≠ some k))
      then act h t else some k := by
  rw [act_of_in _ t ht, act_of_in h t ht]
  have hidx : ((⟨t - 1, by omega⟩ : Fin T).val + 1) = t := by simp; omega
  have hiff : keepRound lo hi k (actions h) ⟨t - 1, by omega⟩ ↔
      (t < lo ∨ (t ≤ hi ∧ some ((h ⟨t - 1, by omega⟩).1) ≠ some k ∧
        ∀ s, lo ≤ s → s < t → act h s ≠ some k)) := by
    unfold keepRound
    rw [hidx]
    simp only [Finset.mem_Ico, ne_eq, Option.some.injEq]
    constructor
    · rintro (h1 | ⟨h1, h2, h3⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2, fun s hs1 hs2 => h3 s ⟨hs1, hs2⟩⟩
    · rintro (h1 | ⟨h1, h2, h3⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2, fun s hs => h3 s hs.1 hs.2⟩
  unfold stopCensor
  by_cases hk : keepRound lo hi k (actions h) ⟨t - 1, by omega⟩
  · rw [if_pos hk, if_pos (hiff.mp hk)]
  · rw [if_neg hk, if_neg (fun hc => hk (hiff.mpr hc))]

lemma act_censor_out {K T : ℕ} (lo hi : ℕ) (k : Fin K) (h : BanditHistory K T) (t : ℕ)
    (ht : ¬ (1 ≤ t ∧ t ≤ T)) : act (stopCensor lo hi k h) t = act h t := by
  rw [act_of_out _ t ht, act_of_out h t ht]

/-- Window invariance: `k` is not chosen in `[lo, hi]` by the record iff by the history. -/
lemma notChosen_censor {K T : ℕ} (lo hi : ℕ) (k : Fin K) (h : BanditHistory K T) :
    notChosen (stopCensor lo hi k h) k lo hi ↔ notChosen h k lo hi := by
  unfold notChosen
  constructor
  · intro H t ht1 ht2 hc
    by_cases ht : 1 ≤ t ∧ t ≤ T
    · have := H t ht1 ht2
      rw [act_censor lo hi k h t ht] at this
      split_ifs at this with hcond
      · exact this hc
      · exact this rfl
    · rw [act_of_out h t ht] at hc; exact absurd hc (by simp)
  · intro H t ht1 ht2
    by_cases ht : 1 ≤ t ∧ t ≤ T
    · rw [act_censor lo hi k h t ht]
      rw [if_pos (Or.inr ⟨ht2, H t ht1 ht2, fun s hs1 hs2 => H s hs1 (by omega)⟩)]
      exact H t ht1 ht2
    · rw [act_of_out _ t ht]; simp

lemma switchCost_agree {K T : ℕ} (h h' : BanditHistory K T) (m : ℕ)
    (hag : ∀ t, t ≤ m → act h t = act h' t) (n : ℕ) (hn : n ≤ m) :
    switchCost h 1 n = switchCost h' 1 n := by
  unfold switchCost
  congr 1
  apply Finset.filter_congr
  intro t _
  constructor
  · rintro ⟨a1, a2, a3, a4, a5⟩
    refine ⟨a1, a2, a3, a4, ?_⟩
    rwa [← hag t (by omega), ← hag (t + 1) (by omega)]
  · rintro ⟨a1, a2, a3, a4, a5⟩
    refine ⟨a1, a2, a3, a4, ?_⟩
    rwa [hag t (by omega), hag (t + 1) (by omega)]

lemma stopTime_agree {K T : ℕ} (S : ℕ) (h h' : BanditHistory K T) (m : ℕ)
    (hag : ∀ t, t ≤ m → act h t = act h' t) (hm : stopTime S h ≤ m) :
    stopTime S h' = stopTime S h := by
  have hmem : ∀ t, t ≤ m →
      (t ∈ (Finset.Icc 1 T).filter (fun t => switchCost h 1 t = S) ↔
        t ∈ (Finset.Icc 1 T).filter (fun t => switchCost h' 1 t = S)) := by
    intro t ht
    simp only [Finset.mem_filter, switchCost_agree h h' m hag t ht]
  unfold stopTime at hm ⊢
  by_cases hne : ((Finset.Icc 1 T).filter (fun t => switchCost h 1 t = S)).Nonempty
  · rw [dif_pos hne] at hm ⊢
    set τ := ((Finset.Icc 1 T).filter (fun t => switchCost h 1 t = S)).min' hne
    have hτ : τ ∈ (Finset.Icc 1 T).filter (fun t => switchCost h' 1 t = S) :=
      (hmem τ hm).mp (Finset.min'_mem _ _)
    have hne' : ((Finset.Icc 1 T).filter (fun t => switchCost h' 1 t = S)).Nonempty := ⟨τ, hτ⟩
    rw [dif_pos hne']
    apply le_antisymm
    · exact Finset.min'_le _ _ hτ
    · have h1 := Finset.min'_le _ _ hτ
      have h2 := Finset.min'_mem _ hne'
      exact Finset.min'_le _ _ ((hmem _ (h1.trans hm)).mpr h2)
  · rw [dif_neg hne] at hm ⊢
    have hne' : ¬ ((Finset.Icc 1 T).filter (fun t => switchCost h' 1 t = S)).Nonempty := by
      rintro ⟨t, ht⟩
      have htT : t ≤ T := (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).2
      exact hne ⟨t, (hmem t (by omega)).mpr ht⟩
    rw [dif_neg hne']

lemma act_stopTime_le {K T : ℕ} (S : ℕ) (h : BanditHistory K T) (k : Fin K)
    (hk : act h (stopTime S h) = some k) : 1 ≤ stopTime S h ∧ stopTime S h ≤ T := by
  by_contra hc
  rw [act_of_out h _ hc] at hk
  exact absurd hk (by simp)

/-- Invariance of the last first-class event `E^{(1)}_{q+2,k}`. -/
lemma last_event_censor {K T : ℕ} (S lo hi : ℕ) (k : Fin K) (h : BanditHistory K T) :
    (stopTime S (stopCensor lo hi k h) ≤ hi ∧ act (stopCensor lo hi k h)
        (stopTime S (stopCensor lo hi k h)) = some k ∧
      notChosen (stopCensor lo hi k h) k lo (stopTime S (stopCensor lo hi k h) - 1)) ↔
    (stopTime S h ≤ hi ∧ act h (stopTime S h) = some k ∧
      notChosen h k lo (stopTime S h - 1)) := by
  set h' := stopCensor lo hi k h with hh'
  constructor
  · rintro ⟨H1, H2, H3⟩
    set τ := stopTime S h' with hτ
    have hτT := act_stopTime_le S h' k H2
    -- the record and the history agree up to round τ
    have hag : ∀ t, t ≤ τ → act h' t = act h t := by
      have hlt : ∀ t, t < τ → act h' t = act h t := by
        intro t ht
        by_cases hin : 1 ≤ t ∧ t ≤ T
        · rw [hh', act_censor lo hi k h t hin]
          split_ifs with hc
          · rfl
          · exfalso
            by_cases htl : t < lo
            · exact hc (Or.inl htl)
            · have := H3 t (by omega) (by omega)
              rw [hh', act_censor lo hi k h t hin, if_neg hc] at this
              exact this rfl
        · rw [hh', act_censor_out lo hi k h t hin]
      intro t ht
      rcases Nat.lt_or_ge t τ with htl | htg
      · exact hlt t htl
      · have hte : t = τ := le_antisymm ht htg
        rw [hte, hh', act_censor lo hi k h _ hτT]
        split_ifs with hc
        · rfl
        · by_contra hne
          apply hc
          by_cases htl : τ < lo
          · exact Or.inl htl
          · refine Or.inr ⟨H1, fun hk => hne hk.symm, fun s hs1 hs2 => ?_⟩
            rw [← hlt s hs2]
            exact H3 s hs1 (by omega)
    have hst : stopTime S h = τ := stopTime_agree S h' h τ hag le_rfl
    rw [hst]
    refine ⟨H1, ?_, fun t ht1 ht2 => ?_⟩
    · rw [← hag τ le_rfl]; exact H2
    · rw [← hag t (by omega)]; exact H3 t ht1 ht2
  · rintro ⟨H1, H2, H3⟩
    set τ := stopTime S h with hτ
    have hτT := act_stopTime_le S h k H2
    have hag : ∀ t, t ≤ τ → act h t = act h' t := by
      intro t ht
      by_cases hin : 1 ≤ t ∧ t ≤ T
      · rw [hh', act_censor lo hi k h t hin]
        rcases Nat.lt_or_ge t τ with htl | htg
        · by_cases hlo : t < lo
          · rw [if_pos (Or.inl hlo)]
          · rw [if_pos (Or.inr ⟨by omega, H3 t (by omega) (by omega),
              fun s hs1 hs2 => H3 s hs1 (by omega)⟩)]
        · have hte : t = τ := le_antisymm ht htg
          subst hte
          split_ifs
          · rfl
          · exact H2
      · rw [hh', act_censor_out lo hi k h t hin]
    have hst : stopTime S h' = τ := stopTime_agree S h h' τ hag le_rfl
    rw [hst]
    refine ⟨H1, ?_, fun t ht1 ht2 => ?_⟩
    · rw [← hag τ le_rfl]; exact H2
    · rw [← hag t (by omega)]; exact H3 t ht1 ht2

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

lemma measurableSet_E2 (S K T j : ℕ) (k : Fin K) : MeasurableSet (E2 S K T j k) := by
  apply measurableSet_of_actions
  intro h h' e hh
  simp only [E2, notChosen, Set.mem_setOf_eq] at hh ⊢
  rw [← act_congr e]; exact hh

lemma preimage_E1 {K : ℕ} (S T j : ℕ) (k : Fin K) (hj : j ≤ qIdx S K + 2) :
    stopCensor (lo1 S K T j) (hi1 S K T j) k ⁻¹' E1 S K T j k = E1 S K T j k := by
  ext h
  simp only [Set.mem_preimage]
  unfold E1 lo1 hi1
  by_cases h2 : j = qIdx S K + 2
  · rw [if_pos h2, if_pos (by omega), if_pos (by omega)]
    simp only [Set.mem_setOf_eq]
    exact last_event_censor S _ _ k h
  · rw [if_neg h2]
    by_cases h1 : j = qIdx S K + 1
    · rw [if_pos h1, if_pos (by omega), if_pos (by omega)]
      simp only [Set.mem_setOf_eq]
      exact notChosen_censor _ _ k h
    · rw [if_neg h1]
      by_cases h3 : qIdx S K + 1 ≤ j
      · omega
      · rw [if_neg h3, if_neg h3]
        simp only [Set.mem_setOf_eq]
        exact notChosen_censor _ _ k h

end BwSC.LowerBound.P1Aux

namespace BwSC.LowerBound.P1Aux

lemma preimage_E2 {K : ℕ} (S T j : ℕ) (k : Fin K) :
    stopCensor (lo2 S K T j) (hi2 S K T j) k ⁻¹' E2 S K T j k = E2 S K T j k := by
  ext h
  simp only [Set.mem_preimage, E2, lo2, hi2, Set.mem_setOf_eq]
  exact notChosen_censor _ _ k h

end BwSC.LowerBound.P1Aux

open BwSC.LowerBound BwSC.LowerBound.P1Aux in
theorem solution {K S T : ℕ} (π : BanditPolicy K) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 (qIdx S K + 2)) (k : Fin K) :
    stopCensor (lo1 S K T j) (hi1 S K T j) k ⁻¹' E1 S K T j k = E1 S K T j k ∧
    artP1 π S T j k (E1 S K T j k) =
      (banditMeasure (gaussianBandit (envAlt1 S K T j k)) π T) (E1 S K T j k) ∧
    artQ1 π S T j k (E1 S K T j k) =
      (banditMeasure (gaussianBandit (0 : Fin K → ℝ)) π T) (E1 S K T j k) ∧
    stopCensor (lo2 S K T j) (hi2 S K T j) k ⁻¹' E2 S K T j k = E2 S K T j k ∧
    artP2 π S T j k (E2 S K T j k) =
      (banditMeasure (gaussianBandit (envAlt2 S K T j k)) π T) (E2 S K T j k) ∧
    artQ2 π S T j k (E2 S K T j k) =
      (banditMeasure (gaussianBandit (0 : Fin K → ℝ)) π T) (E2 S K T j k) := by
  have hj' : j ≤ qIdx S K + 2 := (Finset.mem_Icc.mp hj).2
  have p1 := preimage_E1 S T j k hj'
  have p2 := preimage_E2 S T j k
  refine ⟨p1, ?_, ?_, p2, ?_, ?_⟩
  · unfold artP1
    rw [Measure.map_apply (measurable_stopCensor _ _ _) (measurableSet_E1 _ _ _ _ _), p1]
  · unfold artQ1
    rw [Measure.map_apply (measurable_stopCensor _ _ _) (measurableSet_E1 _ _ _ _ _), p1]
  · unfold artP2
    rw [Measure.map_apply (measurable_stopCensor _ _ _) (measurableSet_E2 _ _ _ _ _), p2]
  · unfold artQ2
    rw [Measure.map_apply (measurable_stopCensor _ _ _) (measurableSet_E2 _ _ _ _ _), p2]
