-- Prove2me | solution 1 for FulkersonPERT.Bounds.meanCPL_le_fNum_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:46:55.778904+00:00
-- url     : https://prove2.me/submissions/918ecb26-497c-4123-96c4-1fbfafaa0ecd

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes
import Definitions.Def_FulkersonPERT_Bounds_Model



namespace FulkersonPERT.Bounds
open CriticalPath.Events

theorem attach_sup'_c {α : Type*} [DecidableEq α] (s : Finset α) (h : s.attach.Nonempty)
    (h' : s.Nonempty) (f : α → ℝ) :
    s.attach.sup' h (fun i => f i.1) = s.sup' h' f := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun i _ => Finset.le_sup' f i.2)
  · exact Finset.sup'_le _ _ (fun i hi => Finset.le_sup' (fun i : s => f i.1) (b := ⟨i, hi⟩)
      (Finset.mem_attach _ _))

theorem earliest_zero_c {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) :
    earliest N y 0 = 0 := by
  rw [earliest]; simp

theorem earliest_eq_c {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) (hj : j ≠ 0) :
    earliest N y j = (N.pred j).sup' (N.pred_nonempty hj) (fun i => y i j + earliest N y i) := by
  rw [earliest, dif_neg hj]
  exact attach_sup'_c (N.pred j) _ _ (fun i => y i j + earliest N y i)

theorem fNum_zero_c {n : ℕ} (N : ProjectNetwork n) (D : BundleDist n) : fNum N D 0 = 0 := by
  rw [fNum]; simp

theorem fNum_eq_c {n : ℕ} (N : ProjectNetwork n) (D : BundleDist n)
    (j : Fin (n + 1)) (hj : j ≠ 0) :
    fNum N D j = ∑ v ∈ D.supp j, D.p j v *
      (N.pred j).sup' (N.pred_nonempty hj) (fun i => fNum N D i + v i) := by
  rw [fNum, dif_neg hj]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [attach_sup'_c (N.pred j) _ _ (fun i => fNum N D i + v i)]

theorem pathLength_cons_cons_c {n : ℕ} (y : Fin (n + 1) → Fin (n + 1) → ℝ) (a b : Fin (n + 1))
    (l : List (Fin (n + 1))) : pathLength y (a :: b :: l) = y a b + pathLength y (b :: l) := by
  simp [pathLength]

theorem pathLength_single_c {n : ℕ} (y : Fin (n + 1) → Fin (n + 1) → ℝ) (a : Fin (n + 1)) :
    pathLength y [a] = 0 := by simp [pathLength]

theorem pathLength_snoc_c {n : ℕ} (y : Fin (n + 1) → Fin (n + 1) → ℝ) (i k : Fin (n + 1))
    (q : List (Fin (n + 1))) :
    pathLength y (q ++ [k, i]) = pathLength y (q ++ [k]) + y k i := by
  induction q with
  | nil => simp [pathLength]
  | cons a t ih =>
    cases t with
    | nil => simp [pathLength]
    | cons b t =>
      have := ih
      simp only [List.cons_append] at this ⊢
      rw [pathLength_cons_cons_c, pathLength_cons_cons_c, this]; ring

theorem le_earliest_of_path_c {n : ℕ} (N : ProjectNetwork n)
    (y : Fin (n + 1) → Fin (n + 1) → ℝ) :
    ∀ (m : ℕ) (p : List (Fin (n + 1))) (i : Fin (n + 1)), p.length = m → IsPathTo N p i →
      pathLength y p ≤ earliest N y i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p i hm ⟨h0, hl, hc⟩
    rcases List.eq_nil_or_concat p with rfl | ⟨q, a, rfl⟩
    · simp at h0
    have ha : a = i := by simpa using hl
    subst ha
    rcases List.eq_nil_or_concat q with rfl | ⟨q', k, rfl⟩
    · simp at h0
      subst h0
      simp [pathLength, earliest_zero_c]
    · have hc' : (q' ++ [k] ++ [a]).IsChain (fun a b => (a, b) ∈ N.P) := by
        simpa only [List.concat_eq_append] using hc
      have hki : (k, a) ∈ N.P := by
        have := (List.isChain_append.1 hc').2.2 k (by simp) a (by simp)
        exact this
      have hq : IsPathTo N (q' ++ [k]) k := by
        refine ⟨?_, by simp, ?_⟩
        · simpa [List.concat_eq_append] using h0
        · exact (List.isChain_append.1 hc').1
      have hne : a ≠ 0 := by
        intro h
        have := N.label_lt _ hki
        simp [h] at this
      have := ih (q' ++ [k]).length (by simp [List.concat_eq_append] at hm ⊢; omega) _ k rfl hq
      simp only [List.concat_eq_append]
      rw [List.append_assoc]
      simp only [List.singleton_append, List.cons_append]
      have e1 := pathLength_snoc_c y a k q'
      simp only [List.append_assoc, List.cons_append, List.nil_append] at e1 ⊢
      rw [e1, earliest_eq_c N y a hne]
      calc _ ≤ earliest N y k + y k a := by linarith
        _ = y k a + earliest N y k := by ring
        _ ≤ _ := Finset.le_sup' (fun i => y i a + earliest N y i) ((N.mem_pred).2 hki)

theorem exists_path_c {n : ℕ} (N : ProjectNetwork n)
    (y : Fin (n + 1) → Fin (n + 1) → ℝ) :
    ∀ (m : ℕ) (i : Fin (n + 1)), i.val = m →
      ∃ p, IsPathTo N p i ∧ pathLength y p = earliest N y i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i hi
    by_cases h : i = 0
    · subst h
      exact ⟨[0], ⟨by simp, by simp, by simp⟩, by simp [pathLength, earliest_zero_c]⟩
    · obtain ⟨i0, hi0, he⟩ := Finset.exists_mem_eq_sup' (N.pred_nonempty h)
        (fun k => y k i + earliest N y k)
      have hlt := N.lt_of_mem_pred hi0
      obtain ⟨p0, ⟨h0, hl, hc⟩, hp0⟩ := ih i0.val (by rw [← hi]; exact hlt) i0 rfl
      rcases List.eq_nil_or_concat p0 with rfl | ⟨q, a, rfl⟩
      · simp at h0
      have ha : a = i0 := by simpa using hl
      subst ha
      refine ⟨q ++ [a, i], ⟨?_, by simp, ?_⟩, ?_⟩
      · rcases q with _ | ⟨b, t⟩
        · simpa using h0
        · simpa using h0
      · have h1 : (q ++ [a]).IsChain (fun a b => (a, b) ∈ N.P) := by
          simpa [List.concat_eq_append] using hc
        have : (q ++ [a] ++ [i]).IsChain (fun a b => (a, b) ∈ N.P) :=
          List.IsChain.append h1 (by simp) (by simp; exact (N.mem_pred).1 hi0)
        simpa using this
      · simp only [List.concat_eq_append] at hp0
        rw [pathLength_snoc_c, hp0, earliest_eq_c N y i h, he]; ring

theorem earliest_isGreatest_c {n : ℕ} (N : ProjectNetwork n)
    (y : Fin (n + 1) → Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    IsGreatest {L : ℝ | ∃ p : List (Fin (n + 1)), IsPathTo N p i ∧ L = pathLength y p}
      (earliest N y i) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hp, h⟩ := exists_path_c N y i.val i rfl
    exact ⟨p, hp, h.symm⟩
  · rintro L ⟨p, hp, rfl⟩
    exact le_earliest_of_path_c N y _ p i rfl hp


theorem earliest_eq_of_eqOn_c {n : ℕ} (N : ProjectNetwork n)
    (y y' : Fin (n + 1) → Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (h : ∀ a b, (a, b) ∈ N.P → b ≤ i → y a b = y' a b) :
    earliest N y i = earliest N y' i := by
  induction' hm : i.val using Nat.strong_induction_on with m ih generalizing i
  by_cases h0 : i = 0
  · subst h0; rw [earliest_zero_c, earliest_zero_c]
  · rw [earliest_eq_c N y i h0, earliest_eq_c N y' i h0]
    apply Finset.sup'_congr _ rfl
    intro k hk
    have hki := (N.mem_pred).1 hk
    have hlt := N.lt_of_mem_pred hk
    rw [h k i hki le_rfl, ih k.val (by rw [← hm]; exact hlt) k
      (fun a b hab hb => h a b hab (hb.trans hlt.le)) rfl]

theorem f_ge_max_add_mean_c {n : ℕ} (N : ProjectNetwork n) (D : BundleDist n) (hD : D.IsProb)
    (j : Fin (n + 1)) (hj : j ≠ 0) :
    (N.pred j).sup' (N.pred_nonempty hj) (fun i => fNum N D i + meanLength D i j) ≤
      fNum N D j := by
  apply Finset.sup'_le
  intro k hk
  rw [fNum_eq_c N D j hj]
  have h1 : fNum N D k + meanLength D k j = ∑ v ∈ D.supp j, D.p j v * (fNum N D k + v k) := by
    simp only [meanLength, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hD.2 j]
    ring
  rw [h1]
  apply Finset.sum_le_sum
  intro v hv
  exact mul_le_mul_of_nonneg_left
    (Finset.le_sup' (fun i => fNum N D i + v i) hk) (hD.1 j v hv)

theorem meanCPL_le_fNum_step_c {n : ℕ} (N : ProjectNetwork n) (D : BundleDist n) (hD : D.IsProb)
    (j : Fin (n + 1)) (ih : ∀ k : Fin (n + 1), k < j → meanCPL N D k ≤ fNum N D k) :
    meanCPL N D j ≤ fNum N D j := by
  by_cases hj : j = 0
  · subst hj; simp [meanCPL, earliest_zero_c, fNum_zero_c]
  · unfold meanCPL
    rw [earliest_eq_c N _ j hj]
    apply Finset.sup'_le
    intro k hk
    have h1 := ih k (N.lt_of_mem_pred hk)
    have h2 := f_ge_max_add_mean_c N D hD j hj
    have h3 := Finset.le_sup' (fun i => fNum N D i + meanLength D i j) hk
    unfold meanCPL at h1
    linarith


section ind
open Classical

theorem prob_nonneg_c {n : ℕ} (D : BundleDist n) (hD : D.IsProb)
    {ω : Fin (n + 1) → Fin (n + 1) → ℝ} (hω : ω ∈ Fintype.piFinset D.supp) :
    0 ≤ prob D ω := by
  unfold prob
  exact Finset.prod_nonneg (fun k _ => hD.1 k _ (Fintype.mem_piFinset.1 hω k))

theorem prob_sum_c {n : ℕ} (D : BundleDist n) (hD : D.IsProb) :
    ∑ ω ∈ Fintype.piFinset D.supp, prob D ω = 1 := by
  unfold prob
  rw [← Finset.prod_univ_sum (fun k => D.supp k) (fun k v => D.p k v)]
  exact Finset.prod_eq_one (fun k _ => hD.2 k)

theorem ind_c {n : ℕ} (D : BundleDist n) (hD : D.IsProb) (j : Fin (n + 1))
    (G : (Fin (n + 1) → ℝ) → (Fin (n + 1) → Fin (n + 1) → ℝ) → ℝ)
    (hG : ∀ v ω w, G v (Function.update ω j w) = G v ω) :
    ∑ ω ∈ Fintype.piFinset D.supp, prob D ω * G (ω j) ω =
      ∑ v ∈ D.supp j, D.p j v * ∑ ω ∈ Fintype.piFinset D.supp, prob D ω * G v ω := by
  set P := Fintype.piFinset D.supp with hP
  let K : (Fin (n + 1) → Fin (n + 1) → ℝ) → ℝ := fun ω => ∏ k ∈ Finset.univ.erase j, D.p k (ω k)
  have hprob : ∀ ω, prob D ω = D.p j (ω j) * K ω := fun ω => by
    unfold prob; rw [Finset.mul_prod_erase _ (fun k => D.p k (ω k)) (Finset.mem_univ j)]
  have hK : ∀ ω w, K (Function.update ω j w) = K ω := fun ω w => by
    apply Finset.prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  have hmaps : ∀ ω ∈ P, ω j ∈ D.supp j := fun ω hω => Fintype.mem_piFinset.1 hω j
  let S : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) → ℝ := fun v w =>
    ∑ ω ∈ P with ω j = w, K ω * G v ω
  have hA : ∀ v, ∀ w ∈ D.supp j, ∀ w' ∈ D.supp j, S v w = S v w' := by
    intro v w hw w' hw'
    apply Finset.sum_nbij' (fun ω => Function.update ω j w') (fun ω => Function.update ω j w)
    · intro ω hω
      rw [Finset.mem_filter] at hω ⊢
      refine ⟨?_, by simp⟩
      rw [hP, Fintype.mem_piFinset] at hω ⊢
      intro k
      by_cases hk : k = j
      · subst hk; simpa using hw'
      · rw [Function.update_of_ne hk]; exact hω.1 k
    · intro ω hω
      rw [Finset.mem_filter] at hω ⊢
      refine ⟨?_, by simp⟩
      rw [hP, Fintype.mem_piFinset] at hω ⊢
      intro k
      by_cases hk : k = j
      · subst hk; simpa using hw
      · rw [Function.update_of_ne hk]; exact hω.1 k
    · intro ω hω
      rw [Finset.mem_filter] at hω
      simp [hω.2]
    · intro ω hω
      rw [Finset.mem_filter] at hω
      simp [hω.2]
    · intro ω hω
      rw [hK, hG]
  have hB : ∀ F : (Fin (n + 1) → Fin (n + 1) → ℝ) → ℝ,
      ∑ ω ∈ P, F ω = ∑ w ∈ D.supp j, ∑ ω ∈ P with ω j = w, F ω := fun F =>
    (Finset.sum_fiberwise_of_maps_to hmaps F).symm
  have hC : ∀ v, ∀ w ∈ D.supp j, ∑ ω ∈ P with ω j = w, prob D ω * G v ω = D.p j w * S v w := by
    intro v w hw
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω hω
    rw [Finset.mem_filter] at hω
    rw [hprob, hω.2]; ring
  have hD' : ∀ v ∈ D.supp j, ∑ ω ∈ P, prob D ω * G v ω = S v v := by
    intro v hv
    rw [hB, Finset.sum_congr rfl (fun w hw => hC v w hw)]
    rw [Finset.sum_congr rfl (fun w hw => by rw [hA v w hw v hv])]
    rw [← Finset.sum_mul, hD.2 j, one_mul]
  calc ∑ ω ∈ P, prob D ω * G (ω j) ω
      = ∑ w ∈ D.supp j, ∑ ω ∈ P with ω j = w, prob D ω * G (ω j) ω := hB _
    _ = ∑ w ∈ D.supp j, D.p j w * S w w := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [← hC w w hw]
        apply Finset.sum_congr rfl
        intro ω hω
        rw [(Finset.mem_filter.1 hω).2]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hD' v hv]

end ind


section main
open Classical

theorem earliest_update_c {n : ℕ} (N : ProjectNetwork n) (ω : Fin (n + 1) → Fin (n + 1) → ℝ)
    (j i : Fin (n + 1)) (hij : i < j) (w : Fin (n + 1) → ℝ) :
    earliest N (arcLengths (Function.update ω j w)) i = earliest N (arcLengths ω) i := by
  apply earliest_eq_of_eqOn_c
  intro a b _ hb
  have : b ≠ j := ne_of_lt (lt_of_le_of_lt hb hij)
  simp [arcLengths, Function.update_of_ne this]

theorem sum_max_add_le_expectedLength_c {n : ℕ} (N : ProjectNetwork n) (D : BundleDist n)
    (hD : D.IsProb) (j : Fin (n + 1)) (hj : j ≠ 0) :
    ∑ v ∈ D.supp j, D.p j v *
        (N.pred j).sup' (N.pred_nonempty hj) (fun i => expectedLength N D i + v i) ≤
      expectedLength N D j := by
  have hex : ∀ v : Fin (n + 1) → ℝ, ∃ i ∈ N.pred j,
      (N.pred j).sup' (N.pred_nonempty hj) (fun i => expectedLength N D i + v i) =
        expectedLength N D i + v i := fun v =>
    Finset.exists_mem_eq_sup' (N.pred_nonempty hj) _
  choose is his hV using hex
  let G : (Fin (n + 1) → ℝ) → (Fin (n + 1) → Fin (n + 1) → ℝ) → ℝ := fun v ω =>
    v (is v) + earliest N (arcLengths ω) (is v)
  have hG : ∀ v ω w, G v (Function.update ω j w) = G v ω := by
    intro v ω w
    simp only [G]
    rw [earliest_update_c N ω j _ (N.lt_of_mem_pred (his v)) w]
  have h1 := ind_c D hD j G hG
  have h2 : ∀ v : Fin (n + 1) → ℝ, ∑ ω ∈ Fintype.piFinset D.supp, prob D ω * G v ω =
      v (is v) + expectedLength N D (is v) := by
    intro v
    simp only [G, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, prob_sum_c D hD]
    unfold expectedLength
    ring
  have h3 : ∑ ω ∈ Fintype.piFinset D.supp, prob D ω * G (ω j) ω ≤ expectedLength N D j := by
    unfold expectedLength
    apply Finset.sum_le_sum
    intro ω hω
    apply mul_le_mul_of_nonneg_left _ (prob_nonneg_c D hD hω)
    rw [earliest_eq_c N _ j hj]
    have := Finset.le_sup' (fun i => arcLengths ω i j + earliest N (arcLengths ω) i)
      (his (ω j))
    simp only [G, arcLengths]
    exact this
  refine le_trans (le_of_eq ?_) (h1 ▸ h3)
  apply Finset.sum_congr rfl
  intro v _
  rw [h2, hV]; ring

theorem fNum_le_expectedLength_step_c {n : ℕ} (N : ProjectNetwork n) (D : BundleDist n)
    (hD : D.IsProb) (j : Fin (n + 1))
    (ih : ∀ k : Fin (n + 1), k < j → fNum N D k ≤ expectedLength N D k) :
    fNum N D j ≤ expectedLength N D j := by
  by_cases hj : j = 0
  · subst hj
    rw [fNum_zero_c]
    unfold expectedLength
    apply Finset.sum_nonneg
    intro ω hω
    rw [earliest_zero_c, mul_zero]
  · rw [fNum_eq_c N D j hj]
    refine le_trans ?_ (sum_max_add_le_expectedLength_c N D hD j hj)
    apply Finset.sum_le_sum
    intro v hv
    apply mul_le_mul_of_nonneg_left _ (hD.1 j v hv)
    apply Finset.sup'_le
    intro k hk
    have := ih k (N.lt_of_mem_pred hk)
    exact le_trans (by linarith) (Finset.le_sup' (fun i => expectedLength N D i + v i) hk)

theorem expected_bounds_c {n : ℕ} (N : ProjectNetwork n) (D : BundleDist n)
    (hD : D.IsProb) :
    ∀ i : Fin (n + 1), meanCPL N D i ≤ fNum N D i ∧ fNum N D i ≤ expectedLength N D i := by
  intro i
  induction' hm : i.val using Nat.strong_induction_on with m ih generalizing i
  have ih' : ∀ k : Fin (n + 1), k < i →
      meanCPL N D k ≤ fNum N D k ∧ fNum N D k ≤ expectedLength N D k :=
    fun k hk => ih k.val (by rw [← hm]; exact hk) k rfl
  exact ⟨meanCPL_le_fNum_step_c N D hD i (fun k hk => (ih' k hk).1),
    fNum_le_expectedLength_step_c N D hD i (fun k hk => (ih' k hk).2)⟩

end main

end FulkersonPERT.Bounds

open FulkersonPERT.Bounds
open CriticalPath.Events

theorem solution {n : ℕ} (N : ProjectNetwork n) (D : BundleDist n) (hD : D.IsProb)
    (j : Fin (n + 1)) (ih : ∀ k : Fin (n + 1), k < j → meanCPL N D k ≤ fNum N D k) :
    meanCPL N D j ≤ fNum N D j := by
  exact meanCPL_le_fNum_step_c N D hD j ih
