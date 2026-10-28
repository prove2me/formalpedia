-- Prove2me | solution 1 for BitcoinHeader.mtp_mono
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:13.109899+00:00
-- url     : https://prove2.me/submissions/b414bd0c-be0f-4725-9100-2aaf83c742a2

import Definitions.Def_BitcoinHeader

open BitcoinHeader

/-- Number of elements of a list that are at least `m`. -/
private def countGe (m : Int) (l : List Int) : Nat := (l.filter fun x => decide (m ≤ x)).length

private theorem le_trans' : ∀ (a b c : Int), (fun a b : Int => decide (a ≤ b)) a b →
    (fun a b : Int => decide (a ≤ b)) b c → (fun a b : Int => decide (a ≤ b)) a c := by
  intro a b c h1 h2
  simp only [decide_eq_true_eq] at *
  omega

private theorem le_total' : ∀ (a b : Int), ((fun a b : Int => decide (a ≤ b)) a b ||
    (fun a b : Int => decide (a ≤ b)) b a) := by
  intro a b
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  omega

private theorem sorted_window (l : List Int) :
    (l.mergeSort fun a b => decide (a ≤ b)).Pairwise (fun a b => (decide (a ≤ b)) = true) :=
  List.pairwise_mergeSort le_trans' le_total' l

private theorem countGe_perm (m : Int) {l₁ l₂ : List Int} (h : l₁.Perm l₂) : countGe m l₁ = countGe m l₂ := by
  unfold countGe
  exact (h.filter _).length_eq

private theorem countGe_le_length (m : Int) (l : List Int) : countGe m l ≤ l.length :=
  List.length_filter_le _ _

private theorem countGe_append (m : Int) (l₁ l₂ : List Int) :
    countGe m (l₁ ++ l₂) = countGe m l₁ + countGe m l₂ := by
  unfold countGe
  rw [List.filter_append, List.length_append]

private theorem countGe_cons_of_le (m t : Int) (l : List Int) (h : m ≤ t) :
    countGe m (t :: l) = countGe m l + 1 := by
  unfold countGe
  rw [List.filter_cons_of_pos (by simpa using h)]
  simp

private theorem countGe_eq_zero_of_forall (m : Int) (l : List Int) (h : ∀ a ∈ l, a < m) :
    countGe m l = 0 := by
  unfold countGe
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro a ha
  have := h a ha
  simp only [decide_eq_true_eq, Int.not_le]
  exact this

/-- Elements at or beyond the median index are at least the median. -/
private theorem count_ge_median (l : List Int) (k : Nat) (hk : k < l.length) :
    l.length - k ≤ countGe ((l.mergeSort fun a b => decide (a ≤ b)).getD k 0) l := by
  generalize hs : (l.mergeSort fun a b => decide (a ≤ b)) = s
  have hperm : s.Perm l := hs ▸ List.mergeSort_perm l _
  have hlen : s.length = l.length := hperm.length_eq
  have hsorted : s.Pairwise (fun a b => (decide (a ≤ b)) = true) := hs ▸ sorted_window l
  have hk' : k < s.length := by omega
  rw [← countGe_perm _ hperm]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
  -- s = take k s ++ (s[k] :: drop (k+1) s), and everything after index k is ≥ s[k]
  have hsplit : s = s.take k ++ s.drop k := (List.take_append_drop k s).symm
  have hdrop : s.drop k = s[k] :: s.drop (k + 1) := List.drop_eq_getElem_cons hk'
  have hpw : (s.drop k).Pairwise (fun a b => (decide (a ≤ b)) = true) :=
    hsorted.sublist (List.drop_sublist k s)
  rw [hdrop, List.pairwise_cons] at hpw
  have hall : ∀ a ∈ s.drop k, s[k] ≤ a := by
    intro a ha
    rw [hdrop] at ha
    rcases List.mem_cons.1 ha with rfl | hm
    · exact Int.le_refl _
    · have := hpw.1 a hm; simpa using this
  have hcount : countGe (s[k]) (s.drop k) = (s.drop k).length := by
    unfold countGe
    have : (s.drop k).filter (fun x => decide (s[k] ≤ x)) = s.drop k := by
      rw [List.filter_eq_self]
      intro a ha; simpa using hall a ha
    rw [this]
  calc l.length - k = s.length - k := by rw [hlen]
    _ = (s.drop k).length := by simp
    _ = countGe (s[k]) (s.drop k) := hcount.symm
    _ ≤ countGe (s[k]) (s.take k) + countGe (s[k]) (s.drop k) := Nat.le_add_left _ _
    _ = countGe (s[k]) s := by rw [← countGe_append]; congr 1; exact hsplit.symm

/-- If at least `n - k` elements are at least `m`, the sorted element at index `k` is at least `m`. -/
private theorem le_median_of_count (l : List Int) (m : Int) (k : Nat) (hk : k < l.length)
    (hc : l.length - k ≤ countGe m l) :
    m ≤ (l.mergeSort fun a b => decide (a ≤ b)).getD k 0 := by
  generalize hs : (l.mergeSort fun a b => decide (a ≤ b)) = s
  have hperm : s.Perm l := hs ▸ List.mergeSort_perm l _
  have hlen : s.length = l.length := hperm.length_eq
  have hsorted : s.Pairwise (fun a b => (decide (a ≤ b)) = true) := hs ▸ sorted_window l
  have hk' : k < s.length := by omega
  rw [← countGe_perm _ hperm] at hc
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
  rcases Int.lt_or_le (s[k]) m with hlt | hle
  · exfalso
    -- everything up to index k is ≤ s[k] < m
    have htake : ∀ a ∈ s.take (k + 1), a < m := by
      intro a ha
      rw [← List.take_append_getElem hk'] at ha
      have hpw : (s.take k ++ [s[k]]).Pairwise (fun a b => (decide (a ≤ b)) = true) := by
        rw [List.take_append_getElem hk']
        exact hsorted.sublist (List.take_sublist _ _)
      rw [List.pairwise_append] at hpw
      rcases List.mem_append.1 ha with h1 | h2
      · have := hpw.2.2 a h1 (s[k]) (List.mem_singleton.2 rfl)
        simp only [decide_eq_true_eq] at this
        omega
      · rw [List.mem_singleton] at h2; omega
    have h0 : countGe m (s.take (k + 1)) = 0 := countGe_eq_zero_of_forall m _ htake
    have hrest : countGe m (s.drop (k + 1)) ≤ s.length - (k + 1) := by
      have := countGe_le_length m (s.drop (k + 1)); simpa using this
    have htot : countGe m s = countGe m (s.take (k + 1)) + countGe m (s.drop (k + 1)) := by
      rw [← countGe_append, List.take_append_drop]
    omega
  · exact hle

/-- The median time past never decreases when a block satisfying the `time-too-old` rule is
appended. -/
theorem solution (times : List Int) (t : Int)
    (h : BitcoinHeader.medianTimePast times < t) :
    BitcoinHeader.medianTimePast times ≤ BitcoinHeader.medianTimePast (t :: times) := by
  generalize hm : medianTimePast times = m at *
  -- the old window and its count
  have hold : (timeWindow times).length - (timeWindow times).length / 2 ≤ countGe m (timeWindow times) := by
    by_cases hne : timeWindow times = []
    · rw [hne]; simp
    · have hpos : 0 < (timeWindow times).length := List.length_pos_iff.2 hne
      have := count_ge_median (timeWindow times) ((timeWindow times).length / 2) (by omega)
      unfold medianTimePast at hm
      simp only [] at hm
      rw [hm] at this
      exact this
  -- the new window is t :: take 10 times
  have hW' : timeWindow (t :: times) = t :: times.take 10 := by
    unfold timeWindow nMedianTimeSpan
    rfl
  -- dropping the eleventh element loses at most one counted element
  have hdrop1 : countGe m (timeWindow times) ≤ countGe m (times.take 10) + 1 := by
    unfold timeWindow nMedianTimeSpan
    have hsplit : times.take 11 = (times.take 11).take 10 ++ (times.take 11).drop 10 :=
      (List.take_append_drop 10 _).symm
    have htt : (times.take 11).take 10 = times.take 10 := by rw [List.take_take]; rfl
    rw [hsplit, countGe_append, htt]
    have : countGe m ((times.take 11).drop 10) ≤ 1 := by
      have h1 := countGe_le_length m ((times.take 11).drop 10)
      have h2 : ((times.take 11).drop 10).length ≤ 1 := by
        simp only [List.length_drop, List.length_take]; omega
      omega
    omega
  have hlen10 : (times.take 10).length = min 10 times.length := List.length_take
  have hlen11 : (timeWindow times).length = min 11 times.length := by
    unfold timeWindow nMedianTimeSpan; exact List.length_take
  -- for a chain shorter than eleven blocks the two windows coincide
  have hshort : times.length ≤ 10 → countGe m (times.take 10) = countGe m (timeWindow times) := by
    intro hle
    unfold timeWindow nMedianTimeSpan
    rw [List.take_of_length_le hle, List.take_of_length_le (by omega)]
  rw [hlen11] at hold
  generalize hc : countGe m (timeWindow times) = c at *
  generalize hd : countGe m (times.take 10) = d at *
  unfold medianTimePast
  simp only []
  rw [hW']
  apply le_median_of_count
  · simp only [List.length_cons, hlen10]; omega
  · rw [countGe_cons_of_le m t _ (Int.le_of_lt h)]
    simp only [List.length_cons, hlen10]
    rw [hd]
    rcases Nat.lt_or_ge times.length 11 with hlt | hge
    · have := hshort (by omega); omega
    · omega
