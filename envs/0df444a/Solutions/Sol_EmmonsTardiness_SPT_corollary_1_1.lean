-- Prove2me | solution 1 for EmmonsTardiness.SPT.corollary_1_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:56:06.851869+00:00
-- url     : https://prove2.me/submissions/70b2e889-fab9-455f-b71a-a2b3504bddb1

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_EmmonsTardiness_SPT_Model

set_option autoImplicit false

namespace Cor11Aux6361
open MooreLateJobs EmmonsTardiness.SPT

lemma compl_eq {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (s t : List ι) (i : ι) (hi : i ∉ s) :
    Shared.completionTime p (s ++ i :: t) i = (s.map p).sum + p i := by
  unfold Shared.completionTime Shared.completionAt
  rw [List.idxOf_append_of_notMem hi]
  simp [List.take_append]
  rw [List.take_of_length_le (by simp)]

lemma arith (pj pk dj dk a : ℝ) (ha : 0 ≤ a) (h1 : pj ≤ pk) (h0 : 0 ≤ pj)
    (hd : dj ≤ max pk dk) :
    max 0 (pj - dj) + max 0 (pj + a + pk - dk) ≤ max 0 (pk - dk) + max 0 (pk + a + pj - dj) := by
  rcases le_max_iff.mp hd with hd | hd <;>
  · simp only [max_def]
    split_ifs <;> linarith

lemma tard_mono {ι : Type*} [DecidableEq ι] (p d : ι → ℝ) (l l' : List ι) (i : ι)
    (h : Shared.completionTime p l i ≤ Shared.completionTime p l' i) :
    tardiness p d l i ≤ tardiness p d l' i := by
  unfold tardiness
  exact max_le_max (le_refl 0) (by linarith)

lemma swap_le {ι : Type*} [DecidableEq ι] (p d : ι → ℝ) (J : Finset ι) (A C : List ι) (j k : ι)
    (hnd : (k :: (A ++ j :: C)).Nodup) (hJ : ∀ x, x ∈ k :: (A ++ j :: C) ↔ x ∈ J)
    (hp : ∀ i ∈ J, 0 ≤ p i) (hpjk : p j ≤ p k) (hd : d j ≤ max (p k) (d k)) :
    totalTardiness p d J (j :: (A ++ k :: C)) ≤ totalTardiness p d J (k :: (A ++ j :: C)) := by
  have hnd' := hnd
  simp only [List.nodup_cons, List.nodup_append, List.mem_append, List.mem_cons, not_or] at hnd'
  obtain ⟨⟨hkA, hkj, hkC⟩, hndA, ⟨hjC, hndC⟩, hdisj⟩ := hnd'
  have hjJ : j ∈ J := (hJ j).1 (by simp)
  have hkJ : k ∈ J := (hJ k).1 (by simp)
  have hjk : j ≠ k := fun e => hkj e.symm
  have hAJ : ∀ x ∈ A, x ∈ J := fun x hx => (hJ x).1 (by simp [hx])
  have hA0 : 0 ≤ (A.map p).sum := List.sum_nonneg (by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hp y (hAJ y hy))
  have hjA : j ∉ A := fun h => (hdisj j h j (by simp)) rfl
  -- completion times of j and k
  have c1 : Shared.completionTime p (j :: (A ++ k :: C)) j = p j := by
    simpa using compl_eq p [] (A ++ k :: C) j (by simp)
  have c2 : Shared.completionTime p (j :: (A ++ k :: C)) k = p j + (A.map p).sum + p k := by
    have := compl_eq p (j :: A) C k (by simp [hkj, hkA])
    simpa [add_assoc] using this
  have c3 : Shared.completionTime p (k :: (A ++ j :: C)) k = p k := by
    simpa using compl_eq p [] (A ++ j :: C) k (by simp)
  have c4 : Shared.completionTime p (k :: (A ++ j :: C)) j = p k + (A.map p).sum + p j := by
    have := compl_eq p (k :: A) C j (by simp [hjk, hjA])
    simpa [add_assoc] using this
  -- other jobs
  have hother : ∀ i ∈ J, i ≠ j → i ≠ k →
      tardiness p d (j :: (A ++ k :: C)) i ≤ tardiness p d (k :: (A ++ j :: C)) i := by
    intro i hi hij hik
    apply tard_mono
    have hm := (hJ i).2 hi
    simp only [List.mem_cons, List.mem_append, hik, hij, false_or] at hm
    rcases hm with hm | hm
    · obtain ⟨A1, A2, rfl⟩ := List.append_of_mem hm
      have hiA1 : i ∉ A1 := by
        intro h'
        have := (List.nodup_append.mp hndA)
        simp at this
        exact (this.2.2 i h').1 rfl
      have e1 := compl_eq p (j :: A1) (A2 ++ k :: C) i (by simp [hij, hiA1])
      have e2 := compl_eq p (k :: A1) (A2 ++ j :: C) i (by simp [hik, hiA1])
      simp only [List.cons_append, List.append_assoc] at e1 e2 ⊢
      rw [e1, e2]
      simp
      linarith
    · obtain ⟨C1, C2, rfl⟩ := List.append_of_mem hm
      have hiC1 : i ∉ C1 := by
        intro h'
        have := (List.nodup_append.mp hndC)
        simp at this
        exact (this.2.2 i h').1 rfl
      have hiA : i ∉ A := fun h' => hdisj i h' i (by simp) rfl
      have e1 := compl_eq p (j :: (A ++ k :: C1)) C2 i (by simp [hij, hik, hiA, hiC1])
      have e2 := compl_eq p (k :: (A ++ j :: C1)) C2 i (by simp [hij, hik, hiA, hiC1])
      simp only [List.cons_append, List.append_assoc] at e1 e2 ⊢
      rw [e1, e2]
      simp
      linarith
  unfold totalTardiness
  rw [← Finset.add_sum_erase J _ hjJ, ← Finset.add_sum_erase J _ hjJ,
    ← Finset.add_sum_erase (J.erase j) _ (Finset.mem_erase.mpr ⟨hjk.symm, hkJ⟩),
    ← Finset.add_sum_erase (J.erase j) _ (Finset.mem_erase.mpr ⟨hjk.symm, hkJ⟩)]
  have hsum := Finset.sum_le_sum (s := (J.erase j).erase k) (fun i hi => by
    simp only [Finset.mem_erase] at hi
    exact hother i hi.2.2 hi.2.1 hi.1)
  have key : tardiness p d (j :: (A ++ k :: C)) j + tardiness p d (j :: (A ++ k :: C)) k ≤
      tardiness p d (k :: (A ++ j :: C)) j + tardiness p d (k :: (A ++ j :: C)) k := by
    unfold tardiness
    rw [c1, c2, c3, c4]
    have := arith (p j) (p k) (d j) (d k) (A.map p).sum hA0 hpjk (hp j hjJ) hd
    linarith
  linarith

end Cor11Aux6361

open EmmonsTardiness.SPT MooreLateJobs in
theorem solution {ι : Type*} [LinearOrder ι] (p d : ι → ℝ) (J : Finset ι)
    (hp : ∀ i ∈ J, 0 ≤ p i) (hidx : IsSPTIndexed p d J) (hJ : J.Nonempty)
    (h : ∀ i ∈ J, J.min' hJ < i → d (J.min' hJ) ≤ max (p i) (d i)) :
    ∃ l, IsOptimal p d J l ∧ l.head? = some (J.min' hJ) := by
  set j := J.min' hJ with hj
  have hjJ : j ∈ J := J.min'_mem hJ
  set L := J.sort (· ≤ ·) with hL
  have hLnd : L.Nodup := Finset.sort_nodup _ _
  have hsched : ∀ l : List ι, Shared.IsSchedule J l ↔ l ∈ L.permutations.toFinset := by
    intro l
    simp only [List.mem_toFinset, List.mem_permutations, Shared.IsSchedule]
    constructor
    · rintro ⟨hn, hm⟩
      exact (List.perm_ext_iff_of_nodup hn hLnd).2 (fun a => by rw [hm, Finset.mem_sort])
    · intro hperm
      exact ⟨hperm.nodup_iff.2 hLnd, fun x => by rw [hperm.mem_iff, Finset.mem_sort]⟩
  have hne : (L.permutations.toFinset).Nonempty :=
    ⟨L, by simp [List.mem_permutations]⟩
  obtain ⟨l, hl, hmin⟩ := Finset.exists_min_image _
    (fun l => EmmonsTardiness.SPT.totalTardiness p d J l) hne
  have hlS := (hsched l).2 hl
  have hopt : EmmonsTardiness.SPT.IsOptimal p d J l :=
    ⟨hlS, fun l' hl' => hmin l' ((hsched l').1 hl')⟩
  rcases hlc : l with _ | ⟨k, rest⟩
  · exfalso
    have := (hlS.2 j).2 hjJ
    simp [hlc] at this
  by_cases hkj : k = j
  · exact ⟨l, hopt, by simp [hlc, hkj]⟩
  have hjrest : j ∈ rest := by
    have := (hlS.2 j).2 hjJ
    rw [hlc] at this
    rcases List.mem_cons.mp this with h' | h'
    · exact absurd h'.symm hkj
    · exact h'
  obtain ⟨A, C, rfl⟩ := List.append_of_mem hjrest
  have hkJ : k ∈ J := (hlS.2 k).1 (by simp [hlc])
  have hlt : j < k := lt_of_le_of_ne (J.min'_le k hkJ) (Ne.symm hkj)
  have hpjk : p j ≤ p k := by
    rcases hidx j hjJ k hkJ hlt with h' | h'
    · exact h'.le
    · exact h'.1.le
  have hnd : (k :: (A ++ j :: C)).Nodup := by rw [← hlc]; exact hlS.1
  have hmem : ∀ x, x ∈ k :: (A ++ j :: C) ↔ x ∈ J := by rw [← hlc]; exact hlS.2
  have hle := Cor11Aux6361.swap_le p d J A C j k hnd hmem hp hpjk (h k hkJ hlt)
  have hperm : (j :: (A ++ k :: C)).Perm (k :: (A ++ j :: C)) := by
    have h1 : (j :: (A ++ k :: C)).Perm (A ++ j :: k :: C) := List.perm_middle.symm
    have h2 : (k :: (A ++ j :: C)).Perm (A ++ k :: j :: C) := List.perm_middle.symm
    exact h1.trans ((List.Perm.swap k j C).append_left A |>.trans h2.symm)
  have hS' : Shared.IsSchedule J (j :: (A ++ k :: C)) :=
    ⟨hperm.nodup_iff.2 hnd, fun x => by rw [hperm.mem_iff, hmem]⟩
  refine ⟨j :: (A ++ k :: C), ⟨hS', fun l' hl' => ?_⟩, by simp⟩
  have := hopt.2 l' hl'
  rw [hlc] at this
  linarith
