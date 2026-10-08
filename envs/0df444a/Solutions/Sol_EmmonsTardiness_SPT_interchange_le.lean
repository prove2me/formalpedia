-- Prove2me | solution 1 for EmmonsTardiness.SPT.interchange_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T18:57:41.617408+00:00
-- url     : https://prove2.me/submissions/f7585ae9-098d-471e-a52d-9ed7ac2023b7

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_EmmonsTardiness_SPT_Model



namespace EmmonsTardiness.SPT

open MooreLateJobs

noncomputable def SF {ι : Type*} (p d : ι → ℝ) : ℝ → List ι → ℝ
  | _, [] => 0
  | t, x :: r => max 0 (t + p x - d x) + SF p d (t + p x) r

section
variable {ι : Type*} (p d : ι → ℝ)

lemma SF_nil (t : ℝ) : SF p d t ([] : List ι) = 0 := rfl
lemma SF_cons (t : ℝ) (x : ι) (r : List ι) :
    SF p d t (x :: r) = max 0 (t + p x - d x) + SF p d (t + p x) r := rfl

lemma SF_append (t : ℝ) (l₁ l₂ : List ι) :
    SF p d t (l₁ ++ l₂) = SF p d t l₁ + SF p d (t + (l₁.map p).sum) l₂ := by
  induction l₁ generalizing t with
  | nil => simp [SF_nil]
  | cons x r ih =>
    simp only [List.cons_append, SF_cons, ih, List.map_cons, List.sum_cons]
    rw [show t + (p x + (r.map p).sum) = t + p x + (r.map p).sum by ring]
    ring

lemma SF_mono (l : List ι) :
    ∀ t t' : ℝ, t ≤ t' → SF p d t l ≤ SF p d t' l := by
  induction l with
  | nil => intros; simp [SF_nil]
  | cons x r ih =>
    intro t t' h
    rw [SF_cons, SF_cons]
    have h1 : max 0 (t + p x - d x) ≤ max 0 (t' + p x - d x) := max_le_max le_rfl (by linarith)
    have := ih (t + p x) (t' + p x) (by linarith)
    linarith

lemma sct_cons_self [DecidableEq ι] (x : ι) (r : List ι) :
    Shared.completionTime p (x :: r) x = p x := by
  simp [Shared.completionTime, Shared.completionAt]

lemma sct_cons_ne [DecidableEq ι] (x i : ι) (r : List ι) (h : i ≠ x) :
    Shared.completionTime p (x :: r) i = p x + Shared.completionTime p r i := by
  simp [Shared.completionTime, Shared.completionAt, List.idxOf_cons_ne _ (Ne.symm h)]

lemma ssum_eq_SF [DecidableEq ι] (l : List ι) (hl : l.Nodup) (t : ℝ) :
    (l.map fun i => max 0 (t + Shared.completionTime p l i - d i)).sum = SF p d t l := by
  induction l generalizing t with
  | nil => simp [SF_nil]
  | cons x r ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.sum_cons, SF_cons, sct_cons_self, ← ih hl.2 (t + p x)]
    congr 1
    apply congrArg
    apply List.map_congr_left
    intro i hi
    have : i ≠ x := fun h => hl.1 (h ▸ hi)
    rw [sct_cons_ne p x i r this, ← add_assoc]

lemma stt_eq [DecidableEq ι] (J : Finset ι) (l : List ι) (hl : Shared.IsSchedule J l) :
    totalTardiness p d J l = SF p d 0 l := by
  have hJ : l.toFinset = J := by ext x; simp [hl.2 x]
  rw [← ssum_eq_SF p d l hl.1 0, totalTardiness, ← hJ, List.sum_toFinset _ hl.1]
  simp [tardiness]

lemma sswap_key (t S pj pk dj dk : ℝ) (hS : 0 ≤ S) (hpj : 0 ≤ pj) (hp : pj ≤ pk)
    (hd : dj ≤ dk ∨ dj ≤ t + pk) :
    max 0 (t + pj - dj) + max 0 (t + pj + S + pk - dk) ≤
      max 0 (t + pk - dk) + max 0 (t + pk + S + pj - dj) := by
  rcases hd with hd | hd <;>
  rcases le_total 0 (t + pj - dj) with h1 | h1 <;>
  rcases le_total 0 (t + pj + S + pk - dk) with h2 | h2 <;>
  rcases le_total 0 (t + pk - dk) with h3 | h3 <;>
  rcases le_total 0 (t + pk + S + pj - dj) with h4 | h4 <;>
  simp only [max_eq_left, max_eq_right, h1, h2, h3, h4] <;> linarith

lemma sswap_le (t : ℝ) (j k : ι) (mid post : List ι) (hS : 0 ≤ (mid.map p).sum) (hpj : 0 ≤ p j)
    (hp : p j ≤ p k) (hd : d j ≤ d k ∨ d j ≤ t + p k) :
    SF p d t (j :: (mid ++ k :: post)) ≤ SF p d t (k :: (mid ++ j :: post)) := by
  simp only [SF_cons, SF_append]
  have hm := SF_mono p d mid (t + p j) (t + p k) (by linarith)
  have key := sswap_key t (mid.map p).sum (p j) (p k) (d j) (d k) hS hpj hp hd
  rw [show t + p k + (mid.map p).sum + p j = t + p j + (mid.map p).sum + p k by ring] at key ⊢
  linarith

end

section
variable {ι : Type*} [DecidableEq ι]

lemma ssched_perm {J : Finset ι} {l l' : List ι} (hl : Shared.IsSchedule J l) (h : l'.Perm l) :
    Shared.IsSchedule J l' :=
  ⟨h.nodup_iff.2 hl.1, fun x => by rw [h.mem_iff, hl.2 x]⟩

lemma sswap_perm (pre mid post : List ι) (j k : ι) :
    (pre ++ j :: (mid ++ k :: post)).Perm (pre ++ k :: (mid ++ j :: post)) := by
  apply List.Perm.append_left
  exact ((List.perm_middle).cons j).trans ((List.Perm.swap k j _).trans ((List.perm_middle).symm.cons k))

lemma smem_after (s t : List ι) (k i : ι) (hn : (s ++ k :: t).Nodup) (hi : i ∈ s ++ k :: t)
    (h : (s ++ k :: t).idxOf k < (s ++ k :: t).idxOf i) : i ∈ t := by
  have hks : k ∉ s := by
    have := List.nodup_middle.1 hn
    rw [List.nodup_cons] at this
    exact fun h' => this.1 (List.mem_append_left _ h')
  rw [List.idxOf_append_of_notMem hks] at h
  simp only [List.idxOf_cons_self, add_zero] at h
  rcases List.mem_append.1 hi with h1 | h1
  · rw [List.idxOf_append_of_mem h1] at h
    have := List.idxOf_lt_length_of_mem h1
    omega
  · rcases List.mem_cons.1 h1 with h2 | h2
    · subst h2
      rw [List.idxOf_append_of_notMem hks] at h
      simp at h
    · exact h2

lemma smem_before (s t : List ι) (k i : ι) (hn : (s ++ k :: t).Nodup) (hi : i ∈ s ++ k :: t)
    (h : (s ++ k :: t).idxOf i < (s ++ k :: t).idxOf k) : i ∈ s := by
  have hks : k ∉ s := by
    have := List.nodup_middle.1 hn
    rw [List.nodup_cons] at this
    exact fun h' => this.1 (List.mem_append_left _ h')
  by_contra hc
  rw [List.idxOf_append_of_notMem hks, List.idxOf_append_of_notMem hc] at h
  simp only [List.idxOf_cons_self, add_zero] at h
  omega

lemma sdecomp (l : List ι) (a b : ι) (hn : l.Nodup) (ha : a ∈ l) (hb : b ∈ l)
    (h : l.idxOf a < l.idxOf b) : ∃ pre mid post, l = pre ++ a :: (mid ++ b :: post) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  have hbt := smem_after s t a b hn hb h
  obtain ⟨m, q, rfl⟩ := List.append_of_mem hbt
  exact ⟨s, m, q, rfl⟩

lemma sprec (pre mid post : List ι) (a b : ι) (hn : (pre ++ a :: (mid ++ b :: post)).Nodup) :
    Precedes (pre ++ a :: (mid ++ b :: post)) a b := by
  have h1 := List.nodup_middle.1 hn
  rw [List.nodup_cons] at h1
  have hapre : a ∉ pre := fun h' => h1.1 (List.mem_append_left _ h')
  have hbpre : b ∉ pre := by
    intro h'
    have := List.disjoint_of_nodup_append hn h'
    exact this (by simp)
  have hab : b ≠ a := by
    intro h'; subst h'; exact h1.1 (List.mem_append_right _ (by simp))
  unfold Precedes
  rw [List.idxOf_append_of_notMem hapre, List.idxOf_append_of_notMem hbpre,
    List.idxOf_cons_self, List.idxOf_cons_ne _ hab.symm]
  omega

lemma sprec_pre (pre rest : List ι) (i k : ι) (hi : i ∈ pre) (hk : k ∉ pre) :
    Precedes (pre ++ rest) i k := by
  unfold Precedes
  rw [List.idxOf_append_of_mem hi, List.idxOf_append_of_notMem hk]
  have := List.idxOf_lt_length_of_mem hi
  omega

lemma smap_swap_id (s : List ι) (j k : ι) (hj : j ∉ s) (hk : k ∉ s) :
    s.map (Equiv.swap j k) = s := by
  conv_rhs => rw [← List.map_id s]
  apply List.map_congr_left
  intro x hx
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hj (h ▸ hx)) (fun h => hk (h ▸ hx))

lemma smap_swap_eq (pre mid post : List ι) (j k : ι)
    (hn : (pre ++ k :: (mid ++ j :: post)).Nodup) :
    (pre ++ k :: (mid ++ j :: post)).map (Equiv.swap j k) = pre ++ j :: (mid ++ k :: post) := by
  have hk := List.nodup_cons.1 (List.nodup_middle.1 hn)
  have e : pre ++ k :: (mid ++ j :: post) = (pre ++ k :: mid) ++ j :: post := by simp
  have hn' := hn; rw [e] at hn'
  have hj := List.nodup_cons.1 (List.nodup_middle.1 hn')
  simp only [List.mem_append, List.mem_cons, not_or] at hk hj
  simp only [List.map_append, List.map_cons, Equiv.swap_apply_right, Equiv.swap_apply_left]
  rw [smap_swap_id pre j k hj.1.1.1 hk.1.1, smap_swap_id mid j k hj.1.1.2.2 hk.1.2.1,
    smap_swap_id post j k hj.1.2 hk.1.2.2.2]

/-- core of the interchange in decomposed form -/
lemma sinter_tt (p d : ι → ℝ) (J : Finset ι) (hp : ∀ i ∈ J, 0 ≤ p i)
    (pre mid post : List ι) (j k : ι)
    (hl : Shared.IsSchedule J (pre ++ k :: (mid ++ j :: post))) (hpp : p j ≤ p k)
    (hd : d j ≤ d k ∨ d j ≤ (pre.map p).sum + p k) :
    Shared.IsSchedule J (pre ++ j :: (mid ++ k :: post)) ∧
      totalTardiness p d J (pre ++ j :: (mid ++ k :: post)) ≤
        totalTardiness p d J (pre ++ k :: (mid ++ j :: post)) := by
  have hs' := ssched_perm hl (sswap_perm pre mid post j k)
  refine ⟨hs', ?_⟩
  have hS : 0 ≤ (mid.map p).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact hp y ((hl.2 y).1 (by simp [hy]))
  rw [stt_eq p d J _ hs', stt_eq p d J _ hl, SF_append p d 0 pre, SF_append p d 0 pre]
  have := sswap_le p d (0 + (pre.map p).sum) j k mid post hS (hp j ((hl.2 j).1 (by simp))) hpp (by simpa using hd)
  linarith

lemma sB_le (p : ι → ℝ) (J B : Finset ι) (hp : ∀ i ∈ J, 0 ≤ p i) (pre : List ι)
    (hn : pre.Nodup) (hpre : ∀ x ∈ pre, x ∈ J) (hB : ∀ i ∈ B, i ∈ pre) :
    ∑ i ∈ B, p i ≤ (pre.map p).sum := by
  rw [← List.sum_toFinset _ hn]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx; exact List.mem_toFinset.2 (hB x hx)
  · intro i hi _; exact hp i (hpre i (List.mem_toFinset.1 hi))

end

theorem interchange_core {ι : Type*} [LinearOrder ι] (p d : ι → ℝ) (J : Finset ι)
    (hp : ∀ i ∈ J, 0 ≤ p i) (hidx : IsSPTIndexed p d J)
    (j k : ι) (hj : j ∈ J) (hk : k ∈ J) (hjk : j < k)
    (B : Finset ι) (hB : B ⊆ J)
    (h2 : d j ≤ max ((∑ i ∈ B, p i) + p k) (d k))
    (l : List ι) (hl : Shared.IsSchedule J l)
    (hBl : ∀ i ∈ B, Precedes l i k) (hkj : Precedes l k j) :
    Shared.IsSchedule J (l.map (Equiv.swap j k)) ∧
      (∀ i ∈ B, Precedes (l.map (Equiv.swap j k)) i k) ∧
      Precedes (l.map (Equiv.swap j k)) j k ∧
      totalTardiness p d J (l.map (Equiv.swap j k)) ≤ totalTardiness p d J l := by
  obtain ⟨pre, mid, post, rfl⟩ :=
    sdecomp l k j hl.1 ((hl.2 k).2 hk) ((hl.2 j).2 hj) hkj
  have hn := hl.1
  rw [smap_swap_eq pre mid post j k hn]
  have hkpre : k ∉ pre := fun h' =>
    (List.nodup_cons.1 (List.nodup_middle.1 hn)).1 (List.mem_append_left _ h')
  have hBpre : ∀ i ∈ B, i ∈ pre := fun i hi =>
    smem_before pre _ k i hn ((hl.2 i).2 (hB hi)) (hBl i hi)
  have hpp : p j ≤ p k := by
    rcases hidx j hj k hk hjk with h | h
    · exact h.le
    · exact h.1.le
  have hpre : ∀ x ∈ pre, x ∈ J := fun x hx => (hl.2 x).1 (List.mem_append_left _ hx)
  have hBs := sB_le p J B hp pre (hn.sublist (List.sublist_append_left _ _)) hpre hBpre
  have hd : d j ≤ d k ∨ d j ≤ (pre.map p).sum + p k := by
    rcases le_max_iff.1 h2 with h | h
    · right; linarith
    · left; exact h
  obtain ⟨hs, hle⟩ := sinter_tt p d J hp pre mid post j k hl hpp hd
  refine ⟨hs, fun i hi => sprec_pre pre _ i k (hBpre i hi) hkpre, sprec pre mid post j k hs.1, hle⟩

end EmmonsTardiness.SPT

open EmmonsTardiness.SPT
open MooreLateJobs

theorem solution {ι : Type*} [LinearOrder ι] (p d : ι → ℝ) (J : Finset ι)
    (hp : ∀ i ∈ J, 0 ≤ p i) (hidx : IsSPTIndexed p d J)
    (j k : ι) (hj : j ∈ J) (hk : k ∈ J) (hjk : j < k)
    (B : Finset ι) (hB : B ⊆ J)
    (h2 : d j ≤ max ((∑ i ∈ B, p i) + p k) (d k))
    (l : List ι) (hl : Shared.IsSchedule J l)
    (hBl : ∀ i ∈ B, Precedes l i k) (hkj : Precedes l k j) :
    Shared.IsSchedule J (l.map (Equiv.swap j k)) ∧
      (∀ i ∈ B, Precedes (l.map (Equiv.swap j k)) i k) ∧
      Precedes (l.map (Equiv.swap j k)) j k ∧
      totalTardiness p d J (l.map (Equiv.swap j k)) ≤ totalTardiness p d J l := by
  exact interchange_core p d J hp hidx j k hj hk hjk B hB h2 l hl hBl hkj
