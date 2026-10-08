-- Prove2me | solution 1 for EmmonsTardiness.EDD.corollary_2_2_star
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T18:31:26.972905+00:00
-- url     : https://prove2.me/submissions/26b3670b-3c32-4ea9-869e-548db82f4032

import Mathlib
import Definitions.Def_EmmonsTardiness_EDD_Model



namespace EmmonsTardiness.EDD

open MooreLateJobs

noncomputable def EFc {ι : Type*} (g : ℝ → ℝ) (p d : ι → ℝ) : ℝ → List ι → ℝ
  | _, [] => 0
  | t, x :: r => g (max 0 (t + p x - d x)) + EFc g p d (t + p x) r

section
variable {ι : Type*} (g : ℝ → ℝ) (p d : ι → ℝ)

lemma EFc_nil (t : ℝ) : EFc g p d t ([] : List ι) = 0 := rfl
lemma EFc_cons (t : ℝ) (x : ι) (r : List ι) :
    EFc g p d t (x :: r) = g (max 0 (t + p x - d x)) + EFc g p d (t + p x) r := rfl

lemma EFc_append (t : ℝ) (l₁ l₂ : List ι) :
    EFc g p d t (l₁ ++ l₂) = EFc g p d t l₁ + EFc g p d (t + (l₁.map p).sum) l₂ := by
  induction l₁ generalizing t with
  | nil => simp [EFc_nil]
  | cons x r ih =>
    simp only [List.cons_append, EFc_cons, ih, List.map_cons, List.sum_cons]
    rw [show t + (p x + (r.map p).sum) = t + p x + (r.map p).sum by ring]
    ring

lemma EFc_mono (hgm : MonotoneOn g (Set.Ici 0)) (l : List ι) :
    ∀ t t' : ℝ, t ≤ t' → EFc g p d t l ≤ EFc g p d t' l := by
  induction l with
  | nil => intros; simp [EFc_nil]
  | cons x r ih =>
    intro t t' h
    rw [EFc_cons, EFc_cons]
    have h1 : g (max 0 (t + p x - d x)) ≤ g (max 0 (t' + p x - d x)) :=
      hgm (Set.mem_Ici.2 (le_max_left _ _)) (Set.mem_Ici.2 (le_max_left _ _)) (max_le_max le_rfl (by linarith))
    have := ih (t + p x) (t' + p x) (by linarith)
    linarith

lemma ect_cons_self [DecidableEq ι] (x : ι) (r : List ι) :
    Shared.completionTime p (x :: r) x = p x := by
  simp [Shared.completionTime, Shared.completionAt]

lemma ect_cons_ne [DecidableEq ι] (x i : ι) (r : List ι) (h : i ≠ x) :
    Shared.completionTime p (x :: r) i = p x + Shared.completionTime p r i := by
  simp [Shared.completionTime, Shared.completionAt, List.idxOf_cons_ne _ (Ne.symm h)]

lemma esum_eq_EFc [DecidableEq ι] (l : List ι) (hl : l.Nodup) (t : ℝ) :
    (l.map fun i => g (max 0 (t + Shared.completionTime p l i - d i))).sum = EFc g p d t l := by
  induction l generalizing t with
  | nil => simp [EFc_nil]
  | cons x r ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.sum_cons, EFc_cons, ect_cons_self, ← ih hl.2 (t + p x)]
    congr 1
    apply congrArg
    apply List.map_congr_left
    intro i hi
    have : i ≠ x := fun h => hl.1 (h ▸ hi)
    rw [ect_cons_ne p x i r this, ← add_assoc]

lemma etp_eq [DecidableEq ι] (J : Finset ι) (l : List ι) (hl : Shared.IsSchedule J l) :
    totalPenalty g p d J l = EFc g p d 0 l := by
  have hJ : l.toFinset = J := by ext x; simp [hl.2 x]
  rw [← esum_eq_EFc g p d l hl.1 0, totalPenalty, ← hJ, List.sum_toFinset _ hl.1]
  simp [EmmonsTardiness.SPT.tardiness]

lemma elsum_eq [DecidableEq ι] (J : Finset ι) (l : List ι) (hl : Shared.IsSchedule J l)
    (f : ι → ℝ) : (l.map f).sum = ∑ i ∈ J, f i := by
  have hJ : l.toFinset = J := by ext x; simp [hl.2 x]
  rw [← hJ, List.sum_toFinset _ hl.1]

lemma elsum_le [DecidableEq ι] (T : Finset ι) (l : List ι) (hn : l.Nodup)
    (hsub : ∀ x ∈ l, x ∈ T) (hp : ∀ i ∈ T, 0 ≤ p i) :
    (l.map p).sum ≤ ∑ i ∈ T, p i := by
  rw [← List.sum_toFinset _ hn]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx; exact hsub x (List.mem_toFinset.1 hx)
  · intro i hi _; exact hp i hi

lemma ekey_conv (hg : ConvexOn ℝ (Set.Ici 0) g) {a b x y : ℝ} (ha : 0 ≤ a) (hax : a ≤ x)
    (hxb : x ≤ b) (hay : a ≤ y) (hyb : y ≤ b) (hs : x + y = a + b) :
    g x + g y ≤ g a + g b := by
  rcases eq_or_lt_of_le (hax.trans hxb) with h | h
  · have hx : x = a := by linarith
    have hy : y = b := by linarith
    rw [hx, hy]
  · have hba : 0 < b - a := by linarith
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (b - x) / (b - a) := ⟨_, rfl⟩
    have hθ0 : 0 ≤ θ := by rw [hθ]; exact div_nonneg (by linarith) hba.le
    have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hba]; linarith
    have hamem : a ∈ Set.Ici (0:ℝ) := ha
    have hbmem : b ∈ Set.Ici (0:ℝ) := show (0:ℝ) ≤ b by linarith
    have h1 := hg.2 hamem hbmem hθ0 (by linarith : (0:ℝ) ≤ 1 - θ) (by ring)
    have h2 := hg.2 hamem hbmem (by linarith : (0:ℝ) ≤ 1 - θ) hθ0 (by ring)
    have ex : θ • a + (1 - θ) • b = x := by
      simp only [smul_eq_mul]; rw [hθ]; field_simp; ring
    have ey : (1 - θ) • a + θ • b = y := by
      rw [show y = a + b - x by linarith]; simp only [smul_eq_mul]; rw [hθ]; field_simp; ring
    rw [ex] at h1; rw [ey] at h2
    simp only [smul_eq_mul] at h1 h2
    calc g x + g y ≤ (θ * g a + (1 - θ) * g b) + ((1 - θ) * g a + θ * g b) := add_le_add h1 h2
      _ = g a + g b := by ring

lemma emajor (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0)) {a b x y : ℝ}
    (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxb : x ≤ b) (hyb : y ≤ b) (hs : x + y ≤ a + b) :
    g x + g y ≤ g a + g b := by
  have hb : 0 ≤ b := hx.trans hxb
  rcases le_or_gt (x + y) b with h | h
  · have k := ekey_conv g hg (le_refl 0) hx (by linarith) hy (by linarith) (by ring : x + y = 0 + (x + y))
    have m1 : g 0 ≤ g a := hgm (le_refl (0:ℝ)) ha ha
    have m2 : g (x + y) ≤ g b := hgm (show (0:ℝ) ≤ x + y by linarith) hb h
    linarith
  · have k := ekey_conv g hg (show 0 ≤ x + y - b by linarith) (by linarith) hxb (by linarith) hyb
      (by ring : x + y = (x + y - b) + b)
    have m1 : g (x + y - b) ≤ g a := hgm (show (0:ℝ) ≤ x + y - b by linarith) ha (by linarith)
    linarith

lemma emove_key (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (t S pj pk dj dk : ℝ) (hpj : 0 ≤ pj) (hd : dk ≤ dj) (hC : t + S + pk ≤ dj) :
    g (max 0 (t + S + pk - dk)) + g (max 0 (t + S + pk + pj - dj)) ≤
      g (max 0 (t + pj - dj)) + g (max 0 (t + pj + S + pk - dk)) := by
  apply emajor g hg hgm (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
  · apply max_le_max le_rfl; linarith
  · apply max_le_max le_rfl; linarith
  · have h0 : 0 ≤ max 0 (t + pj - dj) := le_max_left _ _
    have : max 0 (t + S + pk - dk) + max 0 (t + S + pk + pj - dj) ≤ max 0 (t + pj + S + pk - dk) := by
      rcases le_total 0 (t + S + pk - dk) with h1 | h1 <;>
      rcases le_total 0 (t + S + pk + pj - dj) with h2 | h2 <;>
      rcases le_total 0 (t + pj + S + pk - dk) with h3 | h3 <;>
      simp only [max_eq_left, max_eq_right, h1, h2, h3] <;> linarith
    linarith

lemma eswap_key (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (t S pj pk dj dk : ℝ) (hpj : 0 ≤ pj) (hS : 0 ≤ S) (hp : pj ≤ pk) (hd : dj ≤ dk) :
    g (max 0 (t + pj - dj)) + g (max 0 (t + pj + S + pk - dk)) ≤
      g (max 0 (t + pk - dk)) + g (max 0 (t + pk + S + pj - dj)) := by
  apply emajor g hg hgm (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
  · apply max_le_max le_rfl; linarith
  · apply max_le_max le_rfl; linarith
  · rcases le_total 0 (t + pj - dj) with h1 | h1 <;>
    rcases le_total 0 (t + pj + S + pk - dk) with h2 | h2 <;>
    rcases le_total 0 (t + pk - dk) with h3 | h3 <;>
    rcases le_total 0 (t + pk + S + pj - dj) with h4 | h4 <;>
    simp only [max_eq_left, max_eq_right, h1, h2, h3, h4] <;> linarith

lemma emove_le (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (t : ℝ) (j k : ι) (mid post : List ι) (hpj : 0 ≤ p j) (hd : d k ≤ d j)
    (hC : t + (mid.map p).sum + p k ≤ d j) :
    EFc g p d t (mid ++ k :: j :: post) ≤ EFc g p d t (j :: (mid ++ k :: post)) := by
  simp only [EFc_cons, EFc_append]
  have hm := EFc_mono g p d hgm mid t (t + p j) (by linarith)
  have key := emove_key g hg hgm t (mid.map p).sum (p j) (p k) (d j) (d k) hpj hd hC
  rw [show t + (mid.map p).sum + p k + p j = t + p j + (mid.map p).sum + p k by ring] at key ⊢
  linarith

lemma eswap_le (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (t : ℝ) (j k : ι) (mid post : List ι) (hpj : 0 ≤ p j) (hS : 0 ≤ (mid.map p).sum)
    (hp : p j ≤ p k) (hd : d j ≤ d k) :
    EFc g p d t (j :: (mid ++ k :: post)) ≤ EFc g p d t (k :: (mid ++ j :: post)) := by
  simp only [EFc_cons, EFc_append]
  have hm := EFc_mono g p d hgm mid (t + p j) (t + p k) (by linarith)
  have key := eswap_key g hg hgm t (mid.map p).sum (p j) (p k) (d j) (d k) hpj hS hp hd
  rw [show t + p k + (mid.map p).sum + p j = t + p j + (mid.map p).sum + p k by ring] at key ⊢
  linarith

end
section
variable {ι : Type*} [DecidableEq ι] (g : ℝ → ℝ) (p d : ι → ℝ)

lemma ct_append_of_mem' (m r : List ι) (i : ι) (hi : i ∈ m) :
    Shared.completionTime p (m ++ r) i = Shared.completionTime p m i := by
  unfold Shared.completionTime Shared.completionAt
  rw [List.idxOf_append_of_mem hi, List.take_append_of_le_length (List.idxOf_lt_length_of_mem hi)]

lemma ct_append_last' (m : List ι) (j : ι) (hj : j ∉ m) :
    Shared.completionTime p (m ++ [j]) j = (m.map p).sum + p j := by
  unfold Shared.completionTime Shared.completionAt
  rw [List.idxOf_append_of_notMem hj]; simp

lemma esched_perm {J : Finset ι} {l l' : List ι} (hl : Shared.IsSchedule J l) (h : l'.Perm l) :
    Shared.IsSchedule J l' :=
  ⟨h.nodup_iff.2 hl.1, fun x => by rw [h.mem_iff, hl.2 x]⟩

lemma eopt_of_le {J : Finset ι} {l l' : List ι} (hl : IsOptimal g p d J l)
    (hs : Shared.IsSchedule J l') (h : totalPenalty g p d J l' ≤ totalPenalty g p d J l) :
    IsOptimal g p d J l' :=
  ⟨hs, fun l'' hl'' => h.trans (hl.2 l'' hl'')⟩

lemma eexists_opt (J : Finset ι) : ∃ l, IsOptimal g p d J l := by
  have hne : (J.toList.permutations.toFinset).Nonempty := ⟨J.toList, by simp⟩
  obtain ⟨l, hl, hmin⟩ := Finset.exists_min_image _ (totalPenalty g p d J) hne
  have hsched : ∀ l, l ∈ J.toList.permutations.toFinset ↔ Shared.IsSchedule J l := by
    intro l
    rw [List.mem_toFinset, List.mem_permutations]
    constructor
    · intro h
      exact ⟨h.nodup_iff.2 (Finset.nodup_toList J), fun x => by rw [h.mem_iff, Finset.mem_toList]⟩
    · intro h
      exact (List.perm_ext_iff_of_nodup h.1 (Finset.nodup_toList J)).2
        (fun x => by rw [h.2 x, Finset.mem_toList])
  exact ⟨l, (hsched l).1 hl, fun l' hl' => hmin l' ((hsched l').2 hl')⟩

lemma emove_perm (pre mid post : List ι) (j k : ι) :
    (pre ++ (mid ++ k :: j :: post)).Perm (pre ++ j :: (mid ++ k :: post)) := by
  apply List.Perm.append_left
  have := List.perm_middle (a := j) (l₁ := mid ++ [k]) (l₂ := post)
  simpa using this

lemma eswap_perm (pre mid post : List ι) (j k : ι) :
    (pre ++ j :: (mid ++ k :: post)).Perm (pre ++ k :: (mid ++ j :: post)) := by
  apply List.Perm.append_left
  exact ((List.perm_middle).cons j).trans ((List.Perm.swap k j _).trans ((List.perm_middle).symm.cons k))

lemma emove_tp (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (J : Finset ι) (hp : ∀ i ∈ J, 0 ≤ p i) (pre mid post : List ι) (j k : ι)
    (hl : Shared.IsSchedule J (pre ++ j :: (mid ++ k :: post))) (hd : d k ≤ d j)
    (hs : (pre.map p).sum + (mid.map p).sum + p k ≤ d j) :
    Shared.IsSchedule J (pre ++ (mid ++ k :: j :: post)) ∧
      totalPenalty g p d J (pre ++ (mid ++ k :: j :: post)) ≤
        totalPenalty g p d J (pre ++ j :: (mid ++ k :: post)) := by
  have hs' := esched_perm hl (emove_perm pre mid post j k)
  refine ⟨hs', ?_⟩
  have hj : j ∈ J := (hl.2 j).1 (by simp)
  rw [etp_eq g p d J _ hs', etp_eq g p d J _ hl, EFc_append g p d 0 pre, EFc_append g p d 0 pre]
  have := emove_le g p d hg hgm (0 + (pre.map p).sum) j k mid post (hp j hj) hd (by linarith)
  linarith

lemma eswap_tp (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (J : Finset ι) (hp : ∀ i ∈ J, 0 ≤ p i) (pre mid post : List ι) (j k : ι)
    (hl : Shared.IsSchedule J (pre ++ k :: (mid ++ j :: post))) (hpp : p j ≤ p k) (hd : d j ≤ d k) :
    Shared.IsSchedule J (pre ++ j :: (mid ++ k :: post)) ∧
      totalPenalty g p d J (pre ++ j :: (mid ++ k :: post)) ≤
        totalPenalty g p d J (pre ++ k :: (mid ++ j :: post)) := by
  have hs' := esched_perm hl (eswap_perm pre mid post j k)
  refine ⟨hs', ?_⟩
  have hj : j ∈ J := (hl.2 j).1 (by simp)
  have hS : 0 ≤ (mid.map p).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact hp y ((hl.2 y).1 (by simp [hy]))
  rw [etp_eq g p d J _ hs', etp_eq g p d J _ hl, EFc_append g p d 0 pre, EFc_append g p d 0 pre]
  have := eswap_le g p d hg hgm (0 + (pre.map p).sum) j k mid post (hp j hj) hS hpp hd
  linarith

lemma emem_after (s t : List ι) (k i : ι) (hn : (s ++ k :: t).Nodup) (hi : i ∈ s ++ k :: t)
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

lemma edecomp (l : List ι) (a b : ι) (hn : l.Nodup) (ha : a ∈ l) (hb : b ∈ l)
    (h : l.idxOf a < l.idxOf b) : ∃ pre mid post, l = pre ++ a :: (mid ++ b :: post) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  have hbt := emem_after s t a b hn hb h
  obtain ⟨m, q, rfl⟩ := List.append_of_mem hbt
  exact ⟨s, m, q, rfl⟩

lemma eprec (pre mid post : List ι) (a b : ι) (hn : (pre ++ a :: (mid ++ b :: post)).Nodup) :
    EmmonsTardiness.SPT.Precedes (pre ++ a :: (mid ++ b :: post)) a b := by
  have h1 := List.nodup_middle.1 hn
  rw [List.nodup_cons] at h1
  have hapre : a ∉ pre := fun h' => h1.1 (List.mem_append_left _ h')
  have hbpre : b ∉ pre := by
    intro h'
    have := List.disjoint_of_nodup_append hn h'
    exact this (by simp)
  have hab : b ≠ a := by
    intro h'; subst h'; exact h1.1 (List.mem_append_right _ (by simp))
  unfold EmmonsTardiness.SPT.Precedes
  rw [List.idxOf_append_of_notMem hapre, List.idxOf_append_of_notMem hbpre,
    List.idxOf_cons_self, List.idxOf_cons_ne _ hab.symm]
  omega

lemma eidx_ne (l : List ι) (a b : ι) (ha : a ∈ l) (hab : a ≠ b) : l.idxOf a ≠ l.idxOf b :=
  fun h => hab ((List.idxOf_inj ha).1 h)

end

section
variable {ι : Type*} [DecidableEq ι]

theorem ljr_core (g : ℝ → ℝ) (p d : ι → ℝ)
    (J : Finset ι) (j : ι) (hj : j ∈ J)
    (hlast : ∃ l : List ι, IsOptimal g p d J l ∧ l.getLast? = some j)
    (l' : List ι) (hl' : IsOptimal g p d (J.erase j) l') :
    IsOptimal g p d J (l' ++ [j]) := by
  obtain ⟨l, hopt, hla⟩ := hlast
  obtain ⟨m, rfl⟩ := List.getLast?_eq_some_iff.1 hla
  have hn2 : (j :: m).Nodup := by simpa using List.nodup_append_comm.1 hopt.1.1
  rcases List.nodup_cons.1 hn2 with ⟨hjm, hmn⟩
  have hjl' : j ∉ l' := fun h => by
    have := (hl'.1.2 j).1 h; simp at this
  have hsm : Shared.IsSchedule (J.erase j) m := by
    refine ⟨hmn, fun x => ?_⟩
    rw [Finset.mem_erase]
    constructor
    · intro hx; exact ⟨fun h => hjm (h ▸ hx), (hopt.1.2 x).1 (by simp [hx])⟩
    · intro hx
      have := (hopt.1.2 x).2 hx.2
      simp only [List.mem_append, List.mem_singleton] at this
      rcases this with h | h
      · exact h
      · exact absurd h hx.1
  have hsl : Shared.IsSchedule J (l' ++ [j]) := by
    refine ⟨?_, fun x => ?_⟩
    · have : (j :: l').Nodup := List.nodup_cons.2 ⟨hjl', hl'.1.1⟩
      exact List.nodup_append_comm.1 (by simpa using this)
    · simp only [List.mem_append, List.mem_singleton]
      rw [hl'.1.2 x, Finset.mem_erase]
      constructor
      · rintro (h | h)
        · exact h.2
        · exact h ▸ hj
      · intro hx
        by_cases h : x = j
        · exact Or.inr h
        · exact Or.inl ⟨h, hx⟩
  apply eopt_of_le g p d hopt hsl
  rw [etp_eq g p d J _ hsl, etp_eq g p d J _ hopt.1, EFc_append, EFc_append,
    ← etp_eq g p d _ _ hl'.1, ← etp_eq g p d _ _ hsm,
    elsum_eq _ l' hl'.1 p, elsum_eq _ m hsm p]
  have := hl'.2 m hsm
  linarith

theorem cor21_core (g : ℝ → ℝ) (p d : ι → ℝ)
    (J : Finset ι)
    (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (hp : ∀ i ∈ J, 0 ≤ p i)
    (j : ι) (hj : j ∈ J) (hmax : ∀ i ∈ J, d i ≤ d j)
    (hlast : ∑ i ∈ J, p i ≤ d j + p j) :
    ∃ l : List ι, IsOptimal g p d J l ∧ l.getLast? = some j := by
  obtain ⟨l, hl⟩ := eexists_opt g p d J
  obtain ⟨pre, rest, rfl⟩ := List.append_of_mem ((hl.1.2 j).2 hj)
  rcases List.eq_nil_or_concat rest with h | ⟨mid, k, rfl⟩
  · subst h; exact ⟨_, hl, by simp⟩
  · rw [List.concat_eq_append] at hl
    have hk : k ∈ J := (hl.1.2 k).1 (by simp)
    have hsum := elsum_eq J _ hl.1 p
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, List.map_nil,
      List.sum_nil] at hsum
    obtain ⟨hs, hle⟩ := emove_tp g p d hg hgm J hp pre mid [] j k (by simpa using hl.1) (hmax k hk)
      (by linarith)
    refine ⟨_, eopt_of_le g p d hl hs (by simpa using hle), by simp⟩

theorem cor22_core (g : ℝ → ℝ) (p d : ι → ℝ)
    (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0)) (l : List ι) :
    ∀ (J : Finset ι), (∀ i ∈ J, 0 ≤ p i) → Shared.IsSchedule J l → IsEDDOrder d l →
      (∀ i ∈ J, startTime p l i ≤ d i) → IsOptimal g p d J l := by
  induction l using List.reverseRecOn with
  | nil =>
    intro J _ hl _ _
    have hJ : J = ∅ := by
      ext x; simp only [Finset.notMem_empty, iff_false]; intro hx; simpa using (hl.2 x).2 hx
    subst hJ
    exact ⟨hl, fun l' _ => by simp [totalPenalty]⟩
  | append_singleton m j ih =>
    intro J hp hl hedd hW
    have hjJ : j ∈ J := (hl.2 j).1 (by simp)
    have hn2 : (j :: m).Nodup := by simpa using List.nodup_append_comm.1 hl.1
    rcases List.nodup_cons.1 hn2 with ⟨hjm, hmn⟩
    have hsm : Shared.IsSchedule (J.erase j) m := by
      refine ⟨hmn, fun x => ?_⟩
      rw [Finset.mem_erase]
      constructor
      · intro hx; exact ⟨fun h => hjm (h ▸ hx), (hl.2 x).1 (by simp [hx])⟩
      · intro hx
        have := (hl.2 x).2 hx.2
        simp only [List.mem_append, List.mem_singleton] at this
        rcases this with h | h
        · exact h
        · exact absurd h hx.1
    have hpw := List.pairwise_append.1 hedd
    have hoptm : IsOptimal g p d (J.erase j) m := by
      refine ih (J.erase j) (fun i hi => hp i (Finset.mem_of_mem_erase hi)) hsm hpw.1 ?_
      intro i hi
      have him : i ∈ m := (hsm.2 i).2 hi
      have := hW i (Finset.mem_of_mem_erase hi)
      unfold startTime at this ⊢
      rwa [ct_append_of_mem' p m [j] i him] at this
    have hmax : ∀ i ∈ J, d i ≤ d j := by
      intro i hi
      by_cases h : i = j
      · rw [h]
      · have : i ∈ m := (hsm.2 i).2 (Finset.mem_erase.2 ⟨h, hi⟩)
        exact hpw.2.2 i this j (by simp)
    have hsum := elsum_eq J _ hl p
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, List.map_nil,
      List.sum_nil] at hsum
    have hWj := hW j hjJ
    unfold startTime at hWj
    rw [ct_append_last' p m j hjm] at hWj
    have c21 := cor21_core g p d J hg hgm hp j hjJ hmax (by linarith)
    exact ljr_core g p d J j hjJ c21 m hoptm

end

end EmmonsTardiness.EDD

open EmmonsTardiness.EDD


theorem solution {ι : Type*} [DecidableEq ι] (g : ℝ → ℝ) (p d : ι → ℝ)
    (J : Finset ι)
    (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (hp : ∀ i ∈ J, 0 ≤ p i)
    (l : List ι) (hl : MooreLateJobs.Shared.IsSchedule J l) (hedd : IsEDDOrder d l)
    (hW : ∀ i ∈ J, startTime p l i ≤ d i) :
    IsOptimal g p d J l := by
  exact cor22_core g p d hg hgm l J hp hl hedd hW
