-- Prove2me | solution 2 for BurnInBatch.AgreeTmax.dp2_correct
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T15:48:21.078275+00:00
-- url     : https://prove2.me/submissions/228621b7-9470-45f8-8ca9-5f0d096aba9c

import Mathlib
import Definitions.Def_BurnInBatch_AgreeTmax_Model
import Definitions.Def_BurnInBatch_AgreeTmax_DP2
import Theorems.Thm_BurnInBatch_AgreeTmax_consecutive_optimal

-- carved verbatim out of submission 30830527-2ca6-4f35-8f44-350e413af16f, lines 999-1005

section
open BurnInBatch
open BurnInBatch.AgreeTmax
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
variable {α : Type*} [DecidableEq α]

def tm (p : α → ℕ) (P : Finset α) : ℕ := P.sup p

def tms (p : α → ℕ) (S : List (Finset α)) : ℕ := (S.map (tm p)).sum

def Feas (p d : α → ℕ) : ℕ → List (Finset α) → Prop
  | _, [] => True
  | θ, P :: R => (∀ i ∈ P, θ + tm p P ≤ d i) ∧ Feas p d (θ + tm p P) R

noncomputable def mn (r : α → ℕ) (P : Finset α) : ℕ := sInf (r '' (P : Set α))

theorem mn_le {r : α → ℕ} {P : Finset α} {x : α} (hx : x ∈ P) : mn r P ≤ r x :=
  Nat.sInf_le ⟨x, hx, rfl⟩

theorem exists_mn {r : α → ℕ} {P : Finset α} (h : P.Nonempty) : ∃ x ∈ P, r x = mn r P := by
  have : (r '' (P : Set α)).Nonempty := Set.Nonempty.image r (Finset.coe_nonempty.mpr h)
  obtain ⟨x, hx, hxe⟩ := Nat.sInf_mem this
  exact ⟨x, hx, hxe⟩

theorem tm_le {p : α → ℕ} {P : Finset α} {x : α} (hx : x ∈ P) : p x ≤ tm p P :=
  Finset.le_sup (f := p) hx

theorem tm_le_of {p : α → ℕ} {P : Finset α} {c : ℕ} (h : ∀ x ∈ P, p x ≤ c) : tm p P ≤ c :=
  Finset.sup_le h

theorem tms_append (p : α → ℕ) (S1 S2 : List (Finset α)) :
    tms p (S1 ++ S2) = tms p S1 + tms p S2 := by
  simp [tms]

theorem feas_append {p d : α → ℕ} : ∀ (S1 S2 : List (Finset α)) (θ : ℕ),
    Feas p d θ (S1 ++ S2) ↔ Feas p d θ S1 ∧ Feas p d (θ + tms p S1) S2 := by
  intro S1
  induction S1 with
  | nil => intro S2 θ; simp [Feas, tms]
  | cons P R ih =>
    intro S2 θ
    have e : θ + tms p (P :: R) = θ + tm p P + tms p R := by simp [tms]; omega
    simp only [List.cons_append, Feas, ih, e]
    tauto

theorem feas_iff {n : ℕ} (p d : Fin n → ℕ) : ∀ (S : List (Finset (Fin n))) (θ : ℕ),
    Feas p d θ S ↔ ∀ (k : ℕ) (hk : k < S.length), ∀ i ∈ S[k],
      θ + ((S.take (k + 1)).map (tm p)).sum ≤ d i := by
  intro S
  induction S with
  | nil => intro θ; simp [Feas]
  | cons P R ih =>
    intro θ
    rw [Feas, ih]
    constructor
    · rintro ⟨h0, h1⟩ k hk i hi
      rcases k with _ | k
      · simp at hi ⊢
        exact h0 i hi
      · have := h1 k (by simpa using hk) i (by simpa using hi)
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
        omega
    · intro h
      refine ⟨fun i hi => ?_, fun k hk i hi => ?_⟩
      · have := h 0 (by simp) i (by simpa using hi)
        simpa using this
      · have := h (k + 1) (by simpa using hk) i (by simpa using hi)
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons] at this
        omega

theorem tmax_zero_iff {n : ℕ} (p d : Fin n → ℕ) (S : List (Finset (Fin n))) :
    Tmax p d S = 0 ↔ Feas p d 0 S := by
  rw [feas_iff]
  unfold Tmax
  constructor
  · intro h k hk i hi
    have h1 := (Finset.sup_eq_bot_iff _ _).mp (show _ = (⊥ : ℕ) from h) ⟨k, hk⟩ (Finset.mem_univ _)
    have h2 := (Finset.sup_eq_bot_iff _ _).mp h1 i hi
    have : batchCompletion p S k - d i = 0 := h2
    unfold batchCompletion at this
    have : ((S.take (k + 1)).map (batchTime p)).sum ≤ d i := by omega
    simp only [zero_add]
    exact this
  · intro h
    show _ = (⊥ : ℕ)
    rw [Finset.sup_eq_bot_iff]
    intro k _
    rw [Finset.sup_eq_bot_iff]
    intro i hi
    have := h k.1 k.2 i hi
    simp only [zero_add] at this
    show batchCompletion p S k.1 - d i = 0
    unfold batchCompletion
    have e : ((S.take (k.1 + 1)).map (batchTime p)).sum = ((S.take (k.1 + 1)).map (tm p)).sum := rfl
    rw [e]; omega

theorem makespan_eq {n : ℕ} (p : Fin n → ℕ) (S : List (Finset (Fin n))) :
    makespan p S = tms p S := rfl

noncomputable def Fv {n : ℕ} (B : ℕ) (p d : Fin n → ℕ) (j : ℕ) (i : ℕ) : ℕ∞ :=
  if dp2 B p d (i - 1) + (pOf p j : ℕ∞) ≤ (dOf d i : ℕ∞) then
    dp2 B p d (i - 1) + (pOf p j : ℕ∞)
  else ⊤

theorem dp2_unfold {n : ℕ} (B : ℕ) (p d : Fin n → ℕ) {j : ℕ} (hj : 1 ≤ j) :
    dp2 B p d j = (List.range' (max 1 (j - B + 1)) (j + 1 - max 1 (j - B + 1))).foldr
      (fun i acc => if Fv B p d j i ≤ acc then Fv B p d j i else acc) ⊤ := by
  rw [dp2, if_neg (by omega)]
  exact List.foldr_attach (f := fun i acc => if Fv B p d j i ≤ acc then Fv B p d j i else acc)

theorem foldr_min (F : ℕ → ℕ∞) (l : List ℕ) :
    (∀ i ∈ l, l.foldr (fun i acc => if F i ≤ acc then F i else acc) ⊤ ≤ F i) ∧
    (l.foldr (fun i acc => if F i ≤ acc then F i else acc) ⊤ = ⊤ ∨
      ∃ i ∈ l, l.foldr (fun i acc => if F i ≤ acc then F i else acc) ⊤ = F i) := by
  induction l with
  | nil => exact ⟨by simp, Or.inl rfl⟩
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases h : F a ≤ l.foldr (fun i acc => if F i ≤ acc then F i else acc) ⊤
    · rw [if_pos h]
      refine ⟨fun i hi => ?_, Or.inr ⟨a, List.mem_cons_self, rfl⟩⟩
      rcases List.mem_cons.mp hi with rfl | hi
      · exact le_rfl
      · exact h.trans (ih.1 i hi)
    · rw [if_neg h]
      refine ⟨fun i hi => ?_, ?_⟩
      · rcases List.mem_cons.mp hi with rfl | hi
        · exact (not_le.mp h).le
        · exact ih.1 i hi
      · rcases ih.2 with h1 | ⟨i, hi, h1⟩
        · exact Or.inl h1
        · exact Or.inr ⟨i, List.mem_cons_of_mem _ hi, h1⟩

theorem dp2_le_Fv {n : ℕ} (B : ℕ) (p d : Fin n → ℕ) {j : ℕ} (hj : 1 ≤ j) {i : ℕ}
    (h1 : max 1 (j - B + 1) ≤ i) (h2 : i ≤ j) : dp2 B p d j ≤ Fv B p d j i := by
  rw [dp2_unfold B p d hj]
  apply (foldr_min (Fv B p d j) _).1
  rw [List.mem_range'_1]
  omega

theorem dp2_attained {n : ℕ} (B : ℕ) (p d : Fin n → ℕ) {j : ℕ} (hj : 1 ≤ j) :
    dp2 B p d j = ⊤ ∨ ∃ i, max 1 (j - B + 1) ≤ i ∧ i ≤ j ∧ dp2 B p d j = Fv B p d j i := by
  have := (foldr_min (Fv B p d j) (List.range' (max 1 (j - B + 1)) (j + 1 - max 1 (j - B + 1)))).2
  rw [← dp2_unfold B p d hj] at this
  rcases this with h | ⟨i, hi, h⟩
  · exact Or.inl h
  · rw [List.mem_range'_1] at hi
    exact Or.inr ⟨i, hi.1, by omega, h⟩

def bs (n i0 j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun x : Fin n => i0 ≤ x.val ∧ x.val < j

theorem mem_bs {n i0 j : ℕ} {x : Fin n} : x ∈ bs n i0 j ↔ i0 ≤ x.val ∧ x.val < j := by
  simp [bs]

theorem bs_card {n i0 j : ℕ} (hj : j ≤ n) : (bs n i0 j).card = j - i0 := by
  rw [← Nat.card_Ico i0 j]
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    have := mem_bs.mp hx
    simp only [Finset.mem_Ico]; exact this
  · intro x _ y _ h; exact Fin.ext h
  · intro m hm
    simp only [Finset.mem_Ico] at hm
    exact ⟨⟨m, by omega⟩, mem_bs.mpr hm, rfl⟩

theorem bs_nonempty {n i0 j : ℕ} (hi : i0 < j) (hj : j ≤ n) : (bs n i0 j).Nonempty :=
  ⟨⟨i0, by omega⟩, mem_bs.mpr ⟨le_rfl, hi⟩⟩

theorem bs_tm {n i0 j : ℕ} (p : Fin n → ℕ) (hp : Monotone p) (hi : i0 < j) (hj : j ≤ n) :
    tm p (bs n i0 j) = p ⟨j - 1, by omega⟩ := by
  apply le_antisymm
  · apply tm_le_of
    intro x hx
    have := mem_bs.mp hx
    exact hp (Fin.le_def.mpr (by simp; omega))
  · exact tm_le (mem_bs.mpr ⟨by simp; omega, by simp; omega⟩)

theorem mem_jobs {n j : ℕ} {x : Fin n} : x ∈ jobsUpTo n j ↔ x.val < j := by
  simp [jobsUpTo]

theorem append_block {n B i0 j : ℕ} (hi : i0 < j) (hj : j ≤ n) (hB : j - i0 ≤ B)
    {S0 : List (Finset (Fin n))} (hv : IsValid B (jobsUpTo n i0) S0) :
    IsValid B (jobsUpTo n j) (S0 ++ [bs n i0 j]) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    rcases List.mem_append.mp hP with hP | hP
    · exact h1 P hP
    · rw [List.mem_singleton.mp hP]; exact bs_nonempty hi hj
  · intro P hP
    rcases List.mem_append.mp hP with hP | hP
    · exact h2 P hP
    · rw [List.mem_singleton.mp hP, bs_card hj]; exact hB
  · intro P hP x hx
    rcases List.mem_append.mp hP with hP | hP
    · have := h3 P hP hx
      rw [mem_jobs] at this ⊢; omega
    · rw [List.mem_singleton.mp hP] at hx
      rw [mem_jobs]; exact (mem_bs.mp hx).2
  · rw [List.pairwise_append]
    refine ⟨h4, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton.mp hb]
    rw [Finset.disjoint_left]
    intro x hxa hxb
    have := mem_jobs.mp (h3 a ha hxa)
    have := (mem_bs.mp hxb).1
    omega
  · intro x hx
    rw [mem_jobs] at hx
    by_cases h : x.val < i0
    · obtain ⟨P, hP, hxP⟩ := h5 x (mem_jobs.mpr h)
      exact ⟨P, List.mem_append_left _ hP, hxP⟩
    · exact ⟨bs n i0 j, by simp, mem_bs.mpr ⟨by omega, hx⟩⟩

theorem consec_pairwise {n : ℕ} {S : List (Finset (Fin n))} (hc : IsConsecutive S) :
    S.Pairwise (fun A B => ∀ x ∈ A, ∀ y ∈ B, x < y) :=
  List.pairwise_iff_getElem.mpr (fun a b ha hb hab => hc.2 ⟨a, ha⟩ ⟨b, hb⟩ hab)

theorem last_block {n B j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) {S : List (Finset (Fin n))}
    (hv : IsValid B (jobsUpTo n j) S) (hc : IsConsecutive S) :
    ∃ (S0 : List (Finset (Fin n))) (i0 : ℕ), S = S0 ++ [bs n i0 j] ∧ i0 < j ∧ j - i0 ≤ B ∧
      IsValid B (jobsUpTo n i0) S0 := by
  have hv0 := hv
  obtain ⟨h1, h2, h3, h4, h5⟩ := hv0
  have hjm : (⟨j - 1, by omega⟩ : Fin n) ∈ jobsUpTo n j := mem_jobs.mpr (by simp; omega)
  obtain ⟨P0, hP0, hjP0⟩ := h5 _ hjm
  rcases List.eq_nil_or_concat S with hS | ⟨S0, Q, hS⟩
  · subst hS; simp at hP0
  · rw [List.concat_eq_append] at hS
    have hpw := consec_pairwise hc
    rw [hS] at hpw h1 h2 h3 h4 h5 hP0
    have hQne := h1 Q (by simp)
    have hQJ := h3 Q (by simp)
    obtain ⟨y0, hy0, hy0e⟩ := exists_mn (r := fun i : Fin n => i.val) hQne
    set i0 := mn (fun i : Fin n => i.val) Q with hi0
    have hpw' := List.pairwise_append.mp hpw
    have hord : ∀ P ∈ S0, ∀ x ∈ P, ∀ y ∈ Q, x < y := by
      intro P hP x hx y hy
      exact hpw'.2.2 P hP Q (by simp) x hx y hy
    -- j-1 ∈ Q
    have hjQ : (⟨j - 1, by omega⟩ : Fin n) ∈ Q := by
      rcases List.mem_append.mp hP0 with hP | hP
      · exfalso
        obtain ⟨q, hq⟩ := hQne
        have h6 := hord P0 hP _ hjP0 q hq
        have h7 := mem_jobs.mp (hQJ hq)
        rw [Fin.lt_def] at h6
        simp only at h6
        omega
      · rw [List.mem_singleton.mp hP] at hjP0; exact hjP0
    have hmin : ∀ y ∈ Q, i0 ≤ y.val := fun y hy => mn_le (r := fun i : Fin n => i.val) hy
    have hQeq : Q = bs n i0 j := by
      ext x
      rw [mem_bs]
      constructor
      · intro hx
        exact ⟨hmin x hx, mem_jobs.mp (hQJ hx)⟩
      · rintro ⟨hx1, hx2⟩
        have := hc.1 Q (by rw [hS]; simp) y0 x ⟨j - 1, by omega⟩ hy0 hjQ
          (Fin.le_def.mpr (by rw [← hy0e] at hx1; exact hx1))
          (Fin.le_def.mpr (by simp; omega))
        exact this
    have hi0j : i0 < j := by
      have := mem_jobs.mp (hQJ hy0)
      rw [← hy0e]; exact this
    have hcard : j - i0 ≤ B := by
      have := h2 Q (by simp)
      rw [hQeq, bs_card hjn] at this
      exact this
    refine ⟨S0, i0, by rw [hS, hQeq], hi0j, hcard, ?_, ?_, ?_, ?_, ?_⟩
    · intro P hP; exact h1 P (by simp [hP])
    · intro P hP; exact h2 P (by simp [hP])
    · intro P hP x hx
      have := hord P hP x hx y0 hy0
      rw [Fin.lt_def] at this
      rw [mem_jobs]; omega
    · exact (List.pairwise_append.mp h4).1
    · intro x hx
      have hxj : x ∈ jobsUpTo n j := by
        rw [mem_jobs] at hx ⊢; omega
      obtain ⟨P, hP, hxP⟩ := h5 x hxj
      rcases List.mem_append.mp hP with hP | hP
      · exact ⟨P, hP, hxP⟩
      · exfalso
        rw [List.mem_singleton.mp hP] at hxP
        have := hmin x hxP
        rw [mem_jobs] at hx
        omega

noncomputable def G {n : ℕ} (B : ℕ) (p d : Fin n → ℕ) (j : ℕ) : ℕ∞ :=
  ⨅ (S : List (Finset (Fin n))) (_ : IsValid B (jobsUpTo n j) S ∧ Tmax p d S = 0),
    (makespan p S : ℕ∞)

theorem G_le {n B j : ℕ} (p d : Fin n → ℕ) {S : List (Finset (Fin n))}
    (hv : IsValid B (jobsUpTo n j) S) (ht : Tmax p d S = 0) :
    G B p d j ≤ (makespan p S : ℕ∞) :=
  iInf₂_le S ⟨hv, ht⟩

theorem G_eq_of_min {n B j : ℕ} (p d : Fin n → ℕ) {S : List (Finset (Fin n))}
    (hv : IsValid B (jobsUpTo n j) S) (ht : Tmax p d S = 0)
    (hmin : ∀ S' : List (Finset (Fin n)), IsValid B (jobsUpTo n j) S' → Tmax p d S' = 0 →
      makespan p S ≤ makespan p S') :
    G B p d j = (makespan p S : ℕ∞) := by
  apply le_antisymm (G_le p d hv ht)
  refine le_iInf₂ (fun S' h => ?_)
  exact_mod_cast hmin S' h.1 h.2

theorem G_top {n B j : ℕ} (p d : Fin n → ℕ)
    (h : ¬ ∃ S : List (Finset (Fin n)), IsValid B (jobsUpTo n j) S ∧ Tmax p d S = 0) :
    G B p d j = ⊤ := by
  apply le_antisymm le_top
  refine le_iInf₂ (fun S hS => ?_)
  exact absurd ⟨S, hS⟩ h

theorem feas_last {n : ℕ} (p d : Fin n → ℕ) (S0 : List (Finset (Fin n))) (Q : Finset (Fin n)) :
    Feas p d 0 (S0 ++ [Q]) ↔ Feas p d 0 S0 ∧ ∀ x ∈ Q, tms p S0 + tm p Q ≤ d x := by
  rw [feas_append]
  simp [Feas]

theorem dp2_eq_G {n B : ℕ} (hB : 0 < B) (p d : Fin n → ℕ) (hd : Monotone d) (hp : Monotone p) :
    ∀ j, j ≤ n → dp2 B p d j = G B p d j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hjn
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · have h0 : dp2 B p d 0 = 0 := by rw [dp2]; simp
    rw [h0]
    apply le_antisymm zero_le
    have hv : IsValid B (jobsUpTo n 0) ([] : List (Finset (Fin n))) := by
      simp [IsValid, jobsUpTo]
    have ht : Tmax p d ([] : List (Finset (Fin n))) = 0 := by simp [Tmax]
    have := G_le p d hv ht
    simpa [makespan] using this
  · have hpj : pOf p j = p ⟨j - 1, by omega⟩ := by
      simp only [pOf]; rw [dif_pos ⟨by omega, hjn⟩]
    apply le_antisymm
    · -- dp2 ≤ G
      by_cases hex : ∃ S : List (Finset (Fin n)), IsValid B (jobsUpTo n j) S ∧ Tmax p d S = 0
      · obtain ⟨Ss, hvS, htS, hcons, hmin⟩ := BurnInBatch.AgreeTmax.consecutive_optimal hB p d hd hp j hjn hex
        rw [G_eq_of_min p d hvS htS hmin]
        obtain ⟨S0, i0, rfl, hi0, hcard, hv0⟩ := last_block hj1 hjn hvS hcons
        have hF := (tmax_zero_iff p d _).mp htS
        rw [feas_last] at hF
        have hF0 := hF.1
        have ht0 : Tmax p d S0 = 0 := (tmax_zero_iff p d S0).mpr hF0
        have hGi0 : dp2 B p d i0 = G B p d i0 := ih i0 hi0 (by omega)
        have hle0 := G_le p d hv0 ht0
        have htmbs := bs_tm p hp hi0 hjn
        have hdd : tms p S0 + p ⟨j - 1, by omega⟩ ≤ d ⟨i0, by omega⟩ := by
          have := hF.2 ⟨i0, by omega⟩ (mem_bs.mpr ⟨le_rfl, hi0⟩)
          rw [htmbs] at this
          exact this
        have hmk : makespan p (S0 ++ [bs n i0 j]) = tms p S0 + p ⟨j - 1, by omega⟩ := by
          rw [makespan_eq, tms_append, ← htmbs]
          simp [tms]
        have hcond : dp2 B p d (i0 + 1 - 1) + (pOf p j : ℕ∞) ≤ (dOf d (i0 + 1) : ℕ∞) := by
          have hdo : dOf d (i0 + 1) = d ⟨i0, by omega⟩ := by
            simp only [dOf]; rw [dif_pos ⟨by omega, by omega⟩]; rfl
          rw [hdo, hpj, Nat.add_sub_cancel, hGi0]
          calc G B p d i0 + (p ⟨j - 1, by omega⟩ : ℕ∞) ≤ (makespan p S0 : ℕ∞) + (p ⟨j - 1, by omega⟩ : ℕ∞) :=
                add_le_add_left hle0 _
            _ ≤ (d ⟨i0, by omega⟩ : ℕ∞) := by
                have : makespan p S0 + p ⟨j - 1, by omega⟩ ≤ d ⟨i0, by omega⟩ := hdd
                exact_mod_cast this
        have h1 := dp2_le_Fv B p d hj1 (i := i0 + 1) (by omega) (by omega)
        refine h1.trans ?_
        unfold Fv
        rw [if_pos hcond, hmk, Nat.add_sub_cancel, hGi0, hpj]
        push_cast
        exact add_le_add_left hle0 _
      · rw [G_top p d hex]; exact le_top
    · -- G ≤ dp2
      rcases dp2_attained B p d hj1 with h | ⟨i, hi1, hi2, h⟩
      · rw [h]; exact le_top
      · rw [h]
        unfold Fv
        split_ifs with hcond
        · have hi0 : i - 1 < j := by omega
          have hGi : dp2 B p d (i - 1) = G B p d (i - 1) := ih (i - 1) hi0 (by omega)
          have hne : dp2 B p d (i - 1) ≠ ⊤ := by
            intro htop
            rw [htop, top_add] at hcond
            exact absurd hcond (by rw [top_le_iff]; exact ENat.natCast_ne_top _)
          rw [hGi] at hne hcond
          have hex' : ∃ S : List (Finset (Fin n)), IsValid B (jobsUpTo n (i - 1)) S ∧ Tmax p d S = 0 := by
            by_contra hno
            exact hne (G_top p d hno)
          obtain ⟨S0, hv0, ht0, -, hmin0⟩ := BurnInBatch.AgreeTmax.consecutive_optimal hB p d hd hp (i - 1) (by omega) hex'
          have hGm : G B p d (i - 1) = (makespan p S0 : ℕ∞) := G_eq_of_min p d hv0 ht0 hmin0
          rw [hGm, hpj] at hcond
          have hdo : dOf d i = d ⟨i - 1, by omega⟩ := by
            simp only [dOf]; rw [dif_pos ⟨by omega, by omega⟩]
          rw [hdo] at hcond
          have hcond' : makespan p S0 + p ⟨j - 1, by omega⟩ ≤ d ⟨i - 1, by omega⟩ := by
            exact_mod_cast hcond
          have hvS := append_block (B := B) hi0 hjn (by omega) hv0
          have htmbs := bs_tm p hp hi0 hjn
          have hF0 := (tmax_zero_iff p d S0).mp ht0
          have hFS : Feas p d 0 (S0 ++ [bs n (i - 1) j]) := by
            rw [feas_last]
            refine ⟨hF0, fun x hx => ?_⟩
            rw [htmbs]
            have hx' := mem_bs.mp hx
            have := hd (show (⟨i - 1, by omega⟩ : Fin n) ≤ x from Fin.le_def.mpr (by simp; omega))
            have e : makespan p S0 = tms p S0 := rfl
            omega
          have htS := (tmax_zero_iff p d _).mpr hFS
          have hmk : makespan p (S0 ++ [bs n (i - 1) j]) = makespan p S0 + p ⟨j - 1, by omega⟩ := by
            rw [makespan_eq, tms_append, ← htmbs]
            rw [show makespan p S0 = tms p S0 from rfl]
            simp [tms]
          have := G_le p d hvS htS
          rw [hmk] at this
          rw [hGi, hGm, hpj]
          push_cast at this ⊢
          exact this
        · exact le_top

end

section
open BurnInBatch.AgreeTmax

theorem solution {n B : ℕ} (hB : 0 < B) (p d : Fin n → ℕ)
    (hd : Monotone d) (hp : Monotone p) (j : ℕ) (hj : j ≤ n) :
    dp2 B p d j =
      ⨅ (S : List (Finset (Fin n))) (_ : IsValid B (jobsUpTo n j) S ∧ Tmax p d S = 0),
        (makespan p S : ℕ∞) := by
  exact dp2_eq_G hB p d hd hp j hj

end
