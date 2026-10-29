-- Prove2me | solution 1 for EFXGenVal.TwoVal.theorem_14
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T02:04:37.065614+00:00
-- url     : https://prove2.me/submissions/671db125-c7aa-4a65-bd8d-1482da435753

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_EFXGenVal_TwoVal_Setting

set_option autoImplicit false

open LittleCharity.EFX EFXGenVal.TwoVal

namespace PV0F

/-! ## Sorted lists -/

theorem sort_cons_min {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) (x : ι)
    (hx : x ∈ s) (hmin : ∀ y ∈ s, f x ≤ f y) :
    (s.val.map f).sort (· ≤ ·) = f x :: ((s.erase x).val.map f).sort (· ≤ ·) := by
  apply List.Perm.eq_of_sortedLE
  · exact (Multiset.pairwise_sort _ _).sortedLE
  · apply List.Pairwise.sortedLE
    rw [List.pairwise_cons]
    refine ⟨?_, Multiset.pairwise_sort _ _⟩
    intro a ha
    rw [Multiset.mem_sort, Multiset.mem_map] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    exact hmin y (Finset.mem_of_mem_erase hy)
  · rw [← Multiset.coe_eq_coe, ← Multiset.cons_coe, Multiset.sort_eq, Multiset.sort_eq,
      ← Multiset.map_cons, Finset.erase_val, Multiset.cons_erase (Finset.mem_val.mpr hx)]

theorem lex_of_pareto {ι : Type*} [DecidableEq ι] (f g : ι → ℝ) (s : Finset ι) :
    (∀ i ∈ s, f i ≤ g i) → (∃ i ∈ s, f i < g i) → ∀ l1 l2 : List ℝ,
    List.Lex (· < ·) ((s.val.map f).sort (· ≤ ·) ++ l1) ((s.val.map g).sort (· ≤ ·) ++ l2) := by
  induction s using Finset.strongInduction with
  | _ s ih =>
  intro hle hlt l1 l2
  have hne : s.Nonempty := by
    obtain ⟨i, hi, _⟩ := hlt
    exact ⟨i, hi⟩
  obtain ⟨j, hj, hjmin⟩ := s.exists_min_image g hne
  obtain ⟨k, hk, hkmin⟩ := s.exists_min_image f hne
  rcases lt_or_eq_of_le (show f k ≤ g j from (hkmin j hj).trans (hle j hj)) with h | h
  · rw [sort_cons_min s g j hj hjmin, sort_cons_min s f k hk hkmin]
    simp only [List.cons_append]
    exact List.Lex.rel h
  · have hfj : f j = g j := le_antisymm (hle j hj) (h ▸ hkmin j hj)
    rw [sort_cons_min s g j hj hjmin,
      sort_cons_min s f j hj (fun y hy => (hfj.trans h.symm).le.trans (hkmin y hy)), hfj]
    simp only [List.cons_append]
    apply List.Lex.cons
    apply ih (s.erase j) (Finset.erase_ssubset hj)
    · intro i hi
      exact hle i (Finset.mem_of_mem_erase hi)
    · obtain ⟨i, hi, hlti⟩ := hlt
      refine ⟨i, Finset.mem_erase.mpr ⟨?_, hi⟩, hlti⟩
      rintro rfl
      exact absurd hfj (ne_of_lt hlti)

theorem lex_of_head {ι : Type*} [DecidableEq ι] (f g : ι → ℝ) (s : Finset ι) (a : ι)
    (ha : a ∈ s) (h : ∀ i ∈ s, f a < g i) (l1 l2 : List ℝ) :
    List.Lex (· < ·) ((s.val.map f).sort (· ≤ ·) ++ l1) ((s.val.map g).sort (· ≤ ·) ++ l2) := by
  obtain ⟨j, hj, hjmin⟩ := s.exists_min_image g ⟨a, ha⟩
  obtain ⟨k, hk, hkmin⟩ := s.exists_min_image f ⟨a, ha⟩
  rw [sort_cons_min s g j hj hjmin, sort_cons_min s f k hk hkmin]
  simp only [List.cons_append]
  exact List.Lex.rel ((hkmin a ha).trans_lt (h j hj))

theorem lex_append_left (l : List ℝ) {a b : List ℝ} (h : List.Lex (· < ·) a b) :
    List.Lex (· < ·) (l ++ a) (l ++ b) := by
  induction l with
  | nil => simpa using h
  | cons x l ih =>
    simp only [List.cons_append]
    exact List.Lex.cons ih

variable {n m : ℕ}

theorem plex_of_pareto (v : Fin n → Finset (Fin m) → ℝ) (va vb : Finset (Fin m) → ℝ)
    (A : Finset (Fin n)) (hA : ∀ i ∈ A, v i = va) (hB : ∀ i ∉ A, v i = vb)
    (X Y : Fin n → Finset (Fin m))
    (hle : ∀ i, v i (X i) ≤ v i (Y i)) (hlt : ∃ i, v i (X i) < v i (Y i)) :
    PLexGT va vb A Y X := by
  classical
  unfold PLexGT psi
  obtain ⟨i, hi⟩ := hlt
  by_cases hex : ∃ j ∈ A, va (X j) < va (Y j)
  · exact lex_of_pareto (fun j => va (X j)) (fun j => va (Y j)) A
      (fun j hj => by have := hle j; rwa [hA j hj] at this) hex _ _
  · push_neg at hex
    have heq : A.val.map (fun j => va (X j)) = A.val.map (fun j => va (Y j)) := by
      apply Multiset.map_congr rfl
      intro j hj
      have := hle j
      rw [hA j hj] at this
      exact le_antisymm this (hex j hj)
    rw [heq]
    apply lex_append_left
    have hiA : i ∉ A := by
      intro hiA
      rw [hA i hiA] at hi
      exact absurd (hex i hiA) (not_le.mpr hi)
    have := lex_of_pareto (fun j => vb (X j)) (fun j => vb (Y j)) Aᶜ
      (fun j hj => by have := hle j; rwa [hB j (Finset.mem_compl.mp hj)] at this)
      ⟨i, Finset.mem_compl.mpr hiA, by rwa [hB i hiA] at hi⟩ [] []
    simpa using this

theorem plex_of_head (va vb : Finset (Fin m) → ℝ) (A : Finset (Fin n))
    (X Y : Fin n → Finset (Fin m)) (a0 : Fin n) (ha0 : a0 ∈ A)
    (h : ∀ i ∈ A, va (X a0) < va (Y i)) : PLexGT va vb A Y X := by
  classical
  unfold PLexGT psi
  exact lex_of_head (fun j => va (X j)) (fun j => va (Y j)) A a0 ha0 h _ _

/-! ## Valuations, safety, kappa -/

def Safe (v : Fin n → Finset (Fin m) → ℝ) (X : Fin n → Finset (Fin m))
    (S : Finset (Fin m)) (i : Fin n) : Prop :=
  ∀ h ∈ S, v i (S.erase h) ≤ v i (X i)

theorem safe_lift {v : Fin n → Finset (Fin m) → ℝ} {X Y : Fin n → Finset (Fin m)}
    {S : Finset (Fin m)} {i : Fin n} (hS : Safe v X S i) (hle : v i (X i) ≤ v i (Y i)) :
    Safe v Y S i :=
  fun h hh => (hS h hh).trans hle

theorem semi_iff (v : Fin n → Finset (Fin m) → ℝ) (A : Finset (Fin n))
    (X : Fin n → Finset (Fin m)) :
    IsSemiEFX v A X ↔ ∀ i j, (i ∈ A ∨ j ∈ A) → Safe v X (X j) i := by
  unfold IsSemiEFX EFXEnvies Safe
  constructor
  · rintro ⟨h1, h2⟩ i j hij h hh
    by_cases hi : i ∈ A
    · exact not_lt.mp fun hc => h1 i hi j ⟨h, hh, hc⟩
    · have hj : j ∈ A := hij.resolve_left hi
      exact not_lt.mp fun hc => h2 i hi j hj ⟨h, hh, hc⟩
  · intro H
    refine ⟨fun i hi j ⟨h, hh, hc⟩ => ?_, fun i hi j hj ⟨h, hh, hc⟩ => ?_⟩
    · exact absurd (H i j (Or.inl hi) h hh) (not_le.mpr hc)
    · exact absurd (H i j (Or.inr hj) h hh) (not_le.mpr hc)

theorem v_nonneg {v : Fin n → Finset (Fin m) → ℝ} (hnorm : IsNormalized v)
    (hmono : IsMonotoneVal v) (i : Fin n) (S : Finset (Fin m)) : 0 ≤ v i S := by
  have := hmono i ∅ S (Finset.empty_subset _)
  rwa [hnorm i] at this

theorem v_strict {v : Fin n → Finset (Fin m) → ℝ} (hmono : IsMonotoneVal v)
    (hnd : IsNonDegenerate v) {i : Fin n} {S T : Finset (Fin m)} (h : S ⊂ T) :
    v i S < v i T :=
  lt_of_le_of_ne (hmono i S T h.subset) (hnd i S T h.ne)

theorem v_pos {v : Fin n → Finset (Fin m) → ℝ} (hnorm : IsNormalized v)
    (hmono : IsMonotoneVal v) (hnd : IsNonDegenerate v) {i : Fin n} {S : Finset (Fin m)}
    (h : S.Nonempty) : 0 < v i S := by
  have := v_strict hmono hnd (i := i) (Finset.empty_ssubset.mpr h)
  rwa [hnorm i] at this

theorem not_mem_pool {X : Fin n → Finset (Fin m)} {g : Fin m} (hg : g ∈ pool X) (w : Fin n) :
    g ∉ X w := by
  intro hw
  simp only [pool, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_biUnion, true_and] at hg
  exact hg ⟨w, hw⟩

theorem mem_pool {X : Fin n → Finset (Fin m)} {g : Fin m} (h : ∀ w, g ∉ X w) : g ∈ pool X := by
  simp only [pool, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_biUnion, true_and]
  rintro ⟨w, hw⟩
  exact h w hw

theorem kappa_le {v : Fin n → Finset (Fin m) → ℝ} (hmono : IsMonotoneVal v)
    {X : Fin n → Finset (Fin m)} {i : Fin n} {S T : Finset (Fin m)} (hT : T ⊆ S)
    (hv : v i (X i) < v i T) : kappa v X i S ≤ T.card := by
  unfold kappa
  rw [if_pos (hv.trans_le (hmono i T S hT))]
  exact iInf₂_le T ⟨hT, hv⟩

theorem le_kappa {v : Fin n → Finset (Fin m) → ℝ} {X : Fin n → Finset (Fin m)} {i : Fin n}
    {S : Finset (Fin m)} {c : ℕ} (hP : ∀ T ⊆ S, v i (X i) < v i T → c ≤ T.card) :
    (c : ℕ∞) ≤ kappa v X i S := by
  unfold kappa
  split_ifs
  · exact le_iInf₂ fun T hT => by exact_mod_cast hP T hT.1 hT.2
  · exact le_top

theorem exists_minpref {v : Fin n → Finset (Fin m) → ℝ} {X : Fin n → Finset (Fin m)}
    {i : Fin n} {S : Finset (Fin m)} (h : v i (X i) < v i S) :
    ∃ P, IsMinPreferredSet v X i S P := by
  classical
  obtain ⟨P, hP, hmin⟩ := (S.powerset.filter (fun T => v i (X i) < v i T)).exists_min_image
    Finset.card ⟨S, by simp [h]⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hP
  exact ⟨P, hP.1, hP.2, fun T hT hv => hmin T (by simp [hT, hv])⟩

theorem kappa_minpref {v : Fin n → Finset (Fin m) → ℝ} (hmono : IsMonotoneVal v)
    {X : Fin n → Finset (Fin m)} {i : Fin n} {S P : Finset (Fin m)}
    (hP : IsMinPreferredSet v X i S P) : kappa v X i S = P.card :=
  le_antisymm (kappa_le hmono hP.1 hP.2.1) (le_kappa hP.2.2)

theorem no_envy_small {v : Fin n → Finset (Fin m) → ℝ} (hmono : IsMonotoneVal v)
    {X : Fin n → Finset (Fin m)} {c : Fin n} {S P : Finset (Fin m)}
    (hc : IsMostEnvious v X S c) (hP : IsMinPreferredSet v X c S P) (w : Fin n)
    (T : Finset (Fin m)) (hT : T ⊆ S) (hcard : T.card < P.card) : v w T ≤ v w (X w) := by
  by_contra hcon
  push_neg at hcon
  have h1 := kappa_le hmono hT hcon
  have h2 := hc.2 w
  rw [kappa_minpref hmono hP] at h2
  have h3 : (P.card : ℕ∞) ≤ T.card := h2.trans h1
  exact absurd (by exact_mod_cast h3 : P.card ≤ T.card) (not_le.mpr hcard)

theorem safe_of_champ {v : Fin n → Finset (Fin m) → ℝ} (hmono : IsMonotoneVal v)
    {X : Fin n → Finset (Fin m)} {c : Fin n} {S P : Finset (Fin m)}
    (hc : IsMostEnvious v X S c) (hP : IsMinPreferredSet v X c S P) (w : Fin n) :
    Safe v X P w := fun h hh =>
  no_envy_small hmono hc hP w (P.erase h) ((Finset.erase_subset _ _).trans hP.1)
    (Finset.card_erase_lt_of_mem hh)

theorem champ_transfer {v : Fin n → Finset (Fin m) → ℝ} (hmono : IsMonotoneVal v)
    {X : Fin n → Finset (Fin m)} {S : Finset (Fin m)} {i j : Fin n} (hv : v j = v i)
    (hle : v i (X j) ≤ v i (X i)) (hi : IsMostEnvious v X S i) : IsMostEnvious v X S j := by
  obtain ⟨P, hP⟩ := exists_minpref hi.1
  refine ⟨by rw [hv]; exact hle.trans_lt hi.1, fun w => ?_⟩
  have : kappa v X j S ≤ kappa v X i S := by
    rw [kappa_minpref hmono hP]
    exact kappa_le hmono hP.1 (by rw [hv]; exact hle.trans_lt hP.2.1)
  exact this.trans (hi.2 w)

theorem exists_champ {v : Fin n → Finset (Fin m) → ℝ} (hmono : IsMonotoneVal v)
    {X : Fin n → Finset (Fin m)} {S : Finset (Fin m)} (j : Fin n) (hj : v j (X j) < v j S) :
    ∃ i, IsMostEnvious v X S i := by
  haveI : Nonempty (Fin n) := ⟨j⟩
  obtain ⟨i, -, hi⟩ := Finset.univ.exists_min_image (fun i => kappa v X i S)
    Finset.univ_nonempty
  refine ⟨i, ?_, fun w => hi w (Finset.mem_univ _)⟩
  by_contra hc
  have h1 : kappa v X i S = ⊤ := by unfold kappa; rw [if_neg hc]
  obtain ⟨P, hP⟩ := exists_minpref hj
  have h2 := hi j (Finset.mem_univ _)
  rw [h1, kappa_minpref hmono hP] at h2
  simp at h2

/-- Lemma 5 core: for a min preferred set `P` of a g-champion `i` of `j`. -/
theorem decomp_core {v : Fin n → Finset (Fin m) → ℝ} (hnorm : IsNormalized v)
    (hmono : IsMonotoneVal v) (hnd : IsNonDegenerate v) {X : Fin n → Finset (Fin m)}
    {g : Fin m} (hg : g ∈ pool X) {i j : Fin n}
    (hc : IsMostEnvious v X (insert g (X j)) i) (hne : ¬ v i (X i) < v i (X j))
    (hi : ¬ IsMostEnvious v X (insert g (X i)) i)
    (hj : ¬ IsMostEnvious v X (insert g (X j)) j) {P : Finset (Fin m)}
    (hP : IsMinPreferredSet v X i (insert g (X j)) P) :
    {g} ⊂ P ∧ P ⊂ insert g (X j) := by
  have hgP : g ∈ P := by
    by_contra hgP
    have hsub : P ⊆ X j := by
      intro x hx
      rcases Finset.mem_insert.mp (hP.1 hx) with rfl | h
      · exact absurd hx hgP
      · exact h
    have := hmono i P (X j) hsub
    linarith [hP.2.1, not_lt.mp hne]
  have hPg : P ≠ {g} := by
    intro hPg
    apply hi
    refine ⟨v_strict hmono hnd (Finset.ssubset_insert (not_mem_pool hg i)), fun w => ?_⟩
    have h1 : kappa v X i (insert g (X i)) ≤ ({g} : Finset (Fin m)).card :=
      kappa_le hmono (by simp) (by rw [← hPg]; exact hP.2.1)
    have h2 : ((1 : ℕ) : ℕ∞) ≤ kappa v X w (insert g (X i)) := by
      apply le_kappa
      intro T _ hT
      rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
      rintro rfl
      have := v_nonneg hnorm hmono w (X w)
      rw [hnorm w] at hT
      linarith
    simp only [Finset.card_singleton] at h1
    exact h1.trans (by exact_mod_cast h2)
  have hPS : P ≠ insert g (X j) := by
    intro hPS
    apply hj
    refine ⟨v_strict hmono hnd (Finset.ssubset_insert (not_mem_pool hg j)), fun w => ?_⟩
    have h1 : kappa v X j (insert g (X j)) ≤ (insert g (X j)).card :=
      kappa_le hmono subset_rfl (v_strict hmono hnd (Finset.ssubset_insert (not_mem_pool hg j)))
    have h2 := hc.2 w
    rw [kappa_minpref hmono hP, hPS] at h2
    exact h1.trans h2
  exact ⟨Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr hgP, Ne.symm hPg⟩,
    Finset.ssubset_iff_subset_ne.mpr ⟨hP.1, hPS⟩⟩

/-! ## Improvement steps (PI cycles of length one and two) -/

theorem alloc_update {X : Fin n → Finset (Fin m)} (hX : IsPartialAllocation X) (c : Fin n)
    (S : Finset (Fin m)) (hS : ∀ w, w ≠ c → Disjoint S (X w)) :
    IsPartialAllocation (Function.update X c S) := by
  intro a b hab
  simp only [Function.update_apply]
  split_ifs with ha hb hb
  · exact absurd (ha.trans hb.symm) hab
  · exact hS b hb
  · exact (hS a ha).symm
  · exact hX hab

theorem disj_ins {X : Fin n → Finset (Fin m)} (hX : IsPartialAllocation X) {g : Fin m}
    (hg : g ∈ pool X) {p q : Fin n} (hpq : p ≠ q) : Disjoint (insert g (X p)) (X q) :=
  Finset.disjoint_insert_left.mpr ⟨not_mem_pool hg q, hX hpq⟩

theorem step_self {v : Fin n → Finset (Fin m) → ℝ} (hmono : IsMonotoneVal v)
    {X : Fin n → Finset (Fin m)} (hX : IsPartialAllocation X) {g : Fin m} (hg : g ∈ pool X)
    (c : Fin n) (hc : IsMostEnvious v X (insert g (X c)) c) :
    ∃ Y : Fin n → Finset (Fin m), IsPartialAllocation Y ∧ (∀ w, w ≠ c → Y w = X w) ∧
      v c (X c) < v c (Y c) ∧ (∀ w, v w (X w) ≤ v w (Y w)) ∧
      (∀ i j, Safe v X (X j) i → Safe v Y (Y j) i) := by
  classical
  obtain ⟨P, hP⟩ := exists_minpref hc.1
  have hpar : ∀ w, v w (X w) ≤ v w (Function.update X c P w) := by
    intro w
    by_cases hw : w = c
    · rw [hw, Function.update_self]; exact hP.2.1.le
    · rw [Function.update_of_ne hw]
  refine ⟨Function.update X c P, alloc_update hX c P fun w hw => ?_,
    fun w hw => Function.update_of_ne hw _ _, by rw [Function.update_self]; exact hP.2.1, hpar,
    fun i j hij => ?_⟩
  · exact (disj_ins hX hg (Ne.symm hw)).mono_left hP.1
  · by_cases hj : j = c
    · rw [hj, Function.update_self]
      exact safe_lift (safe_of_champ hmono hc hP i) (hpar i)
    · rw [Function.update_of_ne hj]
      exact safe_lift hij (hpar i)

theorem alloc_two {X : Fin n → Finset (Fin m)}
    (hX : IsPartialAllocation X) (a b : Fin n) (hab : a ≠ b) (Na Nb : Finset (Fin m))
    (hd : Disjoint Na Nb) (hNa : ∀ w, w ≠ a → w ≠ b → Disjoint Na (X w))
    (hNb : ∀ w, w ≠ a → w ≠ b → Disjoint Nb (X w)) :
    ∃ Y : Fin n → Finset (Fin m), IsPartialAllocation Y ∧ Y a = Na ∧ Y b = Nb ∧
      (∀ w, w ≠ a → w ≠ b → Y w = X w) := by
  classical
  refine ⟨fun w => if w = a then Na else if w = b then Nb else X w, ?_, by simp,
    by simp [Ne.symm hab], fun w h1 h2 => by simp [h1, h2]⟩
  intro p q hpq
  dsimp only
  by_cases hpa : p = a
  · have hqa : q ≠ a := fun h => hpq (hpa.trans h.symm)
    by_cases hqb : q = b
    · rw [if_pos hpa, if_neg hqa, if_pos hqb]; exact hd
    · rw [if_pos hpa, if_neg hqa, if_neg hqb]; exact hNa q hqa hqb
  · by_cases hpb : p = b
    · have hqb : q ≠ b := fun h => hpq (hpb.trans h.symm)
      by_cases hqa : q = a
      · rw [if_neg hpa, if_pos hpb, if_pos hqa]; exact hd.symm
      · rw [if_neg hpa, if_pos hpb, if_neg hqa, if_neg hqb]; exact hNb q hqa hqb
    · by_cases hqa : q = a
      · rw [if_neg hpa, if_neg hpb, if_pos hqa]; exact (hNa p hpa hpb).symm
      · by_cases hqb : q = b
        · rw [if_neg hpa, if_neg hpb, if_neg hqa, if_pos hqb]; exact (hNb p hpa hpb).symm
        · rw [if_neg hpa, if_neg hpb, if_neg hqa, if_neg hqb]; exact hX hpq

theorem step_two {v : Fin n → Finset (Fin m) → ℝ} {X : Fin n → Finset (Fin m)}
    (hX : IsPartialAllocation X) (a b : Fin n) (hab : a ≠ b) (Na Nb : Finset (Fin m))
    (hd : Disjoint Na Nb) (hNa : ∀ w, w ≠ a → w ≠ b → Disjoint Na (X w))
    (hNb : ∀ w, w ≠ a → w ≠ b → Disjoint Nb (X w))
    (hva : v a (X a) < v a Na) (hvb : v b (X b) < v b Nb) :
    ∃ Y : Fin n → Finset (Fin m), IsPartialAllocation Y ∧ Y a = Na ∧ Y b = Nb ∧
      (∀ w, w ≠ a → w ≠ b → Y w = X w) ∧ (∀ w, v w (X w) ≤ v w (Y w)) := by
  obtain ⟨Y, hY, hYa, hYb, hYo⟩ := alloc_two hX a b hab Na Nb hd hNa hNb
  refine ⟨Y, hY, hYa, hYb, hYo, fun w => ?_⟩
  by_cases hwa : w = a
  · rw [hwa, hYa]; exact hva.le
  · by_cases hwb : w = b
    · rw [hwb, hYb]; exact hvb.le
    · rw [hYo w hwa hwb]

/-- Two-cycle `a → b` (envy edge) and `b →g a` (champion edge). -/
theorem step_envy {v : Fin n → Finset (Fin m) → ℝ} (hmono : IsMonotoneVal v)
    {X : Fin n → Finset (Fin m)} (hX : IsPartialAllocation X) {g : Fin m} (hg : g ∈ pool X)
    (a b : Fin n) (hab : a ≠ b) (henvy : v a (X a) < v a (X b))
    (hb : IsMostEnvious v X (insert g (X a)) b) :
    ∃ Y : Fin n → Finset (Fin m), IsPartialAllocation Y ∧ (∀ w, w ≠ a → w ≠ b → Y w = X w) ∧
      v a (X a) < v a (Y a) ∧ (∀ w, v w (X w) ≤ v w (Y w)) ∧
      (∀ i, Safe v X (X b) i → Safe v Y (Y a) i) ∧
      (∀ i j, j ≠ a → Safe v X (X j) i → Safe v Y (Y j) i) := by
  obtain ⟨P, hP⟩ := exists_minpref hb.1
  obtain ⟨Y, hY, hYa, hYb, hYo, hpar⟩ := step_two hX a b hab (X b) P
    (((disj_ins hX hg hab).symm).mono_right hP.1)
    (fun w _ hwb => hX (Ne.symm hwb))
    (fun w hwa _ => (disj_ins hX hg (Ne.symm hwa)).mono_left hP.1) henvy hP.2.1
  refine ⟨Y, hY, hYo, by rw [hYa]; exact henvy, hpar, fun i hi => ?_, fun i j hja hij => ?_⟩
  · rw [hYa]; exact safe_lift hi (hpar i)
  · by_cases hjb : j = b
    · rw [hjb, hYb]; exact safe_lift (safe_of_champ hmono hb hP i) (hpar i)
    · rw [hYo j hja hjb]; exact safe_lift hij (hpar i)

/-- Two-cycle `a →g1 b` and `b →g2 a` (two champion edges). -/
theorem step_cc {v : Fin n → Finset (Fin m) → ℝ} (hmono : IsMonotoneVal v)
    {X : Fin n → Finset (Fin m)} (hX : IsPartialAllocation X) {g1 g2 : Fin m}
    (hg1 : g1 ∈ pool X) (hg2 : g2 ∈ pool X) (h12 : g1 ≠ g2)
    (a b : Fin n) (hab : a ≠ b) (ha : IsMostEnvious v X (insert g1 (X b)) a)
    (hb : IsMostEnvious v X (insert g2 (X a)) b) :
    ∃ Y : Fin n → Finset (Fin m), IsPartialAllocation Y ∧ (∀ w, w ≠ a → w ≠ b → Y w = X w) ∧
      v a (X a) < v a (Y a) ∧ (∀ w, v w (X w) ≤ v w (Y w)) ∧
      (∀ i j, Safe v X (X j) i → Safe v Y (Y j) i) := by
  obtain ⟨P1, hP1⟩ := exists_minpref ha.1
  obtain ⟨P2, hP2⟩ := exists_minpref hb.1
  have hd : Disjoint (insert g1 (X b)) (insert g2 (X a)) := by
    rw [Finset.disjoint_insert_left]
    refine ⟨?_, (disj_ins hX hg2 hab).symm⟩
    rw [Finset.mem_insert, not_or]
    exact ⟨h12, not_mem_pool hg1 a⟩
  obtain ⟨Y, hY, hYa, hYb, hYo, hpar⟩ := step_two hX a b hab P1 P2
    ((hd.mono_left hP1.1).mono_right hP2.1)
    (fun w _ hwb => (disj_ins hX hg1 (Ne.symm hwb)).mono_left hP1.1)
    (fun w hwa _ => (disj_ins hX hg2 (Ne.symm hwa)).mono_left hP2.1) hP1.2.1 hP2.2.1
  refine ⟨Y, hY, hYo, by rw [hYa]; exact hP1.2.1, hpar, fun i j hij => ?_⟩
  by_cases hja : j = a
  · rw [hja, hYa]; exact safe_lift (safe_of_champ hmono ha hP1 i) (hpar i)
  · by_cases hjb : j = b
    · rw [hjb, hYb]; exact safe_lift (safe_of_champ hmono hb hP2 i) (hpar i)
    · rw [hYo j hja hjb]; exact safe_lift hij (hpar i)

/-! ## Lemma 15 (non-strict minimum version): semi-EFX to EFX keeping `N_a` -/

theorem semi_to_efx {v : Fin n → Finset (Fin m) → ℝ} (hmono : IsMonotoneVal v)
    (va vb : Finset (Fin m) → ℝ) (A : Finset (Fin n))
    (hB : ∀ i ∉ A, v i = vb) :
    ∀ (N : ℕ) (X : Fin n → Finset (Fin m)), ∑ w, (X w).card = N → IsPartialAllocation X →
      IsSemiEFX v A X → ∀ b0, b0 ∉ A → (∀ b ∉ A, vb (X b0) ≤ vb (X b)) →
      ∃ Y : Fin n → Finset (Fin m), IsPartialAllocation Y ∧ IsEFX v Y ∧ ∀ i ∈ A, Y i = X i := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro X hN hX hS b0 hb0 hmin
  by_cases hE : IsEFX v X
  · exact ⟨X, hX, hE, fun _ _ => rfl⟩
  have hE' : ∃ i j, ∃ h ∈ X j, v i (X i) < v i ((X j).erase h) := by
    by_contra hc
    apply hE
    intro i j h hh
    exact not_lt.mp fun hlt => hc ⟨i, j, h, hh, hlt⟩
  obtain ⟨i, j, h, hh, hlt⟩ := hE'
  rw [semi_iff] at hS
  have hiA : i ∉ A := fun hi => absurd (hS i j (Or.inl hi) h hh) (not_le.mpr hlt)
  have hjA : j ∉ A := fun hj => absurd (hS i j (Or.inr hj) h hh) (not_le.mpr hlt)
  have hvij : v j = v i := by rw [hB i hiA, hB j hjA]
  rw [hB i hiA] at hlt
  have hjb : j ≠ b0 := by
    rintro rfl
    have h1 := hmin i hiA
    have h2 := hmono j ((X j).erase h) (X j) (Finset.erase_subset _ _)
    rw [hB j hjA] at h2
    linarith
  set X' := Function.update X j ((X j).erase h) with hX'
  have hX'j : X' j = (X j).erase h := Function.update_self _ _ _
  have hX'o : ∀ w, w ≠ j → X' w = X w := fun w hw => Function.update_of_ne hw _ _
  have hlt' : ∑ w, (X' w).card < N := by
    rw [← hN]
    apply Finset.sum_lt_sum
    · intro w _
      by_cases hw : w = j
      · rw [hw, hX'j]; exact Finset.card_erase_le
      · rw [hX'o w hw]
    · exact ⟨j, Finset.mem_univ _, by rw [hX'j]; exact Finset.card_erase_lt_of_mem hh⟩
  have hXa : IsPartialAllocation X' :=
    alloc_update hX j _ fun w hw => (hX (Ne.symm hw)).mono_left (Finset.erase_subset _ _)
  have hSa : IsSemiEFX v A X' := by
    rw [semi_iff]
    intro p q hpq
    unfold Safe
    by_cases hq : q = j
    · have hpA : p ∈ A := hpq.resolve_right (by rw [hq]; exact hjA)
      have hpj : p ≠ j := fun h' => hjA (h' ▸ hpA)
      rw [hq, hX'j, hX'o p hpj]
      intro h' hh'
      have hh'' : h' ∈ X j := Finset.mem_of_mem_erase hh'
      refine (hmono p _ _ ?_).trans (hS p j (Or.inl hpA) h' hh'')
      rw [Finset.erase_right_comm]
      exact Finset.erase_subset _ _
    · rw [hX'o q hq]
      by_cases hp : p = j
      · have hqA : q ∈ A := hpq.resolve_left (by rw [hp]; exact hjA)
        rw [hp, hX'j]
        intro h' hh'
        have := hS i q (Or.inr hqA) h' hh'
        rw [hvij]
        rw [hB i hiA] at this ⊢
        linarith
      · rw [hX'o p hp]
        exact hS p q hpq
  have hmin' : ∀ b ∉ A, vb (X' b0) ≤ vb (X' b) := by
    intro b hb
    rw [hX'o b0 (Ne.symm hjb)]
    by_cases hbj : b = j
    · rw [hbj, hX'j]
      linarith [hmin i hiA]
    · rw [hX'o b hbj]; exact hmin b hb
  obtain ⟨Y, hY, hYE, hYA⟩ := ih _ hlt' X' rfl hXa hSa b0 hb0 hmin'
  refine ⟨Y, hY, hYE, fun a ha => ?_⟩
  rw [hYA a ha, hX'o a (fun h' => hjA (h' ▸ ha))]

/-! ## Assembling pieces of the proof of Theorem 14 -/

theorem finish {v : Fin n → Finset (Fin m) → ℝ} (hmono : IsMonotoneVal v)
    (va vb : Finset (Fin m) → ℝ) (A : Finset (Fin n)) (hB : ∀ i ∉ A, v i = vb)
    (hBne : Aᶜ.Nonempty) (X : Fin n → Finset (Fin m)) (a0 : Fin n) (ha0 : a0 ∈ A)
    (Y : Fin n → Finset (Fin m)) (hY : IsPartialAllocation Y) (hYs : IsSemiEFX v A Y)
    (hval : ∀ i ∈ A, va (X a0) < va (Y i)) :
    ∃ Z : Fin n → Finset (Fin m), IsPartialAllocation Z ∧ IsEFX v Z ∧ PLexGT va vb A Z X := by
  obtain ⟨b, hb, hbmin⟩ := Aᶜ.exists_min_image (fun i => vb (Y i)) hBne
  obtain ⟨Z, hZ, hZE, hZA⟩ := semi_to_efx hmono va vb A hB _ Y rfl hY hYs b
    (Finset.mem_compl.mp hb) (fun b' hb' => hbmin b' (Finset.mem_compl.mpr hb'))
  exact ⟨Z, hZ, hZE, plex_of_head va vb A X Z a0 ha0
    (fun i hi => by rw [hZA i hi]; exact hval i hi)⟩

theorem semi_parts {v : Fin n → Finset (Fin m) → ℝ}
    (va vb : Finset (Fin m) → ℝ) (A : Finset (Fin n)) (hA : ∀ i ∈ A, v i = va)
    (hB : ∀ i ∉ A, v i = vb) (X X' : Fin n → Finset (Fin m)) (hEFX : IsEFX v X)
    (a0 : Fin n) (ha0 : a0 ∈ A) (ha0min : ∀ i ∈ A, va (X a0) ≤ va (X i))
    (P : Finset (Fin m)) (hPa : va (X a0) < va P) (hsafeP : ∀ w, Safe v X P w)
    (b0 : Fin n) (H1 : ∀ w ∈ A, X' w = X w ∨ X' w = P)
    (H2 : ∀ w, w ∉ A → w ≠ b0 → X' w = X w)
    (H3 : ∀ h ∈ X' b0, va ((X' b0).erase h) ≤ va (X a0))
    (H4 : ∀ w ∈ A, ∀ h ∈ X' w, vb ((X' w).erase h) ≤ vb (X' b0)) : IsSemiEFX v A X' := by
  have T1 : ∀ j, ∀ h ∈ X' j, va ((X' j).erase h) ≤ va (X a0) := by
    intro j h hh
    by_cases hjb : j = b0
    · rw [hjb] at hh ⊢; exact H3 h hh
    · by_cases hjA : j ∈ A
      · rcases H1 j hjA with hj | hj <;> rw [hj] at hh ⊢
        · have := hEFX a0 j h hh; rwa [hA a0 ha0] at this
        · have := hsafeP a0 h hh; rwa [hA a0 ha0] at this
      · rw [H2 j hjA hjb] at hh ⊢
        have := hEFX a0 j h hh; rwa [hA a0 ha0] at this
  rw [semi_iff]
  intro i j hij h hh
  by_cases hiA : i ∈ A
  · rw [hA i hiA]
    refine (T1 j h hh).trans ?_
    rcases H1 i hiA with hi | hi <;> rw [hi]
    · exact ha0min i hiA
    · exact hPa.le
  · have hjA : j ∈ A := hij.resolve_left hiA
    rw [hB i hiA]
    by_cases hib : i = b0
    · rw [hib]; exact H4 j hjA h hh
    · rw [H2 i hiA hib]
      rcases H1 j hjA with hj | hj <;> rw [hj] at hh ⊢
      · have := hEFX i j h hh; rwa [hB i hiA] at this
      · have := hsafeP i h hh; rwa [hB i hiA] at this

theorem xprime_cycle {v : Fin n → Finset (Fin m) → ℝ} (hmono : IsMonotoneVal v)
    (hnd : IsNonDegenerate v) (va vb : Finset (Fin m) → ℝ) (A : Finset (Fin n))
    (hA : ∀ i ∈ A, v i = va) (hB : ∀ i ∉ A, v i = vb)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hS : IsSemiEFX v A X)
    {g : Fin m} (hg : g ∈ pool X) (a0 b0 : Fin n) (ha0 : a0 ∈ A) (hb0 : b0 ∉ A)
    (ha0min : ∀ i ∈ A, va (X a0) ≤ va (X i)) (hb0min : ∀ i ∉ A, vb (X b0) ≤ vb (X i))
    (hedge : v a0 (X a0) < v a0 (X b0) ∨
      ∃ g2 ∈ pool X, g2 ≠ g ∧ IsMostEnvious v X (insert g2 (X b0)) a0) :
    ∃ Y : Fin n → Finset (Fin m), IsPartialAllocation Y ∧ IsSemiEFX v A Y ∧
      (∀ w, v w (X w) ≤ v w (Y w)) ∧ v a0 (X a0) < v a0 (Y a0) := by
  have hab : a0 ≠ b0 := fun h => hb0 (h ▸ ha0)
  rw [semi_iff] at hS
  obtain ⟨l, hl⟩ := exists_champ hmono a0
    (v_strict hmono hnd (Finset.ssubset_insert (not_mem_pool hg a0)))
  by_cases hlA : l ∈ A
  · have hc : IsMostEnvious v X (insert g (X a0)) a0 := champ_transfer hmono
      (by rw [hA a0 ha0, hA l hlA]) (by rw [hA l hlA]; exact ha0min l hlA) hl
    obtain ⟨Y, hY, -, hlt, hpar, hsafe⟩ := step_self hmono hX hg a0 hc
    exact ⟨Y, hY, (semi_iff v A Y).mpr fun i j hij => hsafe i j (hS i j hij), hpar, hlt⟩
  · have hc : IsMostEnvious v X (insert g (X a0)) b0 := champ_transfer hmono
      (by rw [hB b0 hb0, hB l hlA]) (by rw [hB l hlA]; exact hb0min l hlA) hl
    rcases hedge with he | ⟨g2, hg2, hne, hc2⟩
    · obtain ⟨Y, hY, -, hlt, hpar, hsa, hso⟩ := step_envy hmono hX hg a0 b0 hab he hc
      refine ⟨Y, hY, (semi_iff v A Y).mpr fun i j hij => ?_, hpar, hlt⟩
      by_cases hja : j = a0
      · rw [hja]
        apply hsa
        by_cases hiA : i ∈ A
        · exact hS i b0 (Or.inl hiA)
        · intro h _
          exact (hmono i _ _ (Finset.erase_subset _ _)).trans
            (by rw [hB i hiA]; exact hb0min i hiA)
      · exact hso i j hja (hS i j hij)
    · obtain ⟨Y, hY, -, hlt, hpar, hsafe⟩ := step_cc hmono hX hg2 hg hne a0 b0 hab hc2 hc
      exact ⟨Y, hY, (semi_iff v A Y).mpr fun i j hij => hsafe i j (hS i j hij), hpar, hlt⟩

set_option maxHeartbeats 1000000 in
theorem main (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotoneVal v) (hnd : IsNonDegenerate v)
    (va vb : Finset (Fin m) → ℝ) (A : Finset (Fin n))
    (hA : ∀ i ∈ A, v i = va) (hB : ∀ i ∉ A, v i = vb)
    (hAne : A.Nonempty) (hBne : Aᶜ.Nonempty)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X)
    (hpool : (pool X).Nonempty) (hEFX : IsEFX v X) :
    ∃ Y : Fin n → Finset (Fin m), IsPartialAllocation Y ∧ IsEFX v Y ∧
      PLexGT va vb A Y X := by
  classical
  obtain ⟨g, hg⟩ := hpool
  have done : ∀ Y : Fin n → Finset (Fin m), IsPartialAllocation Y →
      (∀ i j, Safe v Y (Y j) i) → (∀ w, v w (X w) ≤ v w (Y w)) →
      (∃ w, v w (X w) < v w (Y w)) →
      ∃ Y : Fin n → Finset (Fin m), IsPartialAllocation Y ∧ IsEFX v Y ∧ PLexGT va vb A Y X :=
    fun Y hY hE hle hlt => ⟨Y, hY, hE, plex_of_pareto v va vb A hA hB X Y hle hlt⟩
  -- Step 0: an empty bundle receives `g`.
  by_cases hE0 : ∃ i, X i = ∅
  · obtain ⟨i, hi⟩ := hE0
    have hpar : ∀ w, v w (X w) ≤ v w (Function.update X i {g} w) := by
      intro w
      by_cases hw : w = i
      · rw [hw, Function.update_self, hi]; exact hmono i _ _ (Finset.empty_subset _)
      · rw [Function.update_of_ne hw]
    refine done _ (alloc_update hX i {g} fun w _ =>
      Finset.disjoint_singleton_left.mpr (not_mem_pool hg w)) (fun p q => ?_) hpar ⟨i, ?_⟩
    · intro h hh
      by_cases hq : q = i
      · rw [hq, Function.update_self] at hh ⊢
        rw [Finset.mem_singleton.mp hh, Finset.erase_singleton, hnorm p]
        exact v_nonneg hnorm hmono p _
      · rw [Function.update_of_ne hq] at hh ⊢
        exact (hEFX p q h hh).trans (hpar p)
    · rw [Function.update_self, hi]
      exact v_strict hmono hnd (Finset.empty_ssubset.mpr (Finset.singleton_nonempty g))
  push_neg at hE0
  have hne : ∀ i, (X i).Nonempty := hE0
  have hdist : ∀ i j, i ≠ j → X i ≠ X j := by
    intro i j hij heq
    have : Disjoint (X i) (X j) := hX hij
    rw [heq] at this
    exact (hne j).ne_empty (Finset.disjoint_self_iff_empty _ |>.mp this)
  obtain ⟨a0, ha0, ha0min⟩ := A.exists_min_image (fun i => va (X i)) hAne
  obtain ⟨b0, hb0', hb0min'⟩ := Aᶜ.exists_min_image (fun i => vb (X i)) hBne
  have hb0 : b0 ∉ A := Finset.mem_compl.mp hb0'
  have hb0min : ∀ i ∉ A, vb (X b0) ≤ vb (X i) := fun i hi =>
    hb0min' i (Finset.mem_compl.mpr hi)
  have hab : a0 ≠ b0 := fun h => hb0 (h ▸ ha0)
  have hvA0 : v a0 = va := hA a0 ha0
  have hvB0 : v b0 = vb := hB b0 hb0
  have hma : ∀ S T, S ⊆ T → va S ≤ va T := fun S T h => by
    rw [← hvA0]; exact hmono a0 S T h
  have hmb : ∀ S T, S ⊆ T → vb S ≤ vb T := fun S T h => by
    rw [← hvB0]; exact hmono b0 S T h
  have ha0strict : ∀ i ∈ A, i ≠ a0 → va (X a0) < va (X i) := fun i hi hia =>
    lt_of_le_of_ne (ha0min i hi) (by rw [← hvA0]; exact hnd a0 _ _ (hdist a0 i (Ne.symm hia)))
  -- Step 1: PI cycles in `M_X` through `a0` or `b0`.
  by_cases h1 : IsMostEnvious v X (insert g (X a0)) a0
  · obtain ⟨Y, hY, -, hlt, hpar, hsafe⟩ := step_self hmono hX hg a0 h1
    exact done Y hY (fun i j => hsafe i j (hEFX i j)) hpar ⟨a0, hlt⟩
  by_cases h2 : IsMostEnvious v X (insert g (X b0)) b0
  · obtain ⟨Y, hY, -, hlt, hpar, hsafe⟩ := step_self hmono hX hg b0 h2
    exact done Y hY (fun i j => hsafe i j (hEFX i j)) hpar ⟨b0, hlt⟩
  by_cases h3 : v a0 (X a0) < v a0 (X b0)
  · obtain ⟨l, hl⟩ := exists_champ hmono a0
      (v_strict hmono hnd (Finset.ssubset_insert (not_mem_pool hg a0)))
    by_cases hlA : l ∈ A
    · exact absurd (champ_transfer hmono (by rw [hvA0, hA l hlA])
        (by rw [hA l hlA]; exact ha0min l hlA) hl) h1
    · have hc : IsMostEnvious v X (insert g (X a0)) b0 := champ_transfer hmono
        (by rw [hvB0, hB l hlA]) (by rw [hB l hlA]; exact hb0min l hlA) hl
      obtain ⟨Y, hY, -, hlt, hpar, hsa, hso⟩ := step_envy hmono hX hg a0 b0 hab h3 hc
      refine done Y hY (fun i j => ?_) hpar ⟨a0, hlt⟩
      by_cases hja : j = a0
      · rw [hja]; exact hsa i (hEFX i b0)
      · exact hso i j hja (hEFX i j)
  -- Step 2: `a0` g-decomposes `b0` (Lemma 5).
  obtain ⟨c, hc⟩ := exists_champ hmono (S := insert g (X b0)) b0
    (v_strict hmono hnd (Finset.ssubset_insert (not_mem_pool hg b0)))
  have hcA : c ∈ A := by
    by_contra hcA
    exact h2 (champ_transfer hmono (by rw [hvB0, hB c hcA])
      (by rw [hB c hcA]; exact hb0min c hcA) hc)
  have hch : IsMostEnvious v X (insert g (X b0)) a0 := champ_transfer hmono
    (by rw [hvA0, hA c hcA]) (by rw [hA c hcA]; exact ha0min c hcA) hc
  obtain ⟨P, hP⟩ := exists_minpref hch.1
  obtain ⟨hgP, hPS⟩ := decomp_core hnorm hmono hnd hg hch h3 h1 h2 hP
  have hsafeP : ∀ w, Safe v X P w := safe_of_champ hmono hch hP
  have hPa : va (X a0) < va P := by rw [← hvA0]; exact hP.2.1
  have hPsub : P ⊆ insert g (X b0) := hP.1
  have hgP' : g ∈ P := Finset.singleton_subset_iff.mp hgP.subset
  obtain ⟨g', hg'S, hg'P⟩ := Finset.exists_of_ssubset hPS
  have hg'b0 : g' ∈ X b0 := by
    rcases Finset.mem_insert.mp hg'S with h | h
    · exact absurd (by rw [h]; exact hgP') hg'P
    · exact h
  -- the sets `U_i`
  have hU : ∀ i, ∃ U : Finset (Fin m), U ⊆ X i ∧ (∀ h ∈ X i, vb ((X i).erase h) ≤ vb U) ∧
      (vb (X b0) < vb (X i) → (∃ h ∈ X i, U = (X i).erase h) ∧ ∀ S ⊂ X i, vb S ≤ vb U) ∧
      (¬ vb (X b0) < vb (X i) → U = X i) := by
    intro i
    by_cases hi : vb (X b0) < vb (X i)
    · obtain ⟨h, hh, hmax⟩ := (X i).exists_max_image (fun h => vb ((X i).erase h)) (hne i)
      have hprop : ∀ S ⊂ X i, vb S ≤ vb ((X i).erase h) := by
        intro S hS
        obtain ⟨t, ht, htS⟩ := Finset.exists_of_ssubset hS
        exact (hmb S _ fun x hx => Finset.mem_erase.mpr
          ⟨fun hxt => htS (by rw [← hxt]; exact hx), hS.subset hx⟩).trans (hmax t ht)
      exact ⟨(X i).erase h, Finset.erase_subset _ _,
        fun h' hh' => hprop _ (Finset.erase_ssubset hh'), fun _ => ⟨⟨h, hh, rfl⟩, hprop⟩,
        fun hc => absurd hi hc⟩
    · exact ⟨X i, subset_rfl, fun h' _ => hmb _ _ (Finset.erase_subset _ _),
        fun hc => absurd hc hi, fun _ => rfl⟩
  choose U hUsub hUer hUenv hUnot using hU
  by_cases hZP : ∀ i ∈ A, vb (U i) ≤ vb P
  · -- Case 2: `Z = T ∪ g = P` goes to `b0`.
    set X' := Function.update X b0 P with hX'def
    have hX'b0 : X' b0 = P := Function.update_self _ _ _
    have hX'o : ∀ w, w ≠ b0 → X' w = X w := fun w hw => Function.update_of_ne hw _ _
    have hX'al : IsPartialAllocation X' :=
      alloc_update hX b0 P fun w hw => (disj_ins hX hg (Ne.symm hw)).mono_left hPsub
    have hb0P : ∀ b ∉ A, vb P ≤ vb (X' b) := by
      intro b hb
      by_cases hbb : b = b0
      · rw [hbb, hX'b0]
      · rw [hX'o b hbb]
        by_contra hlt
        push_neg at hlt
        apply h2
        refine ⟨v_strict hmono hnd (Finset.ssubset_insert (not_mem_pool hg b0)), fun w => ?_⟩
        have := hch.2 w
        rw [kappa_minpref hmono hP] at this
        refine (kappa_le hmono hPsub ?_).trans this
        rw [hvB0]
        exact (hb0min b hb).trans_lt hlt
    have hsemi : IsSemiEFX v A X' := semi_parts va vb A hA hB X X' hEFX a0 ha0 ha0min P hPa
      hsafeP b0 (fun w hw => Or.inl (hX'o w fun h => hb0 (h ▸ hw)))
      (fun w _ hw => hX'o w hw)
      (by
        rw [hX'b0]
        intro h hh
        have := hsafeP a0 h hh
        rwa [hvA0] at this)
      (fun w hw h hh => by
        rw [hX'o w (fun h' => hb0 (h' ▸ hw))] at hh ⊢
        rw [hX'b0]
        exact (hUer w h hh).trans (hZP w hw))
    have hg'X' : g' ∈ pool X' := mem_pool fun w => by
      by_cases hw : w = b0
      · rw [hw, hX'b0]; exact hg'P
      · rw [hX'o w hw]; exact Finset.disjoint_left.mp (hX (Ne.symm hw)) hg'b0
    obtain ⟨Y, hY, hYs, hpar, hlt⟩ := xprime_cycle hmono hnd va vb A hA hB X' hX'al hsemi
      hg'X' a0 b0 ha0 hb0
      (fun i hi => by
        rw [hX'o a0 hab, hX'o i (fun h => hb0 (h ▸ hi))]
        exact ha0min i hi)
      (fun i hi => by rw [hX'b0]; exact hb0P i hi)
      (Or.inl (by rw [hX'o a0 hab, hX'b0, hvA0]; exact hPa))
    refine finish hmono va vb A hB hBne X a0 ha0 Y hY hYs fun i hi => ?_
    have hpi := hpar i
    rw [hA i hi] at hpi
    by_cases hia : i = a0
    · rw [hia]
      have := hlt
      rw [hX'o a0 hab, hvA0] at this
      exact this
    · rw [hX'o i (fun h => hb0 (h ▸ hi))] at hpi
      exact (ha0strict i hi hia).trans_le hpi
  · -- Cases 1 and 3: `Z = U_r`.
    push_neg at hZP
    obtain ⟨i1, hi1, hi1P⟩ := hZP
    obtain ⟨r, hrA, hrmax⟩ := A.exists_max_image (fun i => vb (U i)) hAne
    have hPr : vb P < vb (U r) := hi1P.trans_le (hrmax i1 hi1)
    have hrb : r ≠ b0 := fun h => hb0 (h ▸ hrA)
    have hUrb0 : vb (U r) ≤ vb (X b0) := by
      by_cases hbr : vb (X b0) < vb (X r)
      · obtain ⟨⟨h, hh, hUe⟩, -⟩ := hUenv r hbr
        rw [hUe]
        have := hEFX b0 r h hh
        rwa [hvB0] at this
      · rw [hUnot r hbr]; exact not_lt.mp hbr
    obtain ⟨X', hX'al, hX'b0, hX'r, hX'o⟩ := alloc_two hX b0 r (Ne.symm hrb) (U r) P
      ((((disj_ins hX hg (Ne.symm hrb)).symm).mono_left (hUsub r)).mono_right hPsub)
      (fun w _ hwr => (hX (Ne.symm hwr)).mono_left (hUsub r))
      (fun w hw0 _ => (disj_ins hX hg (Ne.symm hw0)).mono_left hPsub)
    have hX'oA : ∀ w ∈ A, w ≠ r → X' w = X w := fun w hw hwr =>
      hX'o w (fun h => hb0 (h ▸ hw)) hwr
    have hsemi : IsSemiEFX v A X' := semi_parts va vb A hA hB X X' hEFX a0 ha0 ha0min P hPa
      hsafeP b0
      (fun w hw => by
        by_cases hwr : w = r
        · exact Or.inr (by rw [hwr, hX'r])
        · exact Or.inl (hX'oA w hw hwr))
      (fun w hw hw0 => hX'o w hw0 (fun h => hw (h ▸ hrA)))
      (by
        rw [hX'b0]
        intro h hh
        have := hEFX a0 r h (hUsub r hh)
        rw [hvA0] at this
        exact (hma _ _ (Finset.erase_subset_erase h (hUsub r))).trans this)
      (fun w hw h hh => by
        rw [hX'b0]
        by_cases hwr : w = r
        · rw [hwr, hX'r] at hh ⊢
          exact (hmb _ _ (Finset.erase_subset _ _)).trans hPr.le
        · rw [hX'oA w hw hwr] at hh ⊢
          exact (hUer w h hh).trans (hrmax w hw))
    have hb0X' : ∀ b ∉ A, vb (X' b0) ≤ vb (X' b) := by
      intro b hb
      by_cases hbb : b = b0
      · rw [hbb]
      · rw [hX'b0, hX'o b hbb (fun h => hb (h ▸ hrA))]
        exact hUrb0.trans (hb0min b hb)
    by_cases hr0 : r = a0
    · -- Case 1: `Z = U_{a0}`; `a0` receives `P`.
      refine finish hmono va vb A hB hBne X a0 ha0 X' hX'al hsemi fun i hi => ?_
      by_cases hir : i = r
      · rw [hir, hX'r]; exact hPa
      · rw [hX'oA i hi hir]; exact ha0strict i hi (fun h => hir (h.trans hr0.symm))
    · -- Case 3: `Z = U_r`, `r ≠ a0`.
      have hX'a0 : X' a0 = X a0 := hX'oA a0 ha0 (fun h => hr0 h.symm)
      have hg'X' : g' ∈ pool X' := mem_pool fun w => by
        by_cases hw0 : w = b0
        · rw [hw0, hX'b0]
          exact fun h => Finset.disjoint_left.mp (hX hrb) (hUsub r h) hg'b0
        · by_cases hwr : w = r
          · rw [hwr, hX'r]; exact hg'P
          · rw [hX'o w hw0 hwr]; exact Finset.disjoint_left.mp (hX (Ne.symm hw0)) hg'b0
      have hedge : v a0 (X' a0) < v a0 (X' b0) ∨
          ∃ g2 ∈ pool X', g2 ≠ g' ∧ IsMostEnvious v X' (insert g2 (X' b0)) a0 := by
        by_cases hbr : vb (X b0) < vb (X r)
        · right
          obtain ⟨⟨h, hh, hUe⟩, hUmax⟩ := hUenv r hbr
          refine ⟨h, mem_pool fun w => ?_, ?_, ?_⟩
          · by_cases hw0 : w = b0
            · rw [hw0, hX'b0, hUe]; exact Finset.notMem_erase h _
            · by_cases hwr : w = r
              · rw [hwr, hX'r]
                intro hP'
                rcases Finset.mem_insert.mp (hPsub hP') with h' | h'
                · exact not_mem_pool hg r (h' ▸ hh)
                · exact Finset.disjoint_left.mp (hX hrb) hh h'
              · rw [hX'o w hw0 hwr]; exact Finset.disjoint_left.mp (hX (Ne.symm hwr)) hh
          · intro h'
            exact Finset.disjoint_left.mp (hX hrb) hh (by rw [h']; exact hg'b0)
          · rw [hX'b0, hUe, Finset.insert_erase hh]
            have hnp : ∀ w, ∀ T ⊂ X r, v w T ≤ v w (X' w) := by
              intro w T hT
              obtain ⟨t, ht, htT⟩ := Finset.exists_of_ssubset hT
              have hTs : T ⊆ (X r).erase t := fun x hx =>
                Finset.mem_erase.mpr ⟨fun hxt => htT (by rw [← hxt]; exact hx), hT.subset hx⟩
              by_cases hw0 : w = b0
              · rw [hw0, hX'b0, hvB0, hUe]
                rw [hUe] at hUmax
                exact hUmax T hT
              · by_cases hwr : w = r
                · rw [hwr, hX'r, hA r hrA]
                  have := hEFX a0 r t ht
                  rw [hvA0] at this
                  exact (hma _ _ hTs).trans (this.trans hPa.le)
                · rw [hX'o w hw0 hwr]
                  exact (hmono w _ _ hTs).trans (hEFX w r t ht)
            have henv : v a0 (X' a0) < v a0 (X r) := by
              rw [hX'a0, hvA0]; exact ha0strict r hrA hr0
            refine ⟨henv, fun w => ?_⟩
            refine (kappa_le hmono subset_rfl henv).trans (le_kappa fun T hT hv => ?_)
            by_contra hlt
            push_neg at hlt
            have hTne : T ≠ X r := fun h' => by rw [h'] at hlt; exact lt_irrefl _ hlt
            exact absurd (hnp w T (Finset.ssubset_iff_subset_ne.mpr ⟨hT, hTne⟩)) (not_le.mpr hv)
        · left
          rw [hX'a0, hX'b0, hUnot r hbr, hvA0]
          exact ha0strict r hrA hr0
      obtain ⟨Y, hY, hYs, hpar, hlt⟩ := xprime_cycle hmono hnd va vb A hA hB X' hX'al hsemi
        hg'X' a0 b0 ha0 hb0
        (fun i hi => by
          rw [hX'a0]
          by_cases hir : i = r
          · rw [hir, hX'r]; exact hPa.le
          · rw [hX'oA i hi hir]; exact ha0min i hi)
        hb0X' hedge
      refine finish hmono va vb A hB hBne X a0 ha0 Y hY hYs fun i hi => ?_
      have hpi := hpar i
      rw [hA i hi] at hpi
      by_cases hia : i = a0
      · rw [hia]
        have := hlt
        rw [hX'a0, hvA0] at this
        exact this
      · refine lt_of_lt_of_le ?_ hpi
        by_cases hir : i = r
        · rw [hir, hX'r]; exact hPa
        · rw [hX'oA i hi hir]; exact ha0strict i hi hia

end PV0F

open LittleCharity.EFX EFXGenVal.TwoVal in
theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotoneVal v) (hnd : IsNonDegenerate v)
    (va vb : Finset (Fin m) → ℝ) (A : Finset (Fin n))
    (hA : ∀ i ∈ A, v i = va) (hB : ∀ i ∉ A, v i = vb)
    (hAne : A.Nonempty) (hBne : Aᶜ.Nonempty)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X)
    (hpool : (pool X).Nonempty) (hEFX : IsEFX v X) :
    ∃ Y : Fin n → Finset (Fin m), IsPartialAllocation Y ∧ IsEFX v Y ∧
      PLexGT va vb A Y X := by
  exact PV0F.main v hnorm hmono hnd va vb A hA hB hAne hBne X hX hpool hEFX
