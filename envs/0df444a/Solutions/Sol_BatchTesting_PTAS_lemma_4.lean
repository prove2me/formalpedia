-- Prove2me | solution 1 for BatchTesting.PTAS.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T18:45:11.67074+00:00
-- url     : https://prove2.me/submissions/1252b792-888e-4f8a-9e37-19457aa853e0

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

open BatchTesting.PTAS

namespace BTCommon

variable {n : ℕ} (I : Instance n) (eps : ℝ)

theorem mem_cls {r : ℕ} {i : Fin n} : i ∈ cls I eps r ↔ classOf I eps i = r := by
  simp [cls]

theorem rank_lt_rank {i j : Fin n} (hij : classOf I eps i = classOf I eps j)
    (h : toLex (I.p i, i) < toLex (I.p j, j)) : rank I eps i < rank I eps j := by
  unfold rank
  rw [hij]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨i, ?_, ?_⟩
    · simp [mem_cls, hij, h]
    · simp
  · intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, lt_trans hk.2 h⟩

theorem rank_injOn (r : ℕ) : Set.InjOn (rank I eps) (cls I eps r) := by
  intro i hi j hj hr
  simp only [Finset.mem_coe, mem_cls] at hi hj
  by_contra hne
  have hlex : toLex (I.p i, i) ≠ toLex (I.p j, j) := by
    intro h
    exact hne (congrArg Prod.snd (toLex.injective h))
  rcases lt_or_gt_of_ne hlex with h | h
  · exact (rank_lt_rank I eps (hi.trans hj.symm) h).ne hr
  · exact (rank_lt_rank I eps (hj.trans hi.symm) h).ne hr.symm

theorem rank_lt_card (i : Fin n) : rank I eps i < (cls I eps (classOf I eps i)).card := by
  unfold rank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨i, by simp [mem_cls], by simp⟩

theorem image_rank (r : ℕ) : (cls I eps r).image (rank I eps) = Finset.range (cls I eps r).card := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have := rank_lt_card I eps i
    rw [(mem_cls I eps).mp hi] at this
    simpa using this
  · rw [Finset.card_image_of_injOn (rank_injOn I eps r)]
    simp

theorem card_filter_rank (r k : ℕ) :
    ((cls I eps r).filter (fun i => rank I eps i < k)).card = min k (cls I eps r).card := by
  have h1 : ((cls I eps r).filter (fun i => rank I eps i < k)).card =
      (((cls I eps r).filter (fun i => rank I eps i < k)).image (rank I eps)).card := by
    rw [Finset.card_image_of_injOn]
    exact (rank_injOn I eps r).mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)
  have h2 : ((cls I eps r).filter (fun i => rank I eps i < k)).image (rank I eps) =
      ((cls I eps r).image (rank I eps)).filter (fun x => x < k) := by
    ext x; simp only [Finset.mem_image, Finset.mem_filter]; constructor
    · rintro ⟨i, ⟨hi, hk⟩, rfl⟩; exact ⟨⟨i, hi, rfl⟩, hk⟩
    · rintro ⟨⟨i, hi, rfl⟩, hk⟩; exact ⟨i, ⟨hi, hk⟩, rfl⟩
  rw [h1, h2, image_rank]
  have : (Finset.range (cls I eps r).card).filter (fun x => x < k) =
      Finset.range (min k (cls I eps r).card) := by
    ext x; simp; omega
  rw [this, Finset.card_range]

theorem mem_tested {N : State I eps} {i : Fin n} :
    i ∈ tested I eps N ↔ rank I eps i < N (classIdx I eps i) := by
  simp [tested]

theorem classIdx_eq_iff (i : Fin n) (r : Fin (R I eps + 1)) :
    classIdx I eps i = r ↔ classOf I eps i = (r : ℕ) := by
  simp [classIdx, Fin.ext_iff]

/-- The class-`r` part of `tested N`. -/
theorem tested_filter (N : State I eps) (r : Fin (R I eps + 1)) :
    (tested I eps N).filter (fun i => classIdx I eps i = r) =
      (cls I eps r).filter (fun i => rank I eps i < N r) := by
  ext i
  simp only [Finset.mem_filter, mem_tested, mem_cls, classIdx_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    have : classIdx I eps i = r := (classIdx_eq_iff I eps i r).mpr h2
    rwa [this] at h1
  · rintro ⟨h2, h1⟩
    have : classIdx I eps i = r := (classIdx_eq_iff I eps i r).mpr h2
    exact ⟨by rwa [this], h2⟩

theorem card_tested_filter (N : State I eps) (r : Fin (R I eps + 1)) :
    ((tested I eps N).filter (fun i => classIdx I eps i = r)).card =
      min (N r) (cls I eps r).card := by
  rw [tested_filter, card_filter_rank]

theorem mem_F {N : State I eps} : N ∈ F I eps ↔ ∀ r, N r ≤ (cls I eps r).card := by
  simp [F, Fintype.mem_piFinset]

theorem tested_mono {N M : State I eps} (h : N ≤ M) : tested I eps N ⊆ tested I eps M := by
  intro i hi
  rw [mem_tested] at hi ⊢
  exact lt_of_lt_of_le hi (h _)

theorem tested_zero : tested I eps 0 = ∅ := by
  ext i; simp [mem_tested]

theorem tested_Nall : tested I eps (Nall I eps) = Finset.univ := by
  ext i
  simp only [mem_tested, Finset.mem_univ, iff_true, Nall, classIdx]
  exact rank_lt_card I eps i

theorem card_sdiff_filter {N M : State I eps} (hNM : N ≤ M) (hM : M ∈ F I eps)
    (r : Fin (R I eps + 1)) :
    ((tested I eps M \ tested I eps N).filter (fun i => classIdx I eps i = r)).card = M r - N r := by
  have hfs : (tested I eps M \ tested I eps N).filter (fun i => classIdx I eps i = r) =
      (tested I eps M).filter (fun i => classIdx I eps i = r) \
        (tested I eps N).filter (fun i => classIdx I eps i = r) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [hfs, Finset.card_sdiff_of_subset, card_tested_filter, card_tested_filter]
  · have h1 := (mem_F I eps).mp hM r
    have h2 := hNM r
    rw [min_eq_left h1, min_eq_left (h2.trans h1)]
  · exact Finset.monotone_filter_left _ (tested_mono I eps hNM)

/-- Sum of a class-dependent weight over a finset, grouped by class. -/
theorem sum_by_class (s : Finset (Fin n)) (f : Fin (R I eps + 1) → ℝ) :
    ∑ i ∈ s, f (classIdx I eps i) =
      ∑ r, ((s.filter (fun i => classIdx I eps i = r)).card : ℝ) * f r := by
  rw [← Finset.sum_fiberwise s (classIdx I eps) (fun i => f (classIdx I eps i))]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_congr rfl (g := fun _ => f r)]
  · simp
  · intro i hi
    rw [(Finset.mem_filter.mp hi).2]

theorem P0_nonneg (hI : I.Standing) (N : State I eps) : 0 ≤ P0 I eps N :=
  Finset.prod_nonneg fun i _ => (hI.2.1 i).1

theorem P0_le_one (hI : I.Standing) (N : State I eps) : P0 I eps N ≤ 1 :=
  Finset.prod_le_one (fun i _ => (hI.2.1 i).1) (fun i _ => (hI.2.1 i).2)

theorem P0_anti (hI : I.Standing) {N M : State I eps} (h : N ≤ M) : P0 I eps M ≤ P0 I eps N := by
  unfold P0
  rw [← Finset.prod_sdiff (tested_mono I eps h)]
  calc (∏ i ∈ tested I eps M \ tested I eps N, I.p i) * ∏ i ∈ tested I eps N, I.p i
      ≤ 1 * ∏ i ∈ tested I eps N, I.p i := by
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun i _ => (hI.2.1 i).1)
        exact Finset.prod_le_one (fun i _ => (hI.2.1 i).1) (fun i _ => (hI.2.1 i).2)
    _ = _ := one_mul _

theorem P0_zero : P0 I eps 0 = 1 := by
  simp [P0, tested_zero]

theorem cmin_pos (hI : I.Standing) : 0 < cmin I := by
  obtain ⟨hn, -, hc, -⟩ := hI
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := I.c)
  unfold cmin; rw [← hj]; exact hc j

theorem stepCost_nonneg (hI : I.Standing) (h0 : 0 < eps) (Δ : State I eps) :
    0 ≤ stepCost I eps Δ := by
  unfold stepCost
  have := cmin_pos I hI
  have := hI.2.2.2
  apply add_nonneg (div_nonneg this (le_of_lt ‹_›))
  exact Finset.sum_nonneg fun r _ => by positivity

theorem pathCost_cons_cons (a b : State I eps) (l : List (State I eps)) :
    pathCost I eps (a :: b :: l) = P0 I eps a * stepCost I eps (b - a) + pathCost I eps (b :: l) := by
  simp [pathCost]

theorem pathCost_single (a : State I eps) : pathCost I eps [a] = 0 := by
  simp [pathCost]

theorem pathCost_nil : pathCost I eps [] = 0 := by
  simp [pathCost]

theorem schemeOf_cons_cons (a b : State I eps) (l : List (State I eps)) :
    schemeOf I eps (a :: b :: l) = (tested I eps b \ tested I eps a) :: schemeOf I eps (b :: l) := by
  simp [schemeOf]

theorem schemeOf_single (a : State I eps) : schemeOf I eps [a] = [] := by
  simp [schemeOf]

theorem phi_cons_succ (B : Finset (Fin n)) (S : List (Finset (Fin n))) (t : ℕ) :
    phi I (B :: S) (t + 1) = (∏ i ∈ B, I.p i) * phi I S t := by
  unfold phi
  rw [Finset.prod_range_succ']
  simp [mul_comm]

theorem expectedCostWith_cons (c : Fin n → ℝ) (B : Finset (Fin n)) (S : List (Finset (Fin n))) :
    expectedCostWith I c (B :: S) =
      batchCost I c B + (∏ i ∈ B, I.p i) * expectedCostWith I c S := by
  unfold expectedCostWith
  rw [List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
  simp only [phi_cons_succ, List.getD_cons_succ, List.getD_cons_zero]
  have : phi I (B :: S) 0 = 1 := by simp [phi]
  rw [this, one_mul, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem batchCost_step (hI : I.Standing) {a b : State I eps} (hab : a ≤ b) (hb : b ∈ F I eps) :
    batchCost I (roundedCost I eps) (tested I eps b \ tested I eps a) =
      cmin I * stepCost I eps (b - a) := by
  have hm := cmin_pos I hI
  unfold batchCost stepCost
  have hsum : ∑ i ∈ tested I eps b \ tested I eps a, roundedCost I eps i =
      ∑ i ∈ tested I eps b \ tested I eps a,
        (fun r : Fin (R I eps + 1) => cmin I * (1 + eps) ^ (r : ℕ)) (classIdx I eps i) := rfl
  rw [hsum, sum_by_class I eps _ (fun r : Fin (R I eps + 1) => cmin I * (1 + eps) ^ (r : ℕ))]
  simp only [card_sdiff_filter I eps hab hb, Pi.sub_apply]
  rw [mul_add, Finset.mul_sum, mul_div_cancel₀ _ hm.ne']
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  ring


theorem pathCost_eq_sum (l : List (State I eps)) :
    pathCost I eps l = ∑ m ∈ Finset.range (l.length - 1),
      P0 I eps (l.getD m 0) * stepCost I eps (l.getD (m + 1) 0 - l.getD m 0) := by
  induction l with
  | nil => simp [pathCost_nil]
  | cons a l ih =>
    cases l with
    | nil => simp [pathCost_single]
    | cons b rest =>
      rw [pathCost_cons_cons, ih]
      simp only [List.length_cons, Nat.add_sub_cancel]
      rw [Finset.sum_range_succ' _ (rest.length)]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [add_comm]

/-- Removing repeated consecutive states from a monotone list gives a strictly increasing chain
with the same endpoints, states among the original ones, and no larger cost. -/
theorem dedupe (hI : I.Standing) (h0 : 0 < eps) :
    ∀ (rest : List (State I eps)) (a : State I eps), (a :: rest).IsChain (· ≤ ·) →
      ∃ t : List (State I eps), (a :: t).getLast? = (a :: rest).getLast? ∧
        (∀ N ∈ a :: t, N ∈ a :: rest) ∧ (a :: t).IsChain (fun N M => N ≤ M ∧ N ≠ M) ∧
        pathCost I eps (a :: t) ≤ pathCost I eps (a :: rest) := by
  intro rest
  induction rest with
  | nil =>
    intro a _
    exact ⟨[], rfl, fun N hN => hN, List.isChain_singleton _, le_rfl⟩
  | cons b rest ih =>
    intro a hch
    rw [List.isChain_cons_cons] at hch
    obtain ⟨t, hlast, hsub, hch', hcost⟩ := ih b hch.2
    have hstep : 0 ≤ P0 I eps a * stepCost I eps (b - a) :=
      mul_nonneg (P0_nonneg I eps hI a) (stepCost_nonneg I eps hI h0 _)
    by_cases hab : a = b
    · subst hab
      refine ⟨t, ?_, ?_, hch', ?_⟩
      · rw [hlast, List.getLast?_cons_cons]
      · intro N hN; exact List.mem_cons_of_mem _ (hsub N hN)
      · rw [pathCost_cons_cons]; linarith
    · refine ⟨b :: t, ?_, ?_, ?_, ?_⟩
      · rw [List.getLast?_cons_cons, hlast, List.getLast?_cons_cons]
      · intro N hN
        rcases List.mem_cons.mp hN with rfl | hN
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub N hN)
      · rw [List.isChain_cons_cons]; exact ⟨⟨hch.1, hab⟩, hch'⟩
      · rw [pathCost_cons_cons, pathCost_cons_cons]; linarith

theorem getD_last_of_getLast? {l : List (State I eps)} {x : State I eps}
    (h : l.getLast? = some x) : l.getD (l.length - 1) 0 = x := by
  rw [List.getLast?_eq_getElem?] at h
  rw [List.getD_eq_getElem?_getD, h]; rfl

theorem isChain_of_getD {l : List (State I eps)} {Rel : State I eps → State I eps → Prop}
    (h : ∀ m, m + 1 < l.length → Rel (l.getD m 0) (l.getD (m + 1) 0)) : l.IsChain Rel := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have := h i hi
  rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi] at this

theorem getD_of_isChain {l : List (State I eps)} {Rel : State I eps → State I eps → Prop}
    (h : l.IsChain Rel) : ∀ m, m + 1 < l.length → Rel (l.getD m 0) (l.getD (m + 1) 0) := by
  intro m hm
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hm]
  exact List.isChain_iff_getElem.mp h m hm


theorem path_nodup (G : Finset (State I eps))
    (π : List (State I eps)) (hπ : IsPath I eps G π) : π.Nodup := by
  have h1 : π.IsChain (fun N M : State I eps => N < M) :=
    hπ.2.2.2.imp (fun a b h => lt_of_le_of_ne h.1 h.2)
  have h2 : π.Pairwise (fun N M : State I eps => N < M) := List.isChain_iff_pairwise.mp h1
  exact h2.imp (fun h => ne_of_lt h)

theorem exists_optPath (G : Finset (State I eps))
    (h : ∃ π, IsPath I eps G π) : ∃ π, IsOptPath I eps G π := by
  classical
  let L : Finset (List (State I eps)) :=
    (G.powerset.biUnion fun s => s.val.lists.toFinset).filter (IsPath I eps G)
  have hmem : ∀ π, IsPath I eps G π → π ∈ L := by
    intro π hπ
    simp only [L, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_powerset]
    refine ⟨⟨π.toFinset, ?_, ?_⟩, hπ⟩
    · intro x hx
      exact hπ.2.2.1 x (List.mem_toFinset.mp hx)
    · rw [Multiset.mem_toFinset, Multiset.mem_lists_iff, List.toFinset_val,
        (path_nodup I eps G π hπ).dedup]
      rfl
  obtain ⟨π0, hπ0⟩ := h
  have hne : L.Nonempty := ⟨π0, hmem π0 hπ0⟩
  obtain ⟨π, hπL, hmin⟩ := L.exists_min_image (pathCost I eps) hne
  exact ⟨π, (Finset.mem_filter.mp hπL).2, fun π' hπ' => hmin π' (hmem π' hπ')⟩

theorem IsPath.mono {G G' : Finset (State I eps)} (hGG : G ⊆ G') {π : List (State I eps)}
    (h : IsPath I eps G π) : IsPath I eps G' π :=
  ⟨h.1, h.2.1, fun N hN => hGG (h.2.2.1 N hN), h.2.2.2⟩

theorem FNice_sub_F : FNice I eps ⊆ F I eps := by
  classical
  intro N hN; unfold FNice at hN; exact (Finset.mem_filter.mp hN).1

theorem FGreat_sub_F : FGreat I eps ⊆ F I eps := by
  classical
  intro N hN; unfold FGreat at hN; exact (Finset.mem_filter.mp hN).1


theorem le_psi {m : ℕ} (N : Fin m → ℕ) (r : Fin m) (h : N r ≠ 0) : (r : ℤ) ≤ psi N := by
  unfold psi
  have : (r : ℕ) + 1 ≤ (Finset.univ.filter (fun r => N r ≠ 0)).sup (fun r => (r : ℕ) + 1) :=
    Finset.le_sup (f := fun r : Fin m => (r : ℕ) + 1) (by simp [h])
  omega

theorem psi_cases {m : ℕ} (N : Fin m → ℕ) :
    psi N = -1 ∨ ∃ r : Fin m, N r ≠ 0 ∧ psi N = r := by
  unfold psi
  by_cases hs : (Finset.univ.filter (fun r => N r ≠ 0)).Nonempty
  · obtain ⟨r, hr, heq⟩ := Finset.exists_mem_eq_sup _ hs (fun r : Fin m => (r : ℕ) + 1)
    right
    refine ⟨r, (Finset.mem_filter.mp hr).2, ?_⟩
    rw [heq]; push_cast; ring
  · left
    rw [Finset.not_nonempty_iff_eq_empty] at hs
    rw [hs]; simp

theorem neg_one_le_psi {m : ℕ} (N : Fin m → ℕ) : -1 ≤ psi N := by
  unfold psi; omega

theorem psi_le {m : ℕ} (N : Fin m → ℕ) (x : ℤ) (hx : -1 ≤ x)
    (h : ∀ r : Fin m, N r ≠ 0 → (r : ℤ) ≤ x) : psi N ≤ x := by
  rcases psi_cases N with h1 | ⟨r, hr, h1⟩
  · rw [h1]; exact hx
  · rw [h1]; exact h r hr

theorem psi_eq_zero_of_lt {m : ℕ} (N : Fin m → ℕ) (r : Fin m) (h : psi N < r) : N r = 0 := by
  by_contra hne; exact absurd (le_psi N r hne) (not_le.mpr h)

theorem mem_FNice {N : State I eps} : N ∈ FNice I eps ↔ N ∈ F I eps ∧ IsNice I eps N := by
  classical
  unfold FNice; simp only [Finset.mem_filter]

theorem mem_FGreat {N : State I eps} : N ∈ FGreat I eps ↔ N ∈ F I eps ∧ IsGreat I eps N := by
  classical
  unfold FGreat; simp only [Finset.mem_filter]


theorem forall2_getD {Rel : State I eps → State I eps → Prop} {l1 l2 : List (State I eps)}
    (h : List.Forall₂ Rel l1 l2) : ∀ t, t < l1.length → Rel (l1.getD t 0) (l2.getD t 0) := by
  intro t ht
  have hlen := h.length_eq
  have := (List.forall₂_iff_get.mp h).2 t ht (by omega)
  simp only [List.get_eq_getElem] at this
  rwa [List.getD_eq_getElem _ _ ht, List.getD_eq_getElem _ _ (by omega)]

theorem kappa_nonneg (hI : I.Standing) (h0 : 0 < eps) (h1 : eps ≤ 1) : 0 ≤ kappa n eps := by
  unfold kappa
  apply Int.ceil_nonneg
  apply Real.logb_nonneg (by linarith)
  rw [le_div_iff₀ h0, one_mul]
  have : (1 : ℝ) ≤ n := by exact_mod_cast hI.1
  linarith

theorem zero_mem_F : (0 : State I eps) ∈ F I eps := by
  rw [mem_F]; intro r; simp

theorem isNice_zero (hI : I.Standing) (h0 : 0 < eps) (h1 : eps ≤ 1) : IsNice I eps 0 := by
  intro r hr
  have := kappa_nonneg I eps hI h0 h1
  have hp : psi (0 : State I eps) = -1 := by
    rcases psi_cases (0 : State I eps) with h | ⟨r', hr', _⟩
    · exact h
    · simp at hr'
  rw [hp] at hr
  omega


theorem forall2_of_getD {Rel : State I eps → State I eps → Prop} {l1 l2 : List (State I eps)}
    (hlen : l1.length = l2.length)
    (h : ∀ t, t < l1.length → Rel (l1.getD t 0) (l2.getD t 0)) : List.Forall₂ Rel l1 l2 := by
  rw [List.forall₂_iff_get]
  refine ⟨hlen, fun i h1 h2 => ?_⟩
  have := h i h1
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem path_getD_mem {G : Finset (State I eps)} {π : List (State I eps)} (hπ : IsPath I eps G π)
    (t : ℕ) (ht : t < π.length) : π.getD t 0 ∈ G := by
  rw [List.getD_eq_getElem _ _ ht]
  exact hπ.2.2.1 _ (List.getElem_mem _)

theorem path_ne_nil {G : Finset (State I eps)} {π : List (State I eps)} (hπ : IsPath I eps G π) :
    π ≠ [] := by
  intro h; have := hπ.1; rw [h] at this; simp at this

theorem path_getD_zero {G : Finset (State I eps)} {π : List (State I eps)} (hπ : IsPath I eps G π) :
    π.getD 0 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, hπ.1]; rfl

theorem path_mono {G : Finset (State I eps)} {π : List (State I eps)} (hπ : IsPath I eps G π)
    (t : ℕ) (ht : t + 1 < π.length) : π.getD t 0 ≤ π.getD (t + 1) 0 :=
  (getD_of_isChain I eps hπ.2.2.2 t ht).1


theorem sum_card_cls : ∑ r : Fin (R I eps + 1), ((cls I eps r).card : ℝ) = n := by
  have h := sum_by_class I eps Finset.univ (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro r _
  congr 2
  ext i; simp [classIdx_eq_iff, mem_cls]

theorem pow_kappa (hI : I.Standing) (h0 : 0 < eps) (h1 : eps ≤ 1) :
    (n : ℝ) / eps ≤ (1 + eps) ^ (kappa n eps).toNat := by
  have hκ := kappa_nonneg I eps hI h0 h1
  have hb : (1 : ℝ) < 1 + eps := by linarith
  have hx : 0 < (n : ℝ) / eps := div_pos (by exact_mod_cast hI.1) h0
  rw [← Real.rpow_natCast]
  have hc : ((kappa n eps).toNat : ℝ) = ((kappa n eps : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hκ]
  rw [hc]
  calc (n : ℝ) / eps = (1 + eps) ^ Real.logb (1 + eps) ((n : ℝ) / eps) :=
        (Real.rpow_logb (by linarith) hb.ne' hx).symm
    _ ≤ (1 + eps) ^ ((kappa n eps : ℤ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hb.le (Int.le_ceil _)


theorem path_mono' {G : Finset (State I eps)} {π : List (State I eps)} (hπ : IsPath I eps G π)
    (a b : ℕ) (hab : a ≤ b) (hb : b < π.length) : π.getD a 0 ≤ π.getD b 0 := by
  induction b with
  | zero => rw [Nat.le_zero.mp hab]
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le hab with h | h
    · exact le_trans (ih (by omega) (by omega)) (path_mono I eps hπ b hb)
    · rw [h]

end BTCommon

open BatchTesting.PTAS

namespace BTSeq
open BTCommon

variable {n : ℕ} (I : Instance n) (eps : ℝ)

theorem bucketed_eq (π : List (State I eps)) :
    ∃ f : ℕ → Option (State I eps), bucketed I eps π = (List.range π.length).filterMap f ∧
      f 0 = some (π.getD 0 0) ∧ f (π.length - 1) = some (π.getD (π.length - 1) 0) ∧
      ∀ t, ∀ x, f t = some x → x = π.getD t 0 := by
  classical
  refine ⟨fun t => if t = 0 ∨ t + 1 = π.length ∨
        bucketIndex eps (P0 I eps (π.getD (t - 1) 0)) ≠ bucketIndex eps (P0 I eps (π.getD t 0))
    then some (π.getD t 0) else none, ?_, ?_, ?_, ?_⟩
  · unfold bucketed; congr
  · simp
  · by_cases h : π.length = 0
    · simp [h]
    · dsimp only
      rw [if_pos (Or.inr (Or.inl (by omega)))]
  · intro t x h
    dsimp only at h
    split_ifs at h
    · exact (Option.some.inj h).symm

theorem bucketed_head (π : List (State I eps)) (hne : π ≠ []) :
    (bucketed I eps π).head? = some (π.getD 0 0) := by
  obtain ⟨f, hf, h0, -, -⟩ := bucketed_eq I eps π
  obtain ⟨k, hk⟩ : ∃ k, π.length = k + 1 := ⟨π.length - 1, by
    have := List.length_pos_iff.mpr hne; omega⟩
  rw [hf, hk, List.range_succ_eq_map, List.filterMap_cons, h0]
  rfl

theorem bucketed_getLast (π : List (State I eps)) (hne : π ≠ []) :
    (bucketed I eps π).getLast? = π.getLast? := by
  obtain ⟨f, hf, -, hl, -⟩ := bucketed_eq I eps π
  obtain ⟨k, hk⟩ : ∃ k, π.length = k + 1 := ⟨π.length - 1, by
    have := List.length_pos_iff.mpr hne; omega⟩
  rw [hf, hk, List.range_succ, List.filterMap_append]
  rw [hk, Nat.add_sub_cancel] at hl
  simp only [List.filterMap_cons, hl, List.filterMap_nil, List.getLast?_append,
    List.getLast?_singleton, Option.some_or]
  have : k < π.length := by omega
  rw [List.getLast?_eq_getElem?, hk, Nat.add_sub_cancel, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem this]
  rfl

theorem bucketed_ne_nil (π : List (State I eps)) (hne : π ≠ []) : bucketed I eps π ≠ [] := by
  intro h
  have := bucketed_head I eps π hne
  rw [h] at this; simp at this

theorem greatSeqAux_length (N : State I eps) (D : List (State I eps)) :
    (greatSeqAux I eps N D).length = D.length := by
  induction D generalizing N with
  | nil => rfl
  | cons d D ih => simp [greatSeqAux, ih]

theorem greatSeq_length (D : List (State I eps)) (hD : D ≠ []) :
    (greatSeq I eps D).length = D.length := by
  cases D with
  | nil => exact absurd rfl hD
  | cons d D => simp [greatSeq, greatSeqAux_length]

theorem greatSeqAux_succ :
    ∀ (D : List (State I eps)) (N : State I eps) (m : ℕ), m < D.length →
      (N :: greatSeqAux I eps N D).getD (m + 1) 0 =
        greatNext I eps ((N :: greatSeqAux I eps N D).getD m 0) (D.getD m 0) := by
  intro D
  induction D with
  | nil => intro N m h; simp at h
  | cons d D ih =>
    intro N m hm
    cases m with
    | zero => simp [greatSeqAux]
    | succ m =>
      have := ih (greatNext I eps N d) m (by simp at hm; omega)
      simp only [greatSeqAux, List.getD_cons_succ] at this ⊢
      exact this

theorem greatSeq_succ (D : List (State I eps)) (m : ℕ) (hm : m + 1 < D.length) :
    (greatSeq I eps D).getD (m + 1) 0 =
      greatNext I eps ((greatSeq I eps D).getD m 0) (D.getD (m + 1) 0) := by
  cases D with
  | nil => simp at hm
  | cons d D =>
    simp only [greatSeq, List.tail_cons, List.getD_cons_succ]
    exact greatSeqAux_succ I eps D 0 m (by simp at hm; omega)

theorem greatSeq_zero (D : List (State I eps)) : (greatSeq I eps D).getD 0 0 = 0 := by
  simp [greatSeq]

theorem greatDeltaZ_eq (Nprev Nd : State I eps) (r : Fin (R I eps + 1))
    (h : 0 ≤ greatDeltaZ I eps Nprev Nd r) :
    (((greatNext I eps Nprev Nd - Nprev) r : ℕ) : ℤ) = greatDeltaZ I eps Nprev Nd r ∧
      Nprev r ≤ greatNext I eps Nprev Nd r := by
  unfold greatDeltaZ at h ⊢
  unfold greatNext
  simp only [Pi.sub_apply]
  split_ifs at h ⊢ <;> omega


theorem niceSeqAux_length (N : State I eps) (D : List (State I eps)) :
    (niceSeqAux I eps N D).length = D.length := by
  induction D generalizing N with
  | nil => rfl
  | cons d D ih => simp [niceSeqAux, ih]

theorem niceSeq_length (π : List (State I eps)) (hπ : π ≠ []) :
    (niceSeq I eps π).length = π.length := by
  cases π with
  | nil => exact absurd rfl hπ
  | cons d D => simp [niceSeq, niceSeqAux_length]

theorem niceSeqAux_succ :
    ∀ (D : List (State I eps)) (N : State I eps) (m : ℕ), m < D.length →
      (N :: niceSeqAux I eps N D).getD (m + 1) 0 =
        (N :: niceSeqAux I eps N D).getD m 0 +
          niceDelta I eps ((N :: niceSeqAux I eps N D).getD m 0) (D.getD m 0) := by
  intro D
  induction D with
  | nil => intro N m h; simp at h
  | cons d D ih =>
    intro N m hm
    cases m with
    | zero => simp [niceSeqAux]
    | succ m =>
      have := ih (N + niceDelta I eps N d) m (by simp at hm; omega)
      simp only [niceSeqAux, List.getD_cons_succ] at this ⊢
      exact this

theorem niceSeq_succ (π : List (State I eps)) (m : ℕ) (hm : m + 1 < π.length) :
    (niceSeq I eps π).getD (m + 1) 0 =
      (niceSeq I eps π).getD m 0 + niceDelta I eps ((niceSeq I eps π).getD m 0) (π.getD (m + 1) 0) := by
  cases π with
  | nil => simp at hm
  | cons d D =>
    simp only [niceSeq, List.tail_cons, List.getD_cons_succ]
    exact niceSeqAux_succ I eps D 0 m (by simp at hm; omega)

theorem niceSeq_zero (π : List (State I eps)) : (niceSeq I eps π).getD 0 0 = 0 := by
  simp [niceSeq]

/-- One step of §3.4 dominates its target. -/
theorem niceDelta_dom (Nprev Nstar : State I eps) (hS : Nstar ∈ F I eps) :
    Nstar ≤ Nprev + niceDelta I eps Nprev Nstar := by
  intro r
  have hSr := (mem_F I eps).mp hS r
  simp only [Pi.add_apply]
  unfold niceDelta
  split_ifs with h1 h2
  · have := psi_eq_zero_of_lt (Nstar - Nprev) r h1
    simp only [Pi.sub_apply] at this
    omega
  · simp only [Pi.sub_apply]; omega
  · omega

theorem niceSeq_dom (π : List (State I eps)) (hπ : IsPath I eps (F I eps) π) :
    ∀ t, t < π.length → π.getD t 0 ≤ (niceSeq I eps π).getD t 0 := by
  intro t ht
  cases t with
  | zero => rw [path_getD_zero I eps hπ, niceSeq_zero]
  | succ t =>
    rw [niceSeq_succ I eps π t ht]
    exact niceDelta_dom I eps _ _ (path_getD_mem I eps hπ _ ht)

end BTSeq

open BatchTesting.PTAS

namespace BTBucket
open BTCommon BTSeq

theorem filterMap_ite {α β : Type} (p : α → Prop) [DecidablePred p] (g : α → β) (l : List α) :
    l.filterMap (fun t => if p t then some (g t) else none) = (l.filter (fun t => decide (p t))).map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a
    · simp [List.filterMap_cons, h, ih, List.filter_cons]
    · simp [List.filterMap_cons, h, ih, List.filter_cons]

/-- In a strictly increasing list of naturals, `getD` is strictly monotone. -/
theorem getD_lt_getD {l : List ℕ} (hl : l.Pairwise (· < ·)) {i j : ℕ} (hij : i < j)
    (hj : j < l.length) : l.getD i 0 < l.getD j 0 := by
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj]
  exact List.pairwise_iff_getElem.mp hl i j (by omega) hj hij

theorem getD_le_getD {l : List ℕ} (hl : l.Pairwise (· < ·)) {i j : ℕ} (hij : i ≤ j)
    (hj : j < l.length) : l.getD i 0 ≤ l.getD j 0 := by
  rcases Nat.lt_or_eq_of_le hij with h | rfl
  · exact (getD_lt_getD hl h hj).le
  · exact le_rfl

theorem lt_of_getD_lt {l : List ℕ} (hl : l.Pairwise (· < ·)) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (h : l.getD i 0 < l.getD j 0) : i < j := by
  by_contra hc
  push_neg at hc
  exact absurd h (not_lt.mpr (getD_le_getD hl hc hi))

variable {n : ℕ} (I : Instance n) (eps : ℝ)

/-- The keep-rule of the bucketing (pp. 17–18). -/
def keep (π : List (State I eps)) (t : ℕ) : Prop :=
  t = 0 ∨ t + 1 = π.length ∨
    bucketIndex eps (P0 I eps (π.getD (t - 1) 0)) ≠ bucketIndex eps (P0 I eps (π.getD t 0))

open Classical in
/-- The kept indices, in increasing order. -/
noncomputable def ks (π : List (State I eps)) : List ℕ :=
  (List.range π.length).filter (fun t => decide (keep I eps π t))

theorem bucketed_eq_map (π : List (State I eps)) :
    bucketed I eps π = (ks I eps π).map (fun t => π.getD t 0) := by
  classical
  unfold bucketed ks
  rw [← filterMap_ite]
  congr 1
  funext t
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; exact h2 h1) | (exfalso; exact h1 h2)

theorem ks_sorted (π : List (State I eps)) : (ks I eps π).Pairwise (· < ·) := by
  unfold ks
  exact (List.pairwise_lt_range).filter _

theorem mem_ks (π : List (State I eps)) (t : ℕ) :
    t ∈ ks I eps π ↔ t < π.length ∧ keep I eps π t := by
  classical
  unfold ks
  simp [List.mem_filter, List.mem_range]

theorem ks_length_pos (π : List (State I eps)) (hπ : π ≠ []) : 0 < (ks I eps π).length := by
  have : 0 ∈ ks I eps π := (mem_ks I eps π 0).mpr ⟨List.length_pos_iff.mpr hπ, Or.inl rfl⟩
  exact List.length_pos_of_mem this

theorem ks_getD_lt (π : List (State I eps)) (j : ℕ) (hj : j < (ks I eps π).length) :
    (ks I eps π).getD j 0 < π.length := by
  rw [List.getD_eq_getElem _ _ hj]
  exact ((mem_ks I eps π _).mp (List.getElem_mem hj)).1

theorem ks_getD_keep (π : List (State I eps)) (j : ℕ) (hj : j < (ks I eps π).length) :
    keep I eps π ((ks I eps π).getD j 0) := by
  rw [List.getD_eq_getElem _ _ hj]
  exact ((mem_ks I eps π _).mp (List.getElem_mem hj)).2

theorem ks_index_of_mem (π : List (State I eps)) (t : ℕ) (ht : t ∈ ks I eps π) :
    ∃ i, i < (ks I eps π).length ∧ (ks I eps π).getD i 0 = t := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  exact ⟨i, hi, List.getD_eq_getElem _ _ hi⟩

theorem ks_first (π : List (State I eps)) (hπ : π ≠ []) : (ks I eps π).getD 0 0 = 0 := by
  have h0 : 0 ∈ ks I eps π := (mem_ks I eps π 0).mpr ⟨List.length_pos_iff.mpr hπ, Or.inl rfl⟩
  obtain ⟨i, hi, hit⟩ := ks_index_of_mem I eps π 0 h0
  have := getD_le_getD (ks_sorted I eps π) (Nat.zero_le i) hi
  omega

theorem ks_last (π : List (State I eps)) (hπ : π ≠ []) :
    (ks I eps π).getD ((ks I eps π).length - 1) 0 = π.length - 1 := by
  have hlen := List.length_pos_iff.mpr hπ
  have hL : π.length - 1 ∈ ks I eps π :=
    (mem_ks I eps π _).mpr ⟨by omega, Or.inr (Or.inl (by omega))⟩
  obtain ⟨i, hi, hit⟩ := ks_index_of_mem I eps π _ hL
  have hk := ks_length_pos I eps π hπ
  have h1 := getD_le_getD (ks_sorted I eps π) (show i ≤ (ks I eps π).length - 1 by omega)
    (by omega)
  have h2 := ks_getD_lt I eps π ((ks I eps π).length - 1) (by omega)
  omega

/-- No index strictly between two consecutive kept indices is kept. -/
theorem not_keep_between (π : List (State I eps)) (j : ℕ) (hj : j + 1 < (ks I eps π).length)
    (t : ℕ) (h1 : (ks I eps π).getD j 0 < t) (h2 : t < (ks I eps π).getD (j + 1) 0) :
    ¬ keep I eps π t := by
  intro hk
  have htlen : t < π.length := lt_trans h2 (ks_getD_lt I eps π _ hj)
  obtain ⟨i, hi, rfl⟩ := ks_index_of_mem I eps π t ((mem_ks I eps π t).mpr ⟨htlen, hk⟩)
  have hji := lt_of_getD_lt (ks_sorted I eps π) (by omega) hi h1
  have := getD_le_getD (ks_sorted I eps π) (show j + 1 ≤ i by omega) hi
  omega

theorem bucketed_length (π : List (State I eps)) :
    (bucketed I eps π).length = (ks I eps π).length := by
  rw [bucketed_eq_map, List.length_map]

theorem bucketed_getD (π : List (State I eps)) (j : ℕ) (hj : j < (ks I eps π).length) :
    (bucketed I eps π).getD j 0 = π.getD ((ks I eps π).getD j 0) 0 := by
  rw [bucketed_eq_map, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
    List.getD_eq_getElem _ _ hj]

/-- Two probabilities in the same bucket are within a factor `1 + ε`. -/
theorem same_bucket_ratio (h0 : 0 < eps) {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) (h : bucketIndex eps x = bucketIndex eps y) : x ≤ (1 + eps) * y := by
  unfold bucketIndex at h
  by_cases hx : x ≤ 0
  · have : x = 0 := le_antisymm hx hx0
    rw [this]; positivity
  · have hy : ¬ y ≤ 0 := by
      intro hy; rw [if_neg hx, if_pos hy] at h; exact WithTop.coe_ne_top h
    rw [if_neg hx, if_neg hy] at h
    have hk : ⌊-Real.logb (1 + eps) x⌋₊ = ⌊-Real.logb (1 + eps) y⌋₊ := by
      have h' : (⌊-Real.logb (1 + eps) x⌋₊ + 1 : ℕ) = ⌊-Real.logb (1 + eps) y⌋₊ + 1 :=
        WithTop.coe_injective h
      omega
    push_neg at hx hy
    have hb : (1 : ℝ) < 1 + eps := by linarith
    have hlx : 0 ≤ -Real.logb (1 + eps) x := by
      have := Real.logb_nonpos hb hx0 hx1; linarith
    have hly : 0 ≤ -Real.logb (1 + eps) y := by
      have := Real.logb_nonpos hb hy0 hy1; linarith
    have e1 := Nat.floor_le hlx
    have e2 := Nat.lt_floor_add_one (-Real.logb (1 + eps) y)
    rw [← hk] at e2
    -- logb x > logb y - 1
    have hlog : Real.logb (1 + eps) x ≤ Real.logb (1 + eps) y + 1 := by linarith
    have hxy : x = (1 + eps) ^ Real.logb (1 + eps) x := (Real.rpow_logb (by linarith) hb.ne' hx).symm
    have hyy : y = (1 + eps) ^ Real.logb (1 + eps) y := (Real.rpow_logb (by linarith) hb.ne' hy).symm
    calc x = (1 + eps) ^ Real.logb (1 + eps) x := hxy
      _ ≤ (1 + eps) ^ (Real.logb (1 + eps) y + 1) := Real.rpow_le_rpow_of_exponent_le hb.le hlog
      _ = (1 + eps) * y := by
          rw [Real.rpow_add (by linarith), Real.rpow_one, ← hyy]; ring

end BTBucket

open BatchTesting.PTAS

namespace BTL4
open BTCommon BTSeq BTBucket

/-- The bucket exponent `⌊-log_{1+ε} x⌋`. -/
noncomputable def kk (eps x : ℝ) : ℕ := ⌊-Real.logb (1 + eps) x⌋₊

theorem kk_facts (eps x : ℝ) (h0 : 0 < eps) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    x * (1 + eps) ^ kk eps x ≤ 1 ∧ 1 < (1 + eps) ^ (kk eps x + 1) * x := by
  have hb : (1 : ℝ) < 1 + eps := by linarith
  have hb0 : (0 : ℝ) < 1 + eps := by linarith
  have hy : 0 ≤ -Real.logb (1 + eps) x := by
    have := Real.logb_nonpos hb hx0.le hx1; linarith
  have e1 := Nat.floor_le hy
  have e2 := Nat.lt_floor_add_one (-Real.logb (1 + eps) x)
  have hx : x = (1 + eps) ^ Real.logb (1 + eps) x := (Real.rpow_logb hb0 hb.ne' hx0).symm
  unfold kk
  set m := ⌊-Real.logb (1 + eps) x⌋₊ with hm
  have k1 : x * (1 + eps) ^ m = (1 + eps) ^ (Real.logb (1 + eps) x + (m : ℝ)) := by
    rw [Real.rpow_add hb0, ← hx, Real.rpow_natCast]
  have k2 : (1 + eps) ^ (m + 1) * x = (1 + eps) ^ (((m + 1 : ℕ) : ℝ) + Real.logb (1 + eps) x) := by
    rw [Real.rpow_add hb0, ← hx, Real.rpow_natCast]
  constructor
  · rw [k1]
    apply Real.rpow_le_one_of_one_le_of_nonpos hb.le
    linarith
  · rw [k2]
    apply Real.one_lt_rpow hb
    push_cast
    linarith

theorem kk_mono (eps : ℝ) (h0 : 0 < eps) {x y : ℝ} (hy0 : 0 < y) (hyx : y ≤ x) :
    kk eps x ≤ kk eps y := by
  unfold kk
  apply Nat.floor_le_floor
  have : Real.logb (1 + eps) y ≤ Real.logb (1 + eps) x :=
    Real.logb_le_logb_of_le (by linarith) hy0 hyx
  linarith

theorem bucketIndex_pos (eps x : ℝ) (hx : 0 < x) :
    bucketIndex eps x = ((kk eps x + 1 : ℕ) : WithTop ℕ) := by
  unfold bucketIndex kk; rw [if_neg (not_le.mpr hx)]

variable {n : ℕ} (I : Instance n) (eps : ℝ)

end BTL4

open BTCommon BTSeq BTBucket BTL4 in
theorem solution {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1)
    (πs : List (State I eps)) (hπs : IsPath I eps (F I eps) πs) :
    ∀ k, k + 1 < (bucketed I eps πs).length →
      ∑ j ∈ Finset.Ico k ((bucketed I eps πs).length - 1), P0 I eps ((bucketed I eps πs).getD j 0) ≤
        (1 + eps) ^ 2 / eps * P0 I eps ((bucketed I eps πs).getD k 0) := by
  intro k hk
  have hne := path_ne_nil I eps hπs
  rw [bucketed_length] at hk ⊢
  set L := (ks I eps πs).length with hL
  set B : ℝ := 1 + eps with hB
  have hB1 : 1 < B := by linarith
  have hB0 : 0 < B := by linarith
  let τ : ℕ → ℕ := fun j => (ks I eps πs).getD j 0
  let p : ℕ → ℝ := fun j => P0 I eps ((bucketed I eps πs).getD j 0)
  have hp : ∀ j, j < L → p j = P0 I eps (πs.getD (τ j) 0) := by
    intro j hj; simp only [p, τ]; rw [bucketed_getD I eps πs j hj]
  have hp0 : ∀ j, 0 ≤ p j := fun j => P0_nonneg I eps hI _
  have hp1 : ∀ j, p j ≤ 1 := fun j => P0_le_one I eps hI _
  have hanti : ∀ i j, i ≤ j → j < L → p j ≤ p i := by
    intro i j hij hj
    rw [hp i (by omega), hp j hj]
    exact P0_anti I eps hI (path_mono' I eps hπs _ _ (getD_le_getD (ks_sorted I eps πs) hij hj)
      (ks_getD_lt I eps πs j hj))
  have hτ0 : τ 0 = 0 := ks_first I eps πs hne
  have hτL : τ (L - 1) = πs.length - 1 := ks_last I eps πs hne
  -- consecutive buckets strictly increase
  have hstep : ∀ j, j + 2 < L → 0 < p (j + 1) → kk eps (p j) + 1 ≤ kk eps (p (j + 1)) := by
    intro j hj hpos
    set s := τ (j + 1) with hs
    have hs0 : 0 < s := by
      have := getD_lt_getD (ks_sorted I eps πs) (show 0 < j + 1 by omega) (show j + 1 < L by omega)
      simp only [τ] at hτ0 hs ⊢; omega
    have hsL : s + 1 < πs.length := by
      have := getD_lt_getD (ks_sorted I eps πs) (show j + 1 < L - 1 by omega) (show L - 1 < L by omega)
      simp only [τ] at hτL hs ⊢; omega
    have hkeep := ks_getD_keep I eps πs (j + 1) (by omega)
    rw [← show τ (j + 1) = (ks I eps πs).getD (j + 1) 0 from rfl, ← hs] at hkeep
    unfold keep at hkeep
    rcases hkeep with h | h | h
    · omega
    · omega
    · set x := P0 I eps (πs.getD (s - 1) 0) with hx
      have hy : P0 I eps (πs.getD s 0) = p (j + 1) := (hp (j + 1) (by omega)).symm
      have hxy : p (j + 1) ≤ x := by
        rw [← hy]; exact P0_anti I eps hI (path_mono' I eps hπs _ _ (by omega) (by omega))
      have hxpos : 0 < x := lt_of_lt_of_le hpos hxy
      rw [hy, bucketIndex_pos eps x hxpos, bucketIndex_pos eps _ hpos] at h
      have hne' : kk eps x ≠ kk eps (p (j + 1)) := by
        intro he; apply h; rw [he]
      have hle := kk_mono eps h0 hpos hxy
      have hpj : x ≤ p j := by
        rw [hp j (by omega), hx]
        apply P0_anti I eps hI (path_mono' I eps hπs _ _ _ (by omega))
        have := getD_lt_getD (ks_sorted I eps πs) (show j < j + 1 by omega) (show j + 1 < L by omega)
        simp only [τ] at hs ⊢; omega
      have := kk_mono eps h0 hxpos hpj
      omega
  have hchain : ∀ d, k + d + 1 < L → 0 < p (k + d) → kk eps (p k) + d ≤ kk eps (p (k + d)) := by
    intro d
    induction d with
    | zero => intros; simp
    | succ d ih =>
      intro hd hpos
      have hpos' : 0 < p (k + d) := lt_of_lt_of_le hpos (hanti _ _ (by omega) (by omega))
      have := ih (by omega) hpos'
      have := hstep (k + d) (by omega) (by rw [show k + d + 1 = k + (d + 1) by ring]; exact hpos)
      rw [show k + (d + 1) = k + d + 1 by ring]
      omega
  -- the geometric bound
  set q : ℝ := 1 / B with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one hB0]; exact hB1
  have hqB : ∀ j : ℕ, q ^ j * B ^ j = 1 := by
    intro j; rw [← mul_pow, hq, one_div, inv_mul_cancel₀ hB0.ne', one_pow]
  set C : ℝ := B * p k * B ^ k with hC
  have hbound : ∀ j ∈ Finset.Ico k (L - 1), p j ≤ C * q ^ j := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hjB : p j = p j * B ^ j * q ^ j := by
      rw [mul_assoc, mul_comm (B ^ j), hqB, mul_one]
    by_cases hpj : p j = 0
    · rw [hpj]; exact mul_nonneg (by simp only [hC]; have := hp0 k; positivity) (pow_nonneg hq0 _)
    · have hpos : 0 < p j := lt_of_le_of_ne (hp0 j) (Ne.symm hpj)
      have hpk : 0 < p k := lt_of_lt_of_le hpos (hanti _ _ hj.1 (by omega))
      obtain ⟨d, rfl⟩ : ∃ d, j = k + d := ⟨j - k, by omega⟩
      have hch := hchain d (by omega) hpos
      obtain ⟨fj1, -⟩ := kk_facts eps (p (k + d)) h0 hpos (hp1 _)
      obtain ⟨-, fk2⟩ := kk_facts eps (p k) h0 hpk (hp1 _)
      -- p_j * B^j ≤ C
      have hmain : p (k + d) * B ^ (k + d) ≤ C := by
        have hpow : B ^ (kk eps (p k)) * B ^ (k + d) ≤ B ^ (kk eps (p (k + d))) * B ^ k := by
          rw [← pow_add, ← pow_add]
          exact pow_le_pow_right₀ hB1.le (by omega)
        have hA : 0 < B ^ (kk eps (p k)) := by positivity
        have h3 : p (k + d) * B ^ (k + d) * B ^ (kk eps (p k)) ≤ B ^ k := by
          calc p (k + d) * B ^ (k + d) * B ^ (kk eps (p k))
              = p (k + d) * (B ^ (kk eps (p k)) * B ^ (k + d)) := by ring
            _ ≤ p (k + d) * (B ^ (kk eps (p (k + d))) * B ^ k) :=
                mul_le_mul_of_nonneg_left hpow hpos.le
            _ = (p (k + d) * B ^ (kk eps (p (k + d)))) * B ^ k := by ring
            _ ≤ 1 * B ^ k := mul_le_mul_of_nonneg_right fj1 (by positivity)
            _ = B ^ k := one_mul _
        have h4 : B ^ k ≤ C * B ^ (kk eps (p k)) := by
          have : B ^ k * 1 ≤ B ^ k * (B ^ (kk eps (p k) + 1) * p k) :=
            mul_le_mul_of_nonneg_left fk2.le (by positivity)
          calc B ^ k = B ^ k * 1 := (mul_one _).symm
            _ ≤ B ^ k * (B ^ (kk eps (p k) + 1) * p k) := this
            _ = C * B ^ (kk eps (p k)) := by rw [hC, pow_succ]; ring
        have := le_trans h3 h4
        exact le_of_mul_le_mul_right this hA
      rw [hjB]
      exact mul_le_mul_of_nonneg_right hmain (pow_nonneg hq0 _)
  calc ∑ j ∈ Finset.Ico k (L - 1), p j ≤ ∑ j ∈ Finset.Ico k (L - 1), C * q ^ j :=
        Finset.sum_le_sum hbound
    _ = C * ∑ j ∈ Finset.Ico k (L - 1), q ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (q ^ k / (1 - q)) := by
        apply mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq0 hq1)
        simp only [hC]; have := hp0 k; positivity
    _ = B ^ 2 / eps * p k := by
        have h1q : 1 - q = eps / B := by
          rw [hq]; field_simp; rw [hB]; ring
        rw [h1q, hC]
        have : q ^ k * B ^ k = 1 := hqB k
        field_simp
        linear_combination (p k) * this
