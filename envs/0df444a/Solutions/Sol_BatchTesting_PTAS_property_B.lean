-- Prove2me | solution 1 for BatchTesting.PTAS.property_B
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T18:49:50.370469+00:00
-- url     : https://prove2.me/submissions/d92c09ce-dd39-4b01-af5f-c269027f2769

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

namespace BTGreat
open BTCommon BTSeq BTBucket

/-! ### `P_2` -/

theorem P2_eq (x : ℝ) : P2 x = (2 : ℝ) ^ ⌊Real.logb 2 x⌋ := rfl

theorem P2_pos (x : ℝ) : 0 < P2 x := by unfold P2; positivity

theorem P2_le (x : ℝ) (hx : 0 < x) : P2 x ≤ x := by
  unfold P2
  calc (2 : ℝ) ^ ⌊Real.logb 2 x⌋ = (2 : ℝ) ^ ((⌊Real.logb 2 x⌋ : ℤ) : ℝ) := (Real.rpow_intCast _ _).symm
    _ ≤ (2 : ℝ) ^ Real.logb 2 x := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.floor_le _)
    _ = x := Real.rpow_logb (by norm_num) (by norm_num) hx

theorem lt_two_P2 (x : ℝ) (hx : 0 < x) : x < 2 * P2 x := by
  unfold P2
  calc x = (2 : ℝ) ^ Real.logb 2 x := (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
    _ < (2 : ℝ) ^ (((⌊Real.logb 2 x⌋ : ℤ) : ℝ) + 1) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (Int.lt_floor_add_one _)
    _ = 2 * (2 : ℝ) ^ ⌊Real.logb 2 x⌋ := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_intCast]; ring

/-- `P_2` is monotone, and a larger value is a power-of-two multiple of a smaller one. -/
theorem P2_mul (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    ∃ e : ℕ, P2 y = P2 x * 2 ^ e := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hle : ⌊Real.logb 2 x⌋ ≤ ⌊Real.logb 2 y⌋ :=
    Int.floor_mono (Real.logb_le_logb_of_le (by norm_num) hx hxy)
  refine ⟨(⌊Real.logb 2 y⌋ - ⌊Real.logb 2 x⌋).toNat, ?_⟩
  unfold P2
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num), Int.toNat_of_nonneg (by omega)]
  congr 1; ring

variable {n : ℕ} (I : Instance n) (eps : ℝ)

/-- The weighted size `∑_r N_r (1+ε)^r` (all coordinates). -/
noncomputable def wsum (N : State I eps) : ℝ := ∑ r, (N r : ℝ) * (1 + eps) ^ (r : ℕ)

theorem rhoSum_eq (N : State I eps) :
    (∑ r ∈ Finset.univ.filter (fun r : Fin (R I eps + 1) => (r : ℤ) ≤ psi N),
      (N r : ℝ) * (1 + eps) ^ (r : ℕ)) = wsum I eps N := by
  unfold wsum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs with h
  · rfl
  · rw [psi_eq_zero_of_lt N r (by omega)]; simp

theorem rhoOf_eq (N : State I eps) :
    rhoOf I eps N = ⌈Real.logb (1 + eps) (wsum I eps N)⌉ := by
  unfold rhoOf; rw [rhoSum_eq]

theorem wsum_mono (h0 : 0 < eps) {N M : State I eps} (h : N ≤ M) : wsum I eps N ≤ wsum I eps M := by
  unfold wsum
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast h r

theorem one_le_wsum (h0 : 0 < eps) {N : State I eps} (h : N ≠ 0) : 1 ≤ wsum I eps N := by
  obtain ⟨r, hr⟩ : ∃ r, N r ≠ 0 := by
    by_contra hc; push_neg at hc; exact h (funext hc)
  unfold wsum
  calc (1 : ℝ) ≤ (N r : ℝ) * (1 + eps) ^ (r : ℕ) := by
        have : (1 : ℝ) ≤ N r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
        have : (1 : ℝ) ≤ (1 + eps) ^ (r : ℕ) := one_le_pow₀ (by linarith)
        nlinarith
    _ ≤ _ := Finset.single_le_sum (f := fun r => (N r : ℝ) * (1 + eps) ^ (r : ℕ))
        (fun r _ => by positivity) (Finset.mem_univ r)

theorem rhoOf_nonneg (h0 : 0 < eps) {N : State I eps} (h : N ≠ 0) : 0 ≤ rhoOf I eps N := by
  rw [rhoOf_eq]
  apply Int.ceil_nonneg
  exact Real.logb_nonneg (by linarith) (one_le_wsum I eps h0 h)

/-- `(1+ε)^{ρ}` sandwiches the weighted size (eq. (4)). -/
theorem pow_rho_bounds (h0 : 0 < eps) {N : State I eps} (h : N ≠ 0) :
    wsum I eps N ≤ (1 + eps) ^ rhoOf I eps N ∧
      (1 + eps) ^ rhoOf I eps N < (1 + eps) * wsum I eps N := by
  have hb : (1 : ℝ) < 1 + eps := by linarith
  have hb0 : (0 : ℝ) < 1 + eps := by linarith
  have hS := one_le_wsum I eps h0 h
  have hS0 : 0 < wsum I eps N := by linarith
  have hx := Real.rpow_logb hb0 hb.ne' hS0
  rw [rhoOf_eq, ← Real.rpow_intCast]
  constructor
  · calc wsum I eps N = (1 + eps) ^ Real.logb (1 + eps) (wsum I eps N) := hx.symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hb.le (Int.le_ceil _)
  · calc (1 + eps) ^ ((⌈Real.logb (1 + eps) (wsum I eps N)⌉ : ℤ) : ℝ)
        < (1 + eps) ^ (Real.logb (1 + eps) (wsum I eps N) + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt hb (Int.ceil_lt_add_one _)
      _ = (1 + eps) * wsum I eps N := by
          rw [Real.rpow_add hb0, Real.rpow_one, hx]; ring

theorem rhoOf_mono (h0 : 0 < eps) {N M : State I eps} (hN : N ≠ 0) (h : N ≤ M) :
    rhoOf I eps N ≤ rhoOf I eps M := by
  rw [rhoOf_eq, rhoOf_eq]
  apply Int.ceil_mono
  exact Real.logb_le_logb_of_le (by linarith) (by linarith [one_le_wsum I eps h0 hN])
    (wsum_mono I eps h0 h)

/-- The unit `(ε²/κ) P_2[(1+ε)^{ρ}]`. -/
noncomputable def unit (N : State I eps) : ℝ :=
  (eps ^ 2 / (kappa n eps : ℝ)) * P2 ((1 + eps) ^ rhoOf I eps N)

theorem unit_pos (h0 : 0 < eps) (hκ : 0 < kappa n eps) (N : State I eps) : 0 < unit I eps N := by
  unfold unit
  have : (0 : ℝ) < kappa n eps := by exact_mod_cast hκ
  exact mul_pos (div_pos (by positivity) this) (P2_pos _)

theorem unit_mul (h0 : 0 < eps) {N M : State I eps} (hN : N ≠ 0) (h : N ≤ M) :
    ∃ e : ℕ, unit I eps M = unit I eps N * 2 ^ e := by
  have hb0 : (0 : ℝ) < 1 + eps := by linarith
  have hle : (1 + eps) ^ rhoOf I eps N ≤ (1 + eps) ^ rhoOf I eps M :=
    zpow_le_zpow_right₀ (by linarith) (rhoOf_mono I eps h0 hN h)
  obtain ⟨e, he⟩ := P2_mul _ _ (zpow_pos hb0 _) hle
  refine ⟨e, ?_⟩
  unfold unit; rw [he]; ring

theorem muOf_eq (N : State I eps) (r : Fin (R I eps + 1)) :
    muOf I eps N r = ⌈(N r : ℝ) * (1 + eps) ^ (r : ℕ) / unit I eps N⌉₊ := rfl

theorem greatTarget_eq (N : State I eps) (r : Fin (R I eps + 1)) :
    greatTarget I eps N r =
      min ⌊(muOf I eps N r : ℝ) * unit I eps N / (1 + eps) ^ (r : ℕ)⌋₊ (cls I eps r).card := by
  unfold greatTarget unit; congr 3; ring

/-- `µ u ≥ N_r (1+ε)^r` and `µ u < N_r (1+ε)^r + u`. -/
theorem mu_bounds (h0 : 0 < eps) (hκ : 0 < kappa n eps) (N : State I eps) (r : Fin (R I eps + 1)) :
    (N r : ℝ) * (1 + eps) ^ (r : ℕ) ≤ (muOf I eps N r : ℝ) * unit I eps N ∧
      (muOf I eps N r : ℝ) * unit I eps N < (N r : ℝ) * (1 + eps) ^ (r : ℕ) + unit I eps N := by
  have hu := unit_pos I eps h0 hκ N
  rw [muOf_eq]
  have hx : 0 ≤ (N r : ℝ) * (1 + eps) ^ (r : ℕ) / unit I eps N := by positivity
  constructor
  · have := Nat.le_ceil ((N r : ℝ) * (1 + eps) ^ (r : ℕ) / unit I eps N)
    rwa [div_le_iff₀ hu] at this
  · have := Nat.ceil_lt_add_one hx
    rw [div_add_one hu.ne', lt_div_iff₀ hu] at this
    linarith

theorem target_ge (h0 : 0 < eps) (hκ : 0 < kappa n eps) (N : State I eps) (hN : N ∈ F I eps)
    (r : Fin (R I eps + 1)) : N r ≤ greatTarget I eps N r := by
  rw [greatTarget_eq]
  apply le_min _ ((mem_F I eps).mp hN r)
  apply Nat.le_floor
  rw [le_div_iff₀ (by positivity)]
  exact (mu_bounds I eps h0 hκ N r).1

theorem target_mul_le (h0 : 0 < eps) (hκ : 0 < kappa n eps) (N : State I eps)
    (r : Fin (R I eps + 1)) :
    (greatTarget I eps N r : ℝ) * (1 + eps) ^ (r : ℕ) ≤ (muOf I eps N r : ℝ) * unit I eps N := by
  rw [greatTarget_eq]
  have hw : (0 : ℝ) < (1 + eps) ^ (r : ℕ) := by positivity
  have h1 : ((min ⌊(muOf I eps N r : ℝ) * unit I eps N / (1 + eps) ^ (r : ℕ)⌋₊
      (cls I eps r).card : ℕ) : ℝ) ≤ (muOf I eps N r : ℝ) * unit I eps N / (1 + eps) ^ (r : ℕ) := by
    calc ((min ⌊(muOf I eps N r : ℝ) * unit I eps N / (1 + eps) ^ (r : ℕ)⌋₊
          (cls I eps r).card : ℕ) : ℝ)
        ≤ (⌊(muOf I eps N r : ℝ) * unit I eps N / (1 + eps) ^ (r : ℕ)⌋₊ : ℝ) := by
          exact_mod_cast min_le_left _ _
      _ ≤ _ := Nat.floor_le (by have := unit_pos I eps h0 hκ N; positivity)
  rwa [le_div_iff₀ hw] at h1

/-- The middle-class target is monotone along a monotone sequence of states. -/
theorem target_mono (h0 : 0 < eps) (hκ : 0 < kappa n eps) {N M : State I eps} (hN : N ≠ 0)
    (h : N ≤ M) (r : Fin (R I eps + 1)) : greatTarget I eps N r ≤ greatTarget I eps M r := by
  obtain ⟨e, he⟩ := unit_mul I eps h0 hN h
  have hu := unit_pos I eps h0 hκ N
  have hmu : (muOf I eps N r : ℝ) * unit I eps N ≤ (muOf I eps M r : ℝ) * unit I eps M := by
    have hc : muOf I eps N r ≤ muOf I eps M r * 2 ^ e := by
      rw [muOf_eq]
      apply Nat.ceil_le.mpr
      rw [div_le_iff₀ hu]
      have h1 := (mu_bounds I eps h0 hκ M r).1
      have h2 : (N r : ℝ) * (1 + eps) ^ (r : ℕ) ≤ (M r : ℝ) * (1 + eps) ^ (r : ℕ) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h r) (by positivity)
      rw [he] at h1
      push_cast
      nlinarith
    calc (muOf I eps N r : ℝ) * unit I eps N ≤ ((muOf I eps M r * 2 ^ e : ℕ) : ℝ) * unit I eps N :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hu.le
      _ = (muOf I eps M r : ℝ) * unit I eps M := by rw [he]; push_cast; ring
  rw [greatTarget_eq, greatTarget_eq]
  apply min_le_min_right
  apply Nat.floor_le_floor
  exact div_le_div_of_nonneg_right hmu (by positivity)

theorem psi_mono {m : ℕ} {N M : Fin m → ℕ} (h : N ≤ M) : psi N ≤ psi M := by
  apply psi_le _ _ (neg_one_le_psi _)
  intro r hr
  apply le_psi
  have : N r ≤ M r := h r
  omega

end BTGreat

open BatchTesting.PTAS

namespace BTGreatSeq
open BTCommon BTSeq BTBucket BTGreat

variable {n : ℕ} (I : Instance n) (eps : ℝ)

theorem path_lt {G : Finset (State I eps)} {π : List (State I eps)} (hπ : IsPath I eps G π)
    (a b : ℕ) (hab : a < b) (hb : b < π.length) : π.getD a 0 ≠ π.getD b 0 := by
  have h1 : π.IsChain (fun N M : State I eps => N < M) :=
    hπ.2.2.2.imp (fun a b h => lt_of_le_of_ne h.1 h.2)
  have h2 : π.Pairwise (fun N M : State I eps => N < M) := List.isChain_iff_pairwise.mp h1
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hb]
  exact (List.pairwise_iff_getElem.mp h2 a b (by omega) hb hab).ne

/-- Facts about the bucketed subsequence of a nice-looking path. -/
structure BFacts (πs : List (State I eps)) : Prop where
  len_pos : 0 < (bucketed I eps πs).length
  first : (bucketed I eps πs).getD 0 0 = 0
  nice : ∀ m, m < (bucketed I eps πs).length → (bucketed I eps πs).getD m 0 ∈ FNice I eps
  mono : ∀ i j, i ≤ j → j < (bucketed I eps πs).length →
    (bucketed I eps πs).getD i 0 ≤ (bucketed I eps πs).getD j 0
  ne_zero : ∀ m, 1 ≤ m → m < (bucketed I eps πs).length → (bucketed I eps πs).getD m 0 ≠ 0

theorem bfacts (πs : List (State I eps)) (hπs : IsPath I eps (FNice I eps) πs) :
    BFacts I eps πs := by
  have hne := path_ne_nil I eps hπs
  have hLpos := ks_length_pos I eps πs hne
  have hτ : ∀ m, m < (bucketed I eps πs).length →
      (bucketed I eps πs).getD m 0 = πs.getD ((ks I eps πs).getD m 0) 0 := by
    intro m hm; rw [bucketed_length] at hm; exact bucketed_getD I eps πs m hm
  have hlen := bucketed_length I eps πs
  refine ⟨by rw [hlen]; exact hLpos, ?_, ?_, ?_, ?_⟩
  · rw [hτ 0 (by rw [hlen]; exact hLpos), ks_first I eps πs hne, path_getD_zero I eps hπs]
  · intro m hm
    rw [hτ m hm]
    exact path_getD_mem I eps hπs _ (ks_getD_lt I eps πs m (by rw [← hlen]; exact hm))
  · intro i j hij hj
    rw [hτ i (by omega), hτ j hj]
    rw [hlen] at hj
    exact path_mono' I eps hπs _ _ (getD_le_getD (ks_sorted I eps πs) hij hj)
      (ks_getD_lt I eps πs j hj)
  · intro m hm1 hm
    rw [hτ m hm]
    rw [hlen] at hm
    have h0 : (ks I eps πs).getD 0 0 < (ks I eps πs).getD m 0 :=
      getD_lt_getD (ks_sorted I eps πs) (by omega) hm
    rw [ks_first I eps πs hne] at h0
    have := path_lt I eps hπs 0 _ h0 (ks_getD_lt I eps πs m hm)
    rw [path_getD_zero I eps hπs] at this
    exact fun h => this h.symm

/-- Invariants of the §4.5 sequence. -/
theorem gfacts (h0 : 0 < eps) (hκ0 : 0 ≤ kappa n eps) (πs : List (State I eps)) (hπs : IsPath I eps (FNice I eps) πs) :
    ∀ m, m < (bucketed I eps πs).length →
      (greatSeq I eps (bucketed I eps πs)).getD m 0 ∈ F I eps ∧
      ∀ r : Fin (R I eps + 1), psi ((bucketed I eps πs).getD m 0) < r →
        (greatSeq I eps (bucketed I eps πs)).getD m 0 r = 0 := by
  have hB := bfacts I eps πs hπs
  intro m
  induction m with
  | zero =>
    intro _
    rw [greatSeq_zero]
    exact ⟨zero_mem_F I eps, fun r _ => rfl⟩
  | succ m ih =>
    intro hm
    obtain ⟨hF, hz⟩ := ih (by omega)
    rw [greatSeq_succ I eps _ m hm]
    have hψ : psi ((bucketed I eps πs).getD m 0) ≤ psi ((bucketed I eps πs).getD (m + 1) 0) :=
      psi_mono (hB.mono m (m + 1) (by omega) hm)
    constructor
    · rw [mem_F]; intro r
      have := (mem_F I eps).mp hF r
      unfold greatNext
      split_ifs
      · exact le_rfl
      · rw [greatTarget_eq]; exact min_le_right _ _
      · exact this
    · intro r hr
      unfold greatNext
      rw [if_neg (by omega), if_neg (by omega)]
      exact hz r (by omega)

theorem greatNext_low (Nprev Nd : State I eps) (r : Fin (R I eps + 1))
    (h : (r : ℤ) ≤ psi Nd - kappa n eps) : greatNext I eps Nprev Nd r = (cls I eps r).card := by
  unfold greatNext; rw [if_pos h]

theorem greatNext_mid (Nprev Nd : State I eps) (r : Fin (R I eps + 1))
    (h1 : psi Nd - kappa n eps < (r : ℤ)) (h2 : (r : ℤ) ≤ psi Nd) :
    greatNext I eps Nprev Nd r = greatTarget I eps Nd r := by
  unfold greatNext; rw [if_neg (by omega), if_pos h2]

/-- Property B. -/
theorem propB (h0 : 0 < eps) (πs : List (State I eps)) (hπs : IsPath I eps (FNice I eps) πs) :
    ∀ m, m < (bucketed I eps πs).length →
      (bucketed I eps πs).getD m 0 ≤ (greatSeq I eps (bucketed I eps πs)).getD m 0 := by
  have hB := bfacts I eps πs hπs
  intro m hm r
  cases m with
  | zero => rw [hB.first, greatSeq_zero]
  | succ m =>
    rw [greatSeq_succ I eps _ m hm]
    set Nd := (bucketed I eps πs).getD (m + 1) 0
    have hNdF : Nd ∈ F I eps := FNice_sub_F I eps (hB.nice _ hm)
    have hcard := (mem_F I eps).mp hNdF r
    unfold greatNext
    split_ifs with h1 h2
    · exact hcard
    · have hκ : 0 < kappa n eps := by omega
      exact target_ge I eps h0 hκ Nd hNdF r
    · rw [psi_eq_zero_of_lt Nd r (by omega)]; exact Nat.zero_le _

/-- Lemma 5. -/
theorem lemma5 (h0 : 0 < eps) (hκ0 : 0 ≤ kappa n eps) (πs : List (State I eps))
    (hπs : IsPath I eps (FNice I eps) πs) :
    ∀ m, m + 1 < (bucketed I eps πs).length → ∀ r,
      0 ≤ greatDeltaZ I eps ((greatSeq I eps (bucketed I eps πs)).getD m 0)
        ((bucketed I eps πs).getD (m + 1) 0) r := by
  have hB := bfacts I eps πs hπs
  intro m hm r
  obtain ⟨hF, hz⟩ := gfacts I eps h0 hκ0 πs hπs m (by omega)
  have hψ : psi ((bucketed I eps πs).getD m 0) ≤ psi ((bucketed I eps πs).getD (m + 1) 0) :=
    psi_mono (hB.mono m (m + 1) (by omega) hm)
  have hcard : (greatSeq I eps (bucketed I eps πs)).getD m 0 r ≤ (cls I eps r).card :=
    (mem_F I eps).mp hF r
  unfold greatDeltaZ
  split_ifs with h1 h2
  · omega
  · have hκ : 0 < kappa n eps := by omega
    by_cases hr : psi ((bucketed I eps πs).getD m 0) < r
    · rw [hz r hr]; simp
    · rcases m with _ | m
      · rw [greatSeq_zero]; simp
      · have hmid : (greatSeq I eps (bucketed I eps πs)).getD (m + 1) 0 r =
            greatTarget I eps ((bucketed I eps πs).getD (m + 1) 0) r := by
          rw [greatSeq_succ I eps _ m (by omega)]
          exact greatNext_mid I eps _ _ r (by omega) (by omega)
        rw [hmid]
        have := target_mono I eps h0 hκ (hB.ne_zero (m + 1) (by omega) (by omega))
          (hB.mono (m + 1) (m + 1 + 1) (by omega) hm) r
        omega
  · exact le_rfl

end BTGreatSeq

open BatchTesting.PTAS

open BTCommon BTSeq BTBucket BTGreat BTGreatSeq in
theorem solution {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1)
    (πs : List (State I eps)) (hπs : IsPath I eps (FNice I eps) πs) :
    List.Forall₂ (fun Nd N => Nd ≤ N) (bucketed I eps πs) (greatSeq I eps (bucketed I eps πs)) := by
  have hB := bfacts I eps πs hπs
  have hne : bucketed I eps πs ≠ [] := by
    intro h; have := hB.len_pos; rw [h] at this; simp at this
  exact forall2_of_getD I eps (greatSeq_length I eps _ hne).symm (propB I eps h0 πs hπs)
