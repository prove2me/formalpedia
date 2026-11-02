-- Prove2me | solution 1 for BatchTesting.PTAS.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T18:33:27.915043+00:00
-- url     : https://prove2.me/submissions/54a87cf4-5ffd-4ef0-a2ff-a9e1569c955d

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model
import Theorems.Thm_BatchTesting_PTAS_lemma_1
import Theorems.Thm_BatchTesting_PTAS_lemma_2

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

end BTSeq

open BatchTesting.PTAS

namespace BTThm2
open BTCommon BTSeq

variable {n : ℕ} (I : Instance n) (eps : ℝ)

theorem niceStep (hI : I.Standing) (h0 : 0 < eps) (h1 : eps ≤ 1) (Nprev Nstar : State I eps)
    (hP : Nprev ∈ F I eps) (hPn : IsNice I eps Nprev) (hS : Nstar ∈ F I eps) :
    Nprev + niceDelta I eps Nprev Nstar ∈ F I eps ∧
      IsNice I eps (Nprev + niceDelta I eps Nprev Nstar) := by
  have hκ := kappa_nonneg I eps hI h0 h1
  rw [mem_F] at hP hS
  constructor
  · rw [mem_F]; intro r
    have := hP r; have := hS r
    unfold niceDelta; simp only [Pi.add_apply, Pi.sub_apply]
    split_ifs <;> omega
  · set N := Nprev + niceDelta I eps Nprev Nstar with hN
    set ψb := psi (Nstar - Nprev) with hψb
    have hψ : psi N ≤ max (psi Nprev) ψb := by
      apply psi_le _ _ (le_max_of_le_left (neg_one_le_psi _))
      intro r hr
      simp only [hN, Pi.add_apply] at hr
      by_cases h : Nprev r = 0
      · rw [h, zero_add] at hr
        have : ¬ ψb < r := by
          intro hlt; apply hr; unfold niceDelta; rw [← hψb, if_pos hlt]
        exact le_max_of_le_right (by omega)
      · exact le_max_of_le_left (le_psi _ _ h)
    intro r hr
    have hPr := hP r; have hSr := hS r
    rcases le_max_iff.mp hψ with hc | hc
    · have hfull := hPn r (by omega)
      simp only [hN, Pi.add_apply]
      unfold niceDelta; simp only [Pi.sub_apply]
      split_ifs <;> omega
    · simp only [hN, Pi.add_apply]
      unfold niceDelta
      rw [← hψb, if_neg (by omega), if_neg (by omega)]
      omega

end BTThm2

open BTCommon BTSeq BTThm2 in
theorem solution {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1)
    (π : List (State I eps)) (hπ : IsPath I eps (F I eps) π) :
    ∃ π', IsPath I eps (FNice I eps) π' ∧ pathCost I eps π' ≤ (1 + eps) * pathCost I eps π := by
  have hπne : π ≠ [] := by
    intro h; have := hπ.1; rw [h] at this; simp at this
  have hL1 := lemma_1 I hI eps h0 h1 π hπ
  have hL2 := lemma_2 I hI eps h0 h1 π hπ
  set ns := niceSeq I eps π with hns
  set L := π.length with hL
  have hnsL : ns.length = L := niceSeq_length I eps π hπne
  have hLpos : 0 < L := List.length_pos_iff.mpr hπne
  have hπF : ∀ t, t < L → π.getD t 0 ∈ F I eps := by
    intro t ht
    rw [List.getD_eq_getElem _ _ ht]
    exact hπ.2.2.1 _ (List.getElem_mem _)
  -- invariants
  have hinv : ∀ t, t < L → ns.getD t 0 ∈ F I eps ∧ IsNice I eps (ns.getD t 0) := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [hns, niceSeq_zero]
      exact ⟨zero_mem_F I eps, isNice_zero I eps hI h0 h1⟩
    | succ t ih =>
      intro ht
      obtain ⟨hF, hN⟩ := ih (by omega)
      rw [hns, niceSeq_succ I eps π t ht, ← hns]
      exact niceStep I eps hI h0 h1 _ _ hF hN (hπF _ ht)
  have hmono : ∀ t, t + 1 < L → ns.getD t 0 ≤ ns.getD (t + 1) 0 := by
    intro t ht
    rw [hns, niceSeq_succ I eps π t ht, ← hns]
    exact le_add_of_nonneg_right (fun r => Nat.zero_le _)
  have hch : ns.IsChain (· ≤ ·) := isChain_of_getD I eps (fun m hm => hmono m (by omega))
  have hdom := forall2_getD I eps hL1
  -- the last state
  have hlast : ns.getLast? = some (Nall I eps) := by
    have h1' := hdom (L - 1) (by omega)
    rw [getD_last_of_getLast? I eps hπ.2.1] at h1'
    have hF := (hinv (L - 1) (by omega)).1
    have heq : ns.getD (L - 1) 0 = Nall I eps :=
      le_antisymm (fun r => (mem_F I eps).mp hF r) h1'
    rw [List.getLast?_eq_getElem?, hnsL, ← heq, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  -- cost
  have hcost : pathCost I eps ns ≤ (1 + eps) * pathCost I eps π := by
    rw [pathCost_eq_sum, pathCost_eq_sum, hnsL, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    rw [Finset.mem_range] at ht
    have hP := P0_anti I eps hI (hdom t (by omega))
    have hs := hL2 t (by omega)
    have hs0 := stepCost_nonneg I eps hI h0 (ns.getD (t + 1) 0 - ns.getD t 0)
    have hp0 := P0_nonneg I eps hI (π.getD t 0)
    calc P0 I eps (ns.getD t 0) * stepCost I eps (ns.getD (t + 1) 0 - ns.getD t 0)
        ≤ P0 I eps (π.getD t 0) * stepCost I eps (ns.getD (t + 1) 0 - ns.getD t 0) :=
          mul_le_mul_of_nonneg_right hP hs0
      _ ≤ P0 I eps (π.getD t 0) * ((1 + eps) * stepCost I eps (π.getD (t + 1) 0 - π.getD t 0)) :=
          mul_le_mul_of_nonneg_left hs hp0
      _ = _ := by ring
  -- remove repeated states
  cases hdef : ns with
  | nil => rw [hdef] at hnsL; simp at hnsL; omega
  | cons a rest =>
    rw [hdef] at hch hlast hcost
    have ha0 : a = 0 := by
      have := niceSeq_zero I eps π; rw [← hns, hdef] at this; simpa using this
    obtain ⟨t, htl, htsub, htch, htc⟩ := dedupe I eps hI h0 rest a hch
    refine ⟨a :: t, ⟨by simp [ha0], by rw [htl, hlast], ?_, htch⟩, htc.trans hcost⟩
    intro N hN
    have hNmem : N ∈ ns := by rw [hdef]; exact htsub N hN
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hNmem
    have := hinv i (by omega)
    rw [List.getD_eq_getElem _ _ hi] at this
    exact (mem_FNice I eps).mpr this
