-- Prove2me | solution 1 for BatchTesting.PTAS.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T18:31:12.601189+00:00
-- url     : https://prove2.me/submissions/0a746ccf-5856-4865-a852-172115a9dd62

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model
import Theorems.Thm_BatchTesting_PTAS_theorem_2
import Theorems.Thm_BatchTesting_PTAS_lemma_3
import Theorems.Thm_BatchTesting_PTAS_lemma_4
import Theorems.Thm_BatchTesting_PTAS_lemma_5
import Theorems.Thm_BatchTesting_PTAS_property_A
import Theorems.Thm_BatchTesting_PTAS_property_B
import Theorems.Thm_BatchTesting_PTAS_property_C

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

end BTSeq

open BatchTesting.PTAS

open BTCommon BTSeq in
theorem solution {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1) :
    (∀ π, IsPath I eps (FGreat I eps) π → IsPath I eps (F I eps) π) ∧
      ∀ π, IsPath I eps (F I eps) π →
        ∃ π', IsPath I eps (FGreat I eps) π' ∧ pathCost I eps π' ≤ K eps * pathCost I eps π := by
  refine ⟨fun π hπ => IsPath.mono I eps (FGreat_sub_F I eps) hπ, ?_⟩
  intro π hπ
  -- an optimal nice-looking path
  obtain ⟨π1, hπ1, -⟩ := theorem_2 I hI eps h0 h1 π hπ
  obtain ⟨πs, hopt⟩ := exists_optPath I eps (FNice I eps) ⟨π1, hπ1⟩
  have hπs := hopt.1
  have hπsF : IsPath I eps (F I eps) πs := IsPath.mono I eps (FNice_sub_F I eps) hπs
  have hL3 := lemma_3 I hI eps h0 h1 πs hopt π hπ
  have hL4 := lemma_4 I hI eps h0 h1 πs hπsF
  have hL5 := lemma_5 I hI eps h0 h1 πs hπs
  have hA := property_A I hI eps h0 h1 πs hπs
  have hB := property_B I hI eps h0 h1 πs hπs
  have hC := property_C I hI eps h0 h1 πs hπs
  set b := bucketed I eps πs with hb
  set g := greatSeq I eps b with hg
  have hπsne : πs ≠ [] := by
    intro h; have := hπs.1; rw [h] at this; simp at this
  have hbne : b ≠ [] := bucketed_ne_nil I eps πs hπsne
  set L := b.length with hL
  have hgL : g.length = L := greatSeq_length I eps b hbne
  have hb0 : b.getD 0 0 = 0 := by
    have h1' := bucketed_head I eps πs hπsne
    rw [← hb] at h1'
    have e2 : πs.getD 0 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, hπs.1]; rfl
    rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, h1', Option.getD_some]; exact e2
  have hblast : b.getLast? = some (Nall I eps) := by
    rw [hb, bucketed_getLast I eps πs hπsne]; exact hπs.2.1
  -- monotonicity of the great sequence
  have hmono : ∀ m, m + 1 < L → g.getD m 0 ≤ g.getD (m + 1) 0 := by
    intro m hm r
    rw [hg, greatSeq_succ I eps b m hm]
    exact (greatDeltaZ_eq I eps _ _ r (hL5 m hm r)).2
  have hgch : g.IsChain (· ≤ ·) := isChain_of_getD I eps (fun m hm => hmono m (by omega))
  -- the great sequence ends at N^(all)
  have hglast : g.getLast? = some (Nall I eps) := by
    have hB' : (b.getD (L - 1) 0) ≤ g.getD (L - 1) 0 := by
      have hlt : L - 1 < L := by
        have := List.length_pos_iff.mpr hbne; omega
      have := List.forall₂_iff_get.mp hB
      have h2 := this.2 (L - 1) hlt (by omega)
      simp only [List.get_eq_getElem] at h2
      rwa [List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ (by omega)]
    rw [getD_last_of_getLast? I eps hblast] at hB'
    have hgF : g.getD (L - 1) 0 ∈ F I eps := by
      apply FGreat_sub_F I eps
      apply hA
      rw [List.getD_eq_getElem _ _ (by have := List.length_pos_iff.mpr hbne; omega)]
      exact List.getElem_mem _
    have heq : g.getD (L - 1) 0 = Nall I eps := by
      apply le_antisymm _ hB'
      intro r; exact (mem_F I eps).mp hgF r
    rw [List.getLast?_eq_getElem?, hgL, ← heq, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by have := List.length_pos_iff.mpr hbne; omega)]
    rfl
  -- the cost estimate
  have hcost : pathCost I eps g ≤ K eps * pathCost I eps π := by
    set β' := I.beta / cmin I with hβ'
    have hβ0 : 0 ≤ β' := div_nonneg hI.2.2.2 (cmin_pos I hI).le
    let P : ℕ → ℝ := fun m => P0 I eps (b.getD m 0)
    let Q : ℕ → ℝ := fun m => P0 I eps (g.getD m 0)
    let D : ℕ → ℝ := fun j => ∑ r, ((((b.getD (j + 1) 0 - b.getD j 0) r : ℕ)) : ℝ) *
      (1 + eps) ^ (r : ℕ)
    let E : ℕ → ℝ := fun m => ∑ r, (greatDeltaZ I eps (g.getD m 0) (b.getD (m + 1) 0) r : ℝ) *
      (1 + eps) ^ (r : ℕ)
    have hP0 : ∀ m, 0 ≤ P m := fun m => P0_nonneg I eps hI _
    have hD0 : ∀ j, 0 ≤ D j := fun j => Finset.sum_nonneg fun r _ => by positivity
    have hcb : pathCost I eps b = ∑ m ∈ Finset.range (L - 1), P m * (β' + D m) := by
      rw [pathCost_eq_sum]; rfl
    have hcg : pathCost I eps g = ∑ m ∈ Finset.range (L - 1), Q m * (β' + E m) := by
      rw [pathCost_eq_sum, hgL]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_range] at hm
      have hm' : m + 1 < L := by omega
      simp only [Q, E]
      congr 1
      unfold stepCost
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      congr 1
      have := (greatDeltaZ_eq I eps (g.getD m 0) (b.getD (m + 1) 0) r (hL5 m hm' r)).1
      rw [hg, greatSeq_succ I eps b m hm', ← hg, ← this]
      push_cast; rfl
    have hE0 : ∀ m, m + 1 < L → 0 ≤ E m := by
      intro m hm
      exact Finset.sum_nonneg fun r _ => mul_nonneg (by exact_mod_cast hL5 m hm r) (by positivity)
    have hQP : ∀ m, m + 1 < L → Q m ≤ P m := by
      intro m hm
      apply P0_anti I eps hI
      have := List.forall₂_iff_get.mp hB
      have h2 := this.2 m (by omega) (by omega)
      simp only [List.get_eq_getElem] at h2
      rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    -- Step 1: termwise bound
    have step1 : pathCost I eps g ≤ ∑ m ∈ Finset.range (L - 1),
        P m * (β' + (1 + 3 * eps) * D m + 2 * eps ^ 2 * ∑ j ∈ Finset.range m, D j) := by
      rw [hcg]
      apply Finset.sum_le_sum
      intro m hm
      rw [Finset.mem_range] at hm
      have hm' : m + 1 < L := by omega
      have hCm := hC m hm'
      calc Q m * (β' + E m) ≤ P m * (β' + E m) :=
            mul_le_mul_of_nonneg_right (hQP m hm') (by linarith [hE0 m hm'])
        _ ≤ P m * (β' + (1 + 3 * eps) * D m + 2 * eps ^ 2 * ∑ j ∈ Finset.range m, D j) := by
            apply mul_le_mul_of_nonneg_left _ (hP0 m)
            have : E m ≤ (1 + 3 * eps) * D m + 2 * eps ^ 2 * ∑ j ∈ Finset.range m, D j := hCm
            linarith
    -- Step 2: exchange the double sum and apply Lemma 4
    have step2 : ∑ m ∈ Finset.range (L - 1), P m * ∑ j ∈ Finset.range m, D j ≤
        ∑ j ∈ Finset.range (L - 1), D j * ((1 + eps) ^ 2 / eps * P j) := by
      have hswap : ∑ m ∈ Finset.range (L - 1), P m * ∑ j ∈ Finset.range m, D j =
          ∑ j ∈ Finset.range (L - 1), D j * ∑ m ∈ Finset.Ico (j + 1) (L - 1), P m := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm' (s' := fun j => Finset.Ico (j + 1) (L - 1))
          (t' := Finset.range (L - 1))]
        · apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro m _; ring
        · intro m j
          simp only [Finset.mem_range, Finset.mem_Ico]
          omega
      rw [hswap]
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range] at hj
      apply mul_le_mul_of_nonneg_left _ (hD0 j)
      calc ∑ m ∈ Finset.Ico (j + 1) (L - 1), P m ≤ ∑ m ∈ Finset.Ico j (L - 1), P m := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx; simp only [Finset.mem_Ico] at hx ⊢; omega
            · intros; exact hP0 _
        _ ≤ (1 + eps) ^ 2 / eps * P j := hL4 j (by omega)
    -- Step 3: combine
    have hb' : pathCost I eps b ≤ (1 + eps) ^ 2 * pathCost I eps π := hL3
    have hcb0 : 0 ≤ pathCost I eps b := by
      rw [hcb]; exact Finset.sum_nonneg fun m _ => mul_nonneg (hP0 m) (by linarith [hD0 m])
    have step3 : ∑ m ∈ Finset.range (L - 1),
        P m * (β' + (1 + 3 * eps) * D m + 2 * eps ^ 2 * ∑ j ∈ Finset.range m, D j) ≤
        ((1 + 3 * eps) + 2 * eps * (1 + eps) ^ 2) * pathCost I eps b := by
      have e1 : ∑ m ∈ Finset.range (L - 1),
          P m * (β' + (1 + 3 * eps) * D m + 2 * eps ^ 2 * ∑ j ∈ Finset.range m, D j) =
          ∑ m ∈ Finset.range (L - 1), P m * (β' + (1 + 3 * eps) * D m) +
            2 * eps ^ 2 * ∑ m ∈ Finset.range (L - 1), P m * ∑ j ∈ Finset.range m, D j := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro m _; ring
      have e2 : ∑ j ∈ Finset.range (L - 1), D j * ((1 + eps) ^ 2 / eps * P j) =
          (1 + eps) ^ 2 / eps * ∑ j ∈ Finset.range (L - 1), P j * D j := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      have e3 : ∑ m ∈ Finset.range (L - 1), P m * (β' + (1 + 3 * eps) * D m) ≤
          (1 + 3 * eps) * pathCost I eps b := by
        rw [hcb, Finset.mul_sum]
        apply Finset.sum_le_sum; intro m _
        have := hP0 m
        have : 0 ≤ P m * β' := mul_nonneg this hβ0
        nlinarith
      have e4 : ∑ j ∈ Finset.range (L - 1), P j * D j ≤ pathCost I eps b := by
        rw [hcb]
        apply Finset.sum_le_sum; intro m _
        have := mul_nonneg (hP0 m) hβ0
        nlinarith
      rw [e1]
      have h2e : 2 * eps ^ 2 * ((1 + eps) ^ 2 / eps) = 2 * eps * (1 + eps) ^ 2 := by
        field_simp
      have hk0 : 0 ≤ 2 * eps ^ 2 := by positivity
      have hk1 : 0 ≤ (1 + eps) ^ 2 / eps := by positivity
      calc ∑ m ∈ Finset.range (L - 1), P m * (β' + (1 + 3 * eps) * D m) +
            2 * eps ^ 2 * ∑ m ∈ Finset.range (L - 1), P m * ∑ j ∈ Finset.range m, D j
          ≤ (1 + 3 * eps) * pathCost I eps b +
            2 * eps ^ 2 * ((1 + eps) ^ 2 / eps * ∑ j ∈ Finset.range (L - 1), P j * D j) := by
            rw [← e2]
            exact add_le_add e3 (mul_le_mul_of_nonneg_left step2 hk0)
        _ = (1 + 3 * eps) * pathCost I eps b +
            2 * eps * (1 + eps) ^ 2 * ∑ j ∈ Finset.range (L - 1), P j * D j := by
            rw [← mul_assoc, h2e]
        _ ≤ (1 + 3 * eps) * pathCost I eps b + 2 * eps * (1 + eps) ^ 2 * pathCost I eps b := by
            have : 0 ≤ 2 * eps * (1 + eps) ^ 2 := by positivity
            nlinarith
        _ = _ := by ring
    have hc0 : 0 ≤ (1 + 3 * eps) + 2 * eps * (1 + eps) ^ 2 := by positivity
    calc pathCost I eps g ≤ ((1 + 3 * eps) + 2 * eps * (1 + eps) ^ 2) * pathCost I eps b :=
          step1.trans step3
      _ ≤ ((1 + 3 * eps) + 2 * eps * (1 + eps) ^ 2) * ((1 + eps) ^ 2 * pathCost I eps π) :=
          mul_le_mul_of_nonneg_left hb' hc0
      _ = K eps * pathCost I eps π := by unfold K; ring
  -- remove repeated states
  cases hgdef : g with
  | nil => rw [hgdef] at hgL; exact absurd hgL.symm (by simpa [hL] using hbne)
  | cons a rest =>
    rw [hgdef] at hgch hglast hcost
    have ha0 : a = 0 := by
      have := greatSeq_zero I eps b; rw [← hg, hgdef] at this; simpa using this
    obtain ⟨t, htl, htsub, htch, htc⟩ := dedupe I eps hI h0 rest a hgch
    refine ⟨a :: t, ⟨by simp [ha0], by rw [htl, hglast], ?_, htch⟩, htc.trans hcost⟩
    intro N hN
    apply hA
    rw [hgdef]
    exact htsub N hN
