-- Prove2me | solution 1 for BatchTesting.PTAS.greedy_within_class
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T18:20:52.660198+00:00
-- url     : https://prove2.me/submissions/76fc6fee-5c8d-4944-9acc-f51725452e1a

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

end BTCommon

open BatchTesting.PTAS

namespace BTGreedy
open BTCommon

variable {n : ℕ} (I : Instance n) (eps : ℝ)

/-- Per-class counts of a set of variables. -/
noncomputable def cnt (U : Finset (Fin n)) : State I eps :=
  fun r => (U.filter (fun i => classIdx I eps i = r)).card

theorem filter_classIdx_eq (U : Finset (Fin n)) (r : Fin (R I eps + 1)) :
    U.filter (fun i => classIdx I eps i = r) = U.filter (fun i => classOf I eps i = (r : ℕ)) := by
  ext i; simp [classIdx_eq_iff]

theorem filter_subset_cls (U : Finset (Fin n)) (r : Fin (R I eps + 1)) :
    U.filter (fun i => classIdx I eps i = r) ⊆ cls I eps r := by
  intro i hi
  rw [filter_classIdx_eq] at hi
  exact (mem_cls I eps).mpr (Finset.mem_filter.mp hi).2

theorem cnt_mem_F (U : Finset (Fin n)) : cnt I eps U ∈ F I eps := by
  rw [mem_F]; intro r
  exact Finset.card_le_card (filter_subset_cls I eps U r)

theorem cnt_univ : cnt I eps Finset.univ = Nall I eps := by
  funext r
  simp only [cnt, Nall]
  congr 1
  ext i; simp [classIdx_eq_iff, mem_cls]

theorem cnt_empty : cnt I eps ∅ = 0 := by
  funext r; simp [cnt]

/-- Within one class, the `k` smallest-probability variables have the smallest product. -/
theorem prod_rank_le (hI : I.Standing) (r k : ℕ) :
    ∀ m (A : Finset (Fin n)), A ⊆ cls I eps r → A.card = k →
      (A \ (cls I eps r).filter (fun i => rank I eps i < k)).card = m →
      ∏ i ∈ (cls I eps r).filter (fun i => rank I eps i < k), I.p i ≤ ∏ i ∈ A, I.p i := by
  intro m
  induction m with
  | zero =>
    intro A hA hk hm
    have hsub : A ⊆ (cls I eps r).filter (fun i => rank I eps i < k) := by
      rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hm; exact hm
    have hcardT : ((cls I eps r).filter (fun i => rank I eps i < k)).card = k := by
      rw [card_filter_rank, min_eq_left]; rw [← hk]; exact Finset.card_le_card hA
    have : A = (cls I eps r).filter (fun i => rank I eps i < k) :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcardT, hk])
    rw [this]
  | succ m ih =>
    intro A hA hk hm
    set T := (cls I eps r).filter (fun i => rank I eps i < k) with hT
    have hcardT : T.card = k := by
      rw [hT, card_filter_rank, min_eq_left]; rw [← hk]; exact Finset.card_le_card hA
    obtain ⟨a, ha⟩ : (A \ T).Nonempty := by
      rw [← Finset.card_pos, hm]; exact Nat.succ_pos _
    rw [Finset.mem_sdiff] at ha
    obtain ⟨t, htT, htA⟩ : ∃ t ∈ T, t ∉ A := by
      by_contra hcon
      push_neg at hcon
      have : T = A := Finset.eq_of_subset_of_card_le hcon (by rw [hcardT, hk])
      exact ha.2 (this ▸ ha.1)
    have haC := hA ha.1
    have htC : t ∈ cls I eps r := (Finset.mem_filter.mp htT).1
    have hrt : rank I eps t < k := (Finset.mem_filter.mp htT).2
    have hra : k ≤ rank I eps a := by
      by_contra h; push_neg at h
      exact ha.2 (Finset.mem_filter.mpr ⟨haC, h⟩)
    have hcl : classOf I eps t = classOf I eps a :=
      ((mem_cls I eps).mp htC).trans ((mem_cls I eps).mp haC).symm
    have hpta : I.p t ≤ I.p a := by
      by_contra h
      push_neg at h
      have hlex : toLex (I.p a, a) < toLex (I.p t, t) := Prod.Lex.lt_iff.mpr (Or.inl h)
      have := rank_lt_rank I eps hcl.symm hlex
      omega
    set A' := insert t (A.erase a) with hA'
    have htA' : t ∉ A.erase a := fun h => htA (Finset.mem_of_mem_erase h)
    have hA'sub : A' ⊆ cls I eps r := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact htC
      · exact hA (Finset.mem_of_mem_erase hx)
    have hA'card : A'.card = k := by
      rw [hA', Finset.card_insert_of_notMem htA', Finset.card_erase_of_mem ha.1, hk]
      have : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hrt
      omega
    have hA'm : (A' \ T).card = m := by
      have : A' \ T = (A \ T).erase a := by
        ext x
        simp only [hA', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨rfl | ⟨hxa, hxA⟩, hxT⟩
          · exact absurd htT hxT
          · exact ⟨hxa, hxA, hxT⟩
        · rintro ⟨hxa, hxA, hxT⟩
          exact ⟨Or.inr ⟨hxa, hxA⟩, hxT⟩
      rw [this, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ha), hm]; rfl
    have h1 := ih A' hA'sub hA'card hA'm
    have hnn : 0 ≤ ∏ i ∈ A.erase a, I.p i := Finset.prod_nonneg fun i _ => (hI.2.1 i).1
    calc ∏ i ∈ T, I.p i ≤ ∏ i ∈ A', I.p i := h1
      _ = I.p t * ∏ i ∈ A.erase a, I.p i := by rw [hA', Finset.prod_insert htA']
      _ ≤ I.p a * ∏ i ∈ A.erase a, I.p i := mul_le_mul_of_nonneg_right hpta hnn
      _ = ∏ i ∈ A, I.p i := Finset.mul_prod_erase A _ ha.1

theorem P0_cnt_le (hI : I.Standing) (U : Finset (Fin n)) :
    P0 I eps (cnt I eps U) ≤ ∏ i ∈ U, I.p i := by
  unfold P0
  rw [← Finset.prod_fiberwise (tested I eps (cnt I eps U)) (classIdx I eps),
    ← Finset.prod_fiberwise U (classIdx I eps)]
  apply Finset.prod_le_prod
  · intro r _; exact Finset.prod_nonneg fun i _ => (hI.2.1 i).1
  · intro r _
    rw [tested_filter]
    exact prod_rank_le I eps hI r _ _ _ (filter_subset_cls I eps U r) rfl rfl

theorem cnt_union_sub (U B : Finset (Fin n)) (h : Disjoint B U) (r : Fin (R I eps + 1)) :
    (cnt I eps (U ∪ B) - cnt I eps U) r = (B.filter (fun i => classIdx I eps i = r)).card := by
  simp only [Pi.sub_apply, cnt, Finset.filter_union]
  rw [Finset.card_union_of_disjoint]
  · omega
  · exact Finset.disjoint_filter_filter h.symm

theorem cnt_le_union (U B : Finset (Fin n)) : cnt I eps U ≤ cnt I eps (U ∪ B) := by
  intro r
  exact Finset.card_le_card (Finset.monotone_filter_left _ Finset.subset_union_left)

theorem batchCost_cnt (hI : I.Standing) (U B : Finset (Fin n)) (h : Disjoint B U) :
    batchCost I (roundedCost I eps) B =
      cmin I * stepCost I eps (cnt I eps (U ∪ B) - cnt I eps U) := by
  have hm := cmin_pos I hI
  unfold batchCost stepCost
  have hsum : ∑ i ∈ B, roundedCost I eps i =
      ∑ i ∈ B, (fun r : Fin (R I eps + 1) => cmin I * (1 + eps) ^ (r : ℕ)) (classIdx I eps i) := rfl
  rw [hsum, sum_by_class I eps _ (fun r : Fin (R I eps + 1) => cmin I * (1 + eps) ^ (r : ℕ))]
  simp only [cnt_union_sub I eps U B h]
  rw [mul_add, Finset.mul_sum, mul_div_cancel₀ _ hm.ne']
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem claim (hI : I.Standing) (h0 : 0 < eps) :
    ∀ (S : List (Finset (Fin n))) (U : Finset (Fin n)), S.Pairwise Disjoint →
      (∀ B ∈ S, Disjoint B U) → (∀ i, i ∈ U ∨ ∃ B ∈ S, i ∈ B) →
      ∃ π : List (State I eps), π.head? = some (cnt I eps U) ∧
        π.getLast? = some (Nall I eps) ∧ (∀ N ∈ π, N ∈ F I eps) ∧
        π.IsChain (fun N M => N ≤ M ∧ N ≠ M) ∧
        cmin I * pathCost I eps π ≤
          (∏ i ∈ U, I.p i) * expectedCostWith I (roundedCost I eps) S := by
  intro S
  induction S with
  | nil =>
    intro U _ _ hcov
    have hU : U = Finset.univ := by
      ext i; simp only [Finset.mem_univ, iff_true]
      rcases hcov i with h | ⟨B, hB, _⟩
      · exact h
      · simp at hB
    subst hU
    refine ⟨[Nall I eps], by simp [cnt_univ], rfl, ?_, List.isChain_singleton _, ?_⟩
    · intro N hN
      simp only [List.mem_singleton] at hN
      subst hN; rw [← cnt_univ]; exact cnt_mem_F I eps _
    · simp [pathCost_single, expectedCostWith]
  | cons B S ih =>
    intro U hpw hdis hcov
    rw [List.pairwise_cons] at hpw
    have hBU : Disjoint B U := hdis B List.mem_cons_self
    obtain ⟨π, hhead, hlast, hF, hch, hcost⟩ := ih (U ∪ B) hpw.2
      (fun B' hB' => Finset.disjoint_union_right.mpr
        ⟨hdis B' (List.mem_cons_of_mem _ hB'), (hpw.1 B' hB').symm⟩)
      (by
        intro i
        rcases hcov i with h | ⟨B', hB', hi⟩
        · exact Or.inl (Finset.mem_union_left _ h)
        · rcases List.mem_cons.mp hB' with rfl | hB'
          · exact Or.inl (Finset.mem_union_right _ hi)
          · exact Or.inr ⟨B', hB', hi⟩)
    have hUnn : 0 ≤ ∏ i ∈ U, I.p i := Finset.prod_nonneg fun i _ => (hI.2.1 i).1
    have hb := hI.2.2.2
    by_cases hBe : B = ∅
    · subst hBe
      rw [Finset.union_empty] at hhead hcost
      refine ⟨π, hhead, hlast, hF, hch, ?_⟩
      rw [expectedCostWith_cons, Finset.prod_empty, one_mul]
      have : 0 ≤ (∏ i ∈ U, I.p i) * batchCost I (roundedCost I eps) ∅ := by
        apply mul_nonneg hUnn; simp [batchCost, hb]
      nlinarith
    · obtain ⟨i0, hi0⟩ := Finset.nonempty_iff_ne_empty.mpr hBe
      cases π with
      | nil => simp at hhead
      | cons b rest =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        refine ⟨cnt I eps U :: cnt I eps (U ∪ B) :: rest, rfl, ?_, ?_, ?_, ?_⟩
        · rw [List.getLast?_cons_cons]; exact hlast
        · intro N hN
          rcases List.mem_cons.mp hN with rfl | hN
          · exact cnt_mem_F I eps U
          · exact hF N hN
        · rw [List.isChain_cons_cons]
          refine ⟨⟨cnt_le_union I eps U B, ?_⟩, hch⟩
          intro heq
          have h1 := congrFun heq (classIdx I eps i0)
          have h2 : (cnt I eps (U ∪ B) - cnt I eps U) (classIdx I eps i0) = 0 := by
            rw [Pi.sub_apply, ← h1, Nat.sub_self]
          rw [cnt_union_sub I eps U B hBU] at h2
          rw [Finset.card_eq_zero] at h2
          have : i0 ∈ B.filter (fun i => classIdx I eps i = classIdx I eps i0) :=
            Finset.mem_filter.mpr ⟨hi0, rfl⟩
          rw [h2] at this; simp at this
        · rw [pathCost_cons_cons, mul_add, expectedCostWith_cons, mul_add]
          have hP := P0_cnt_le I eps hI U
          have hbc : 0 ≤ batchCost I (roundedCost I eps) B := by
            unfold batchCost
            apply add_nonneg hb
            apply Finset.sum_nonneg; intro i _
            unfold roundedCost
            have := (cmin_pos I hI).le
            positivity
          have e1 : cmin I * (P0 I eps (cnt I eps U) * stepCost I eps (cnt I eps (U ∪ B) - cnt I eps U))
              = P0 I eps (cnt I eps U) * batchCost I (roundedCost I eps) B := by
            rw [batchCost_cnt I eps hI U B hBU]; ring
          have e2 : (∏ i ∈ U ∪ B, I.p i) = (∏ i ∈ U, I.p i) * ∏ i ∈ B, I.p i :=
            Finset.prod_union hBU.symm
          rw [e2] at hcost
          rw [e1]
          have := mul_le_mul_of_nonneg_right hP hbc
          nlinarith

end BTGreedy

open BTCommon BTGreedy in
theorem solution {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1)
    (S : List (Finset (Fin n))) (hS : IsTestingScheme S) :
    ∃ π, IsPath I eps (F I eps) π ∧
      cmin I * pathCost I eps π ≤ expectedCostWith I (roundedCost I eps) S := by
  obtain ⟨π, hhead, hlast, hF, hch, hcost⟩ := claim I eps hI h0 S ∅ hS.1
    (fun B _ => Finset.disjoint_empty_right B) (fun i => Or.inr (hS.2 i))
  rw [cnt_empty] at hhead
  rw [Finset.prod_empty, one_mul] at hcost
  exact ⟨π, ⟨hhead, hlast, hF, hch⟩, hcost⟩
