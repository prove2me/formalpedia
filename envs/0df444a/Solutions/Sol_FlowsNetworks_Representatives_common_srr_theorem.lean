-- Prove2me | solution 1 for FlowsNetworks.Representatives.common_srr_theorem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:41:55.016529+00:00
-- url     : https://prove2.me/submissions/256b27a9-d22d-415a-af1c-34d4304cc244

import Mathlib
theorem g70fn2_card_prod {m K : ℕ} (T : Finset (Fin m)) (b : Fin m → ℕ) (hb : ∀ i, b i ≤ K) :
    ((T ×ˢ (Finset.univ : Finset (Fin K))).filter (fun p => p.2.val < b p.1)).card
      = ∑ i ∈ T, b i := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.card_filter]
  have := Fin.card_filter_val_lt (n := K) (m := b i)
  rw [min_eq_right (hb i)] at this
  exact this


theorem g70fn2_csrr_fwd {m n : ℕ} (S T : Fin n → Finset (Fin m)) (a a' : Fin m → ℕ)
    (r : Fin n → Fin m) (σ : Equiv.Perm (Fin n))
    (hrS : ∀ j, r j ∈ S j ∧ r j ∈ T (σ j))
    (hb : ∀ i, a i ≤ (Finset.univ.filter (fun j => r j = i)).card ∧
          (Finset.univ.filter (fun j => r j = i)).card ≤ a' i) (X Y : Finset (Fin n)) :
    (X.card : ℤ) + (Y.card : ℤ) ≤
          (n : ℤ) - ∑ i, (a i : ℤ) + ∑ i ∈ X.biUnion S ∪ Y.biUnion T, (a i : ℤ)
            + ∑ i ∈ X.biUnion S ∩ Y.biUnion T, (a' i : ℤ) := by
  set I := X.biUnion S
  set J := Y.biUnion T
  set Yp := Finset.univ.filter (fun j => σ j ∈ Y)
  have hYp : Yp.card = Y.card := by
    have : Yp = Y.map σ.symm.toEmbedding := by
      ext j; simp [Yp, Equiv.apply_eq_iff_eq_symm_apply]
    rw [this, Finset.card_map]
  -- W
  have hW : (X ∩ Yp).card ≤ ∑ i ∈ I ∩ J, a' i := by
    rw [Finset.card_eq_sum_card_fiberwise (f := r) (t := I ∩ J)]
    · refine Finset.sum_le_sum fun i _ => le_trans ?_ (hb i).2
      apply Finset.card_le_card
      intro j hj; simp only [Finset.mem_filter] at hj ⊢; exact ⟨Finset.mem_univ _, hj.2⟩
    · intro j hj
      simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe, Yp, Finset.mem_filter,
        Finset.mem_univ, true_and] at hj ⊢
      exact ⟨Finset.mem_biUnion.2 ⟨j, hj.1, (hrS j).1⟩, Finset.mem_biUnion.2 ⟨σ j, hj.2, (hrS j).2⟩⟩
  -- O
  set O := Finset.univ.filter (fun j => r j ∉ I ∪ J)
  have hO : ∑ i ∈ (I ∪ J)ᶜ, a i ≤ O.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := r) (t := (I ∪ J)ᶜ)]
    · refine Finset.sum_le_sum fun i hi => le_trans (hb i).1 (le_of_eq ?_)
      congr 1; ext j
      simp only [O, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact ⟨h ▸ (Finset.mem_compl.1 hi), h⟩
      · exact fun h => h.2
    · intro j hj
      simp only [O, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj
      simpa using hj
  have hOd : Disjoint O (X ∪ Yp) := by
    rw [Finset.disjoint_left]
    intro j hjO hj
    simp only [O, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hjO hj
    apply hjO
    rcases hj with hj | hj
    · exact Or.inl (Finset.mem_biUnion.2 ⟨j, hj, (hrS j).1⟩)
    · simp only [Yp, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact Or.inr (Finset.mem_biUnion.2 ⟨σ j, hj, (hrS j).2⟩)
  have h3 := Finset.card_union_add_card_inter X Yp
  have h4 : O.card + (X ∪ Yp).card ≤ n := by
    rw [← Finset.card_union_of_disjoint hOd]
    simpa using Finset.card_le_univ (O ∪ (X ∪ Yp))
  have h5 : ∑ i, (a i : ℤ) = ∑ i ∈ I ∪ J, (a i : ℤ) + ∑ i ∈ (I ∪ J)ᶜ, (a i : ℤ) :=
    (Finset.sum_add_sum_compl _ _).symm
  have hO' : ((∑ i ∈ (I ∪ J)ᶜ, a i : ℕ) : ℤ) ≤ O.card := by exact_mod_cast hO
  have hW' : (((X ∩ Yp).card : ℕ) : ℤ) ≤ ((∑ i ∈ I ∩ J, a' i : ℕ) : ℤ) := by exact_mod_cast hW
  push_cast at hO' hW'
  rw [← hYp]
  have : ((X.card : ℕ) : ℤ) + Yp.card = (X ∪ Yp).card + (X ∩ Yp).card := by exact_mod_cast h3.symm
  have h4' : ((O.card : ℕ) : ℤ) + (X ∪ Yp).card ≤ n := by exact_mod_cast h4
  linarith

theorem g70fn2_csrr_bwd {m n : ℕ} (S T : Fin n → Finset (Fin m)) (a a' : Fin m → ℕ)
    (ha : ∀ i, a i ≤ a' i)
    (H : ∀ X Y : Finset (Fin n),
        (X.card : ℤ) + (Y.card : ℤ) ≤
          (n : ℤ) - ∑ i, (a i : ℤ) + ∑ i ∈ X.biUnion S ∪ Y.biUnion T, (a i : ℤ)
            + ∑ i ∈ X.biUnion S ∩ Y.biUnion T, (a' i : ℤ)) :
    ∃ (r : Fin n → Fin m) (σ : Equiv.Perm (Fin n)),
        (∀ j, r j ∈ S j ∧ r j ∈ T (σ j)) ∧
        ∀ i, a i ≤ (Finset.univ.filter (fun j => r j = i)).card ∧
          (Finset.univ.filter (fun j => r j = i)).card ≤ a' i := by
  classical
  set K := ∑ i, a' i + 1 with hK
  have hK' : ∀ i, a' i < K := fun i => by
    have := Finset.single_le_sum (f := a') (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  let ex : Finset (Fin m) → (Fin m → ℕ) → Finset (Fin m × Fin K) := fun A b =>
    (A ×ˢ Finset.univ).filter (fun p => p.2.val < b p.1)
  have mem_ex : ∀ A b p, p ∈ ex A b ↔ p.1 ∈ A ∧ p.2.val < b p.1 := by
    intro A b p; simp [ex]
  have card_ex : ∀ A b, (∀ i, b i ≤ K) → (ex A b).card = ∑ i ∈ A, b i :=
    fun A b hb => g70fn2_card_prod A b hb
  let S' : Fin n → Finset (Fin m × Fin K) := fun j => ex (S j) a'
  let T' : Fin n → Finset (Fin m × Fin K) := fun j => ex (T j) a'
  let M : Finset (Fin m × Fin K) := ex Finset.univ a
  have hbU : ∀ (U : Fin n → Finset (Fin m)) (X : Finset (Fin n)),
      X.biUnion (fun j => ex (U j) a') = ex (X.biUnion U) a' := by
    intro U X; ext p
    simp only [Finset.mem_biUnion, mem_ex]
    constructor
    · rintro ⟨j, hj, h1, h2⟩; exact ⟨⟨j, hj, h1⟩, h2⟩
    · rintro ⟨⟨j, hj, h1⟩, h2⟩; exact ⟨j, hj, h1, h2⟩
  let t : Fin n ⊕ (Fin m × Fin K) → Finset ((Fin m × Fin K) ⊕ Fin n) := fun z =>
    Sum.elim (fun j => (S' j).map Function.Embedding.inl)
      (fun e => (if e ∈ M then ∅ else {Sum.inl e}) ∪
        ((Finset.univ.filter (fun k => e ∈ T' k)).map Function.Embedding.inr)) z
  have hall : ∀ Z : Finset (Fin n ⊕ (Fin m × Fin K)), Z.card ≤ (Z.biUnion t).card := by
    intro Z
    set X := Z.toLeft
    set F := Z.toRight
    set Ks := Finset.univ.filter (fun k => ∃ e ∈ F, e ∈ T' k)
    set Y := Ksᶜ
    set I := X.biUnion S
    set J := Y.biUnion T
    set I' := ex I a'
    set J' := ex J a'
    have hZ : X.card + F.card = Z.card := Finset.card_toLeft_add_card_toRight
    have hsub : (I' ∪ F.filter (fun e => e ∉ M)).disjSum Ks ⊆ Z.biUnion t := by
      intro w hw
      rcases w with e | k
      · rw [Finset.inl_mem_disjSum, Finset.mem_union] at hw
        rcases hw with he | he
        · change e ∈ ex (X.biUnion S) a' at he
          rw [← hbU S X] at he
          obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.1 he
          exact Finset.mem_biUnion.2 ⟨Sum.inl j, Finset.mem_toLeft.1 hj, by simp [t, S', hej]⟩
        · rw [Finset.mem_filter] at he
          exact Finset.mem_biUnion.2 ⟨Sum.inr e, Finset.mem_toRight.1 he.1, by simp [t, he.2]⟩
      · rw [Finset.inr_mem_disjSum] at hw
        simp only [Ks, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        obtain ⟨e, he, hek⟩ := hw
        exact Finset.mem_biUnion.2 ⟨Sum.inr e, Finset.mem_toRight.1 he, by simp [t, hek]⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_disjSum] at h1
    -- F avoids J'
    have hFJ : ∀ e ∈ F, e ∉ J' := by
      intro e he heJ
      change e ∈ ex (Y.biUnion T) a' at heJ
      rw [← hbU T Y] at heJ
      obtain ⟨k, hk, hek⟩ := Finset.mem_biUnion.1 heJ
      rw [Finset.mem_compl] at hk
      exact hk (by simp only [Ks, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨e, he, hek⟩)
    -- counting
    have c1 : (I' ∪ F.filter (fun e => e ∉ M)).card =
        I'.card + ((F.filter (fun e => e ∉ M)) \ I').card := by
      rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]
    have c2 : F.card ≤ (F ∩ I').card + ((F.filter (fun e => e ∉ M)) \ I').card +
        ((F \ I').filter (fun e => e ∈ M)).card := by
      have : F ⊆ (F ∩ I') ∪ ((F.filter (fun e => e ∉ M)) \ I') ∪ ((F \ I').filter (fun e => e ∈ M)) := by
        intro e he
        by_cases h1 : e ∈ I'
        · simp [he, h1]
        · by_cases h2 : e ∈ M <;> simp [he, h1, h2]
      have q1 := Finset.card_le_card this
      have q2 := Finset.card_union_le ((F ∩ I') ∪ ((F.filter (fun e => e ∉ M)) \ I'))
        ((F \ I').filter (fun e => e ∈ M))
      have q3 := Finset.card_union_le (F ∩ I') ((F.filter (fun e => e ∉ M)) \ I')
      omega
    have c3 : ((F \ I').filter (fun e => e ∈ M)).card ≤ ∑ i ∈ (I ∪ J)ᶜ, a i := by
      rw [← card_ex _ a (fun i => ((ha i).trans (hK' i).le))]
      apply Finset.card_le_card
      intro e he
      simp only [Finset.mem_filter, Finset.mem_sdiff] at he
      obtain ⟨⟨heF, heI⟩, heM⟩ := he
      have hM' := (mem_ex _ _ _).1 heM
      rw [mem_ex]
      refine ⟨?_, hM'.2⟩
      rw [Finset.mem_compl, Finset.mem_union]
      rintro (h | h)
      · exact heI ((mem_ex _ _ _).2 ⟨h, lt_of_lt_of_le hM'.2 (ha _)⟩)
      · exact hFJ e heF ((mem_ex _ _ _).2 ⟨h, lt_of_lt_of_le hM'.2 (ha _)⟩)
    have c4 : (F ∩ I').card + ∑ i ∈ I ∩ J, a' i ≤ I'.card := by
      have hIJ : ex (I ∩ J) a' = I' ∩ J' := by
        ext p; simp only [mem_ex, Finset.mem_inter, I', J']; tauto
      rw [← card_ex _ a' (fun i => (hK' i).le), hIJ]
      rw [← Finset.card_union_of_disjoint]
      · apply Finset.card_le_card
        intro e he
        rcases Finset.mem_union.1 he with h | h
        · exact (Finset.mem_inter.1 h).2
        · exact (Finset.mem_inter.1 h).1
      · rw [Finset.disjoint_left]
        intro e h1 h2
        exact hFJ e (Finset.mem_inter.1 h1).1 (Finset.mem_inter.1 h2).2
    have hX := H X Y
    have hY : Y.card = n - Ks.card := by rw [Finset.card_compl, Fintype.card_fin]
    have hKn : Ks.card ≤ n := by simpa using Finset.card_le_univ Ks
    have h5 : ∑ i, (a i : ℤ) = ∑ i ∈ I ∪ J, (a i : ℤ) + ∑ i ∈ (I ∪ J)ᶜ, (a i : ℤ) :=
      (Finset.sum_add_sum_compl _ _).symm
    have c3' : (((F \ I').filter (fun e => e ∈ M)).card : ℤ) ≤ ∑ i ∈ (I ∪ J)ᶜ, (a i : ℤ) := by
      exact_mod_cast c3
    have c4' : ((F ∩ I').card : ℤ) + ∑ i ∈ I ∩ J, (a' i : ℤ) ≤ I'.card := by exact_mod_cast c4
    have c1' : ((I' ∪ F.filter (fun e => e ∉ M)).card : ℤ) =
        I'.card + ((F.filter (fun e => e ∉ M)) \ I').card := by exact_mod_cast c1
    have c2' : (F.card : ℤ) ≤ (F ∩ I').card + ((F.filter (fun e => e ∉ M)) \ I').card +
        ((F \ I').filter (fun e => e ∈ M)).card := by exact_mod_cast c2
    have h1' : ((I' ∪ F.filter (fun e => e ∉ M)).card : ℤ) + Ks.card ≤ (Z.biUnion t).card := by
      exact_mod_cast h1
    have hY' : (Y.card : ℤ) = n - Ks.card := by rw [hY]; push_cast [hKn]; ring
    have hZ' : (X.card : ℤ) + F.card = Z.card := by exact_mod_cast hZ
    have : (Z.card : ℤ) ≤ (Z.biUnion t).card := by linarith
    exact_mod_cast this
  obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2
    ⟨hf, by simp [Fintype.card_sum]; omega⟩
  have hS : ∀ j, ∃ e, f (Sum.inl j) = Sum.inl e ∧ e ∈ S' j := by
    intro j
    have := hft (Sum.inl j)
    simp only [t, Sum.elim_inl, Finset.mem_map, Function.Embedding.inl_apply] at this
    obtain ⟨e, he, h⟩ := this
    exact ⟨e, h.symm, he⟩
  choose r' hr1 hr2 using hS
  have hT : ∀ j, ∃ k, f (Sum.inr (r' j)) = Sum.inr k ∧ r' j ∈ T' k := by
    intro j
    have := hft (Sum.inr (r' j))
    simp only [t, Sum.elim_inr, Finset.mem_union, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and, Function.Embedding.inr_apply] at this
    rcases this with h | ⟨k, hk, h⟩
    · split_ifs at h with hm
      · simp at h
      · rw [Finset.mem_singleton, ← hr1 j] at h
        exact absurd (hf h) (by simp)
    · exact ⟨k, h.symm, hk⟩
  choose τ hτ1 hτ2 using hT
  have hrinj : Function.Injective r' := by
    intro x y h
    have : f (Sum.inl x) = f (Sum.inl y) := by rw [hr1, hr1, h]
    exact Sum.inl_injective (hf this)
  have hτinj : Function.Injective τ := by
    intro x y h
    have : f (Sum.inr (r' x)) = f (Sum.inr (r' y)) := by rw [hτ1, hτ1, h]
    exact hrinj (Sum.inr_injective (hf this))
  have hτbij : Function.Bijective τ := (Fintype.bijective_iff_injective_and_card τ).2 ⟨hτinj, rfl⟩
  have hM : ∀ e ∈ M, ∃ j, r' j = e := by
    intro e he
    obtain ⟨z, hz⟩ := hbij.2 (Sum.inl e)
    rcases z with j | e'
    · rw [hr1] at hz; exact ⟨j, Sum.inl_injective hz⟩
    · have := hft (Sum.inr e')
      rw [hz] at this
      simp only [t, Sum.elim_inr, Finset.mem_union, Finset.mem_map, Function.Embedding.inr_apply,
        reduceCtorEq, and_false, exists_false, or_false] at this
      split_ifs at this with hm
      · simp at this
      · rw [Finset.mem_singleton, Sum.inl.injEq] at this
        subst this; exact absurd he hm
  refine ⟨fun j => (r' j).1, Equiv.ofBijective τ hτbij, fun j => ?_, fun i => ⟨?_, ?_⟩⟩
  · have h1 := (mem_ex _ _ _).1 (hr2 j)
    have h2 := (mem_ex _ _ _).1 (hτ2 j)
    exact ⟨h1.1, h2.1⟩
  · have hsub : ((Finset.univ.filter (fun c : Fin K => c.val < a i)).image
        (fun c => (i, c))) ⊆ (Finset.univ.filter (fun j => (r' j).1 = i)).image r' := by
      intro p hp
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      obtain ⟨j, hj⟩ := hM (i, c) ((mem_ex _ _ _).2 ⟨Finset.mem_univ _, hc⟩)
      exact Finset.mem_image.2 ⟨j, by simp [hj], hj⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (fun c d h => by simpa using h),
      Fin.card_filter_val_lt, min_eq_right ((ha i).trans (hK' i).le)] at h1
    exact h1.trans Finset.card_image_le
  · have hsub : (Finset.univ.filter (fun j => (r' j).1 = i)).image (fun j => (r' j).2) ⊆
        Finset.univ.filter (fun c : Fin K => c.val < a' i) := by
      intro c hc
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have := (mem_ex _ _ _).1 (hr2 j)
      rw [← hj]; exact this.2
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn, Fin.card_filter_val_lt, min_eq_right (hK' i).le] at h1
    · exact h1
    · intro j hj k hk h
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj hk
      exact hrinj (Prod.ext (hj.trans hk.symm) h)

theorem solution {m n : ℕ} (S T : Fin n → Finset (Fin m)) (a a' : Fin m → ℕ)
    (ha : ∀ i, a i ≤ a' i) :
    (∃ (r : Fin n → Fin m) (σ : Equiv.Perm (Fin n)),
        (∀ j, r j ∈ S j ∧ r j ∈ T (σ j)) ∧
        ∀ i, a i ≤ (Finset.univ.filter (fun j => r j = i)).card ∧
          (Finset.univ.filter (fun j => r j = i)).card ≤ a' i) ↔
      ∀ X Y : Finset (Fin n),
        (X.card : ℤ) + (Y.card : ℤ) ≤
          (n : ℤ) - ∑ i, (a i : ℤ) + ∑ i ∈ X.biUnion S ∪ Y.biUnion T, (a i : ℤ)
            + ∑ i ∈ X.biUnion S ∩ Y.biUnion T, (a' i : ℤ) := by
  constructor
  · rintro ⟨r, σ, h1, h2⟩ X Y
    exact g70fn2_csrr_fwd S T a a' r σ h1 h2 X Y
  · exact g70fn2_csrr_bwd S T a a' ha
