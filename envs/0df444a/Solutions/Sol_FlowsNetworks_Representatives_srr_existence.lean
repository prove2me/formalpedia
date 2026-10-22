-- Prove2me | solution 1 for FlowsNetworks.Representatives.srr_existence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:57:25.5606+00:00
-- url     : https://prove2.me/submissions/62fb3e51-5daa-4a56-ae48-6d1e698190c3

import Mathlib
import Definitions.Def_FlowsNetworks_Representatives_SystemsOfRepresentatives
open FlowsNetworks.Representatives

theorem g70fn2_marg {ι E : Type} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (S : ι → Finset E) (M : Finset E) :
    (∃ r : ι → E, Function.Injective r ∧ (∀ j, r j ∈ S j) ∧ M ⊆ Finset.univ.image r) ↔
      ∀ X : Finset ι, X.card ≤ (X.biUnion S).card ∧
        X.card + M.card ≤ Fintype.card ι + (M ∩ X.biUnion S).card := by
  constructor
  · rintro ⟨r, hr, hrS, hM⟩ X
    constructor
    · rw [← Finset.card_image_of_injective X hr]
      apply Finset.card_le_card
      intro e he
      simp only [Finset.mem_image] at he
      obtain ⟨j, hj, rfl⟩ := he
      exact Finset.mem_biUnion.2 ⟨j, hj, hrS j⟩
    · have h1 : M \ X.biUnion S ⊆ Xᶜ.image r := by
        intro e he
        rw [Finset.mem_sdiff] at he
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (hM he.1)
        refine Finset.mem_image.2 ⟨j, ?_, rfl⟩
        rw [Finset.mem_compl]
        intro hj
        exact he.2 (Finset.mem_biUnion.2 ⟨j, hj, hrS j⟩)
      have h2 := Finset.card_le_card h1
      have h3 := Finset.card_image_le (s := Xᶜ) (f := r)
      rw [Finset.card_compl] at h3
      have h4 : (M \ X.biUnion S).card + (M ∩ X.biUnion S).card = M.card :=
        Finset.card_sdiff_add_card_inter M _
      have h5 := Finset.card_le_univ X
      omega
  · intro H
    have hle : Fintype.card ι ≤ Fintype.card E := by
      have := (H Finset.univ).1
      rw [Finset.card_univ] at this
      exact this.trans (Finset.card_le_univ _)
    let D := Fin (Fintype.card E - Fintype.card ι)
    let T : ι ⊕ D → Finset E := fun z => Sum.elim S (fun _ => Mᶜ) z
    have hall : ∀ Z : Finset (ι ⊕ D), Z.card ≤ (Z.biUnion T).card := by
      intro Z
      have hZ := Finset.card_toLeft_add_card_toRight (u := Z)
      have hsub1 : Z.toLeft.biUnion S ⊆ Z.biUnion T := by
        intro e he
        obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.1 he
        exact Finset.mem_biUnion.2 ⟨Sum.inl j, Finset.mem_toLeft.1 hj, hej⟩
      by_cases hY : Z.toRight = ∅
      · rw [hY, Finset.card_empty] at hZ
        have := (H Z.toLeft).1
        have := Finset.card_le_card hsub1
        omega
      · obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.2 hY
        have hsub2 : (M ∩ Z.toLeft.biUnion S) ∪ Mᶜ ⊆ Z.biUnion T := by
          intro e he
          rcases Finset.mem_union.1 he with he | he
          · exact hsub1 (Finset.mem_inter.1 he).2
          · exact Finset.mem_biUnion.2 ⟨Sum.inr d, Finset.mem_toRight.1 hd, he⟩
        have hdisj : Disjoint (M ∩ Z.toLeft.biUnion S) Mᶜ :=
          Finset.disjoint_left.2 fun e he he' =>
            (Finset.mem_compl.1 he') (Finset.mem_inter.1 he).1
        have h1 := Finset.card_le_card hsub2
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_compl] at h1
        have h2 := (H Z.toLeft).2
        have h3 : Z.toRight.card ≤ Fintype.card E - Fintype.card ι := by
          have := Finset.card_le_univ Z.toRight
          simpa [D] using this
        have h4 := Finset.card_le_card (Finset.subset_univ M)
        rw [Finset.card_univ] at h4
        omega
    obtain ⟨f, hf, hfT⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective T).1 hall
    have hcard : Fintype.card (ι ⊕ D) = Fintype.card E := by
      simp [D, Fintype.card_sum]; omega
    have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩
    refine ⟨fun j => f (Sum.inl j), fun a b h => Sum.inl_injective (hf h),
      fun j => hfT (Sum.inl j), ?_⟩
    intro e he
    obtain ⟨z, rfl⟩ := hbij.2 e
    rcases z with j | d
    · exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
    · exact absurd he (Finset.mem_compl.1 (hfT (Sum.inr d)))

theorem g70fn2_card_prod {m K : ℕ} (T : Finset (Fin m)) (b : Fin m → ℕ) (hb : ∀ i, b i ≤ K) :
    ((T ×ˢ (Finset.univ : Finset (Fin K))).filter (fun p => p.2.val < b p.1)).card
      = ∑ i ∈ T, b i := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.card_filter]
  have := Fin.card_filter_val_lt (n := K) (m := b i)
  rw [min_eq_right (hb i)] at this
  exact this

theorem g70fn2_cnt_lt {m n : ℕ} (r : Fin n → Fin m) (j k : Fin n) (hjk : r j = r k) (h : j < k) :
    (Finset.univ.filter (fun l => r l = r j ∧ l < j)).card <
      (Finset.univ.filter (fun l => r l = r k ∧ l < k)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨j, by simp [hjk, h], by simp⟩
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    exact ⟨hl.1.trans hjk, hl.2.trans h⟩

theorem g70fn2_cnt_inj {m n : ℕ} (r : Fin n → Fin m) (j k : Fin n) (hjk : r j = r k)
    (h : (Finset.univ.filter (fun l => r l = r j ∧ l < j)).card =
      (Finset.univ.filter (fun l => r l = r k ∧ l < k)).card) : j = k := by
  rcases lt_trichotomy j k with hl | hl | hl
  · exact absurd h (g70fn2_cnt_lt r j k hjk hl).ne
  · exact hl
  · exact absurd h.symm (g70fn2_cnt_lt r k j hjk.symm hl).ne

theorem g70fn2_cnt_le {m n : ℕ} (r : Fin n → Fin m) (j : Fin n) :
    (Finset.univ.filter (fun l => r l = r j ∧ l < j)).card < occurrences r (r j) := by
  unfold occurrences
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨j, by simp, by simp⟩
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    exact hl.1

theorem solution {m n : ℕ} (S : Fin n → Finset (Fin m)) (a a' : Fin m → ℕ)
    (ha : ∀ i, a i ≤ a' i) :
    (∃ r : Fin n → Fin m, IsSRR S a a' r) ↔
      ∀ X : Finset (Fin n),
        (X.card : ℤ) ≤ min ((n : ℤ) - ∑ i, (a i : ℤ) + ∑ i ∈ indexSet S X, (a i : ℤ))
          (∑ i ∈ indexSet S X, (a' i : ℤ)) := by
  set K := ∑ i, a' i + 1 with hK
  have hK' : ∀ i, a' i < K := fun i => by
    have := Finset.single_le_sum (f := a') (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  let S' : Fin n → Finset (Fin m × Fin K) := fun j =>
    ((S j ×ˢ Finset.univ).filter (fun p => p.2.val < a' p.1))
  let M : Finset (Fin m × Fin K) :=
    ((Finset.univ ×ˢ Finset.univ).filter (fun p => p.2.val < a p.1))
  have key := g70fn2_marg S' M
  simp only [Fintype.card_fin] at key
  have hbU : ∀ X : Finset (Fin n), X.biUnion S' =
      ((X.biUnion S ×ˢ Finset.univ).filter (fun p => p.2.val < a' p.1)) := by
    intro X; ext p
    simp only [S', Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      and_true]
    constructor
    · rintro ⟨j, hj, h1, h2⟩; exact ⟨⟨j, hj, h1⟩, h2⟩
    · rintro ⟨⟨j, hj, h1⟩, h2⟩; exact ⟨j, hj, h1, h2⟩
  have hMI : ∀ X : Finset (Fin n), M ∩ X.biUnion S' =
      ((X.biUnion S ×ˢ Finset.univ).filter (fun p => p.2.val < a p.1)) := by
    intro X; rw [hbU]; ext p
    simp only [M, Finset.mem_inter, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and, and_true]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨h1, h2, lt_of_lt_of_le h1 (ha _)⟩
  have hcI : ∀ X : Finset (Fin n), (X.biUnion S').card = ∑ i ∈ X.biUnion S, a' i := by
    intro X; rw [hbU]; exact g70fn2_card_prod _ _ fun i => (hK' i).le
  have hcMI : ∀ X : Finset (Fin n), (M ∩ X.biUnion S').card = ∑ i ∈ X.biUnion S, a i := by
    intro X; rw [hMI]; exact g70fn2_card_prod _ _ fun i => ((ha i).trans (hK' i).le)
  have hcM : M.card = ∑ i, a i := g70fn2_card_prod _ _ fun i => ((ha i).trans (hK' i).le)
  have hcond : (∀ X : Finset (Fin n),
        (X.card : ℤ) ≤ min ((n : ℤ) - ∑ i, (a i : ℤ) + ∑ i ∈ indexSet S X, (a i : ℤ))
          (∑ i ∈ indexSet S X, (a' i : ℤ))) ↔
      ∀ X : Finset (Fin n), X.card ≤ (X.biUnion S').card ∧
        X.card + M.card ≤ n + (M ∩ X.biUnion S').card := by
    refine forall_congr' fun X => ?_
    rw [hcI, hcMI, hcM, le_min_iff]
    unfold indexSet
    have e1 : ((∑ i, a i : ℕ) : ℤ) = ∑ i, (a i : ℤ) := by push_cast; rfl
    have e2 : ((∑ i ∈ X.biUnion S, a i : ℕ) : ℤ) = ∑ i ∈ X.biUnion S, (a i : ℤ) := by push_cast; rfl
    have e3 : ((∑ i ∈ X.biUnion S, a' i : ℕ) : ℤ) = ∑ i ∈ X.biUnion S, (a' i : ℤ) := by
      push_cast; rfl
    rw [← e1, ← e2, ← e3]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> omega
    · rintro ⟨h1, h2⟩; constructor <;> omega
  rw [hcond, ← key]
  constructor
  · rintro ⟨r, hrS, hocc⟩
    let cnt : Fin n → ℕ := fun j => (Finset.univ.filter (fun l => r l = r j ∧ l < j)).card
    have hcnt : ∀ j, cnt j < a' (r j) := fun j =>
      lt_of_lt_of_le (g70fn2_cnt_le r j) (hocc (r j)).2
    refine ⟨fun j => (r j, ⟨cnt j, (hcnt j).trans (hK' _)⟩), ?_, ?_, ?_⟩
    · intro j k h
      simp only [Prod.mk.injEq, Fin.mk.injEq] at h
      exact g70fn2_cnt_inj r j k h.1 h.2
    · intro j
      simp only [S', Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      exact ⟨hrS j, hcnt j⟩
    · rintro ⟨i, c⟩ hp
      simp only [M, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
      have hsurj := Finset.surj_on_of_inj_on_of_card_le
        (s := Finset.univ.filter (fun l => r l = i)) (t := Finset.range (occurrences r i))
        (fun j _ => cnt j) (by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [Finset.mem_range, ← hj]; exact g70fn2_cnt_le r j)
        (by
          intro j k hj hk h
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hk
          exact g70fn2_cnt_inj r j k (hj.trans hk.symm) h)
        (by rw [Finset.card_range]; rfl)
      obtain ⟨j, hj, hcj⟩ := hsurj c.val (by
        rw [Finset.mem_range]; exact lt_of_lt_of_le hp (hocc i).1)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      refine Finset.mem_image.2 ⟨j, Finset.mem_univ _, ?_⟩
      ext
      · simp [hj]
      · simp [hcj]
  · rintro ⟨r', hr', hrS', hM⟩
    refine ⟨fun j => (r' j).1, fun j => ?_, fun i => ⟨?_, ?_⟩⟩
    · have := hrS' j
      simp only [S', Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at this
      exact this.1
    · -- lower bound
      have hsub : ((Finset.univ.filter (fun c : Fin K => c.val < a i)).image
          (fun c => (i, c))) ⊆ (Finset.univ.filter (fun j => (r' j).1 = i)).image r' := by
        intro p hp
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        have hmem : (i, c) ∈ M := by
          simp only [M, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
          exact hc
        obtain ⟨j, -, hj⟩ := Finset.mem_image.1 (hM hmem)
        exact Finset.mem_image.2 ⟨j, by simp [hj], hj⟩
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ (fun c d h => by simpa using h),
        Fin.card_filter_val_lt, min_eq_right ((ha i).trans (hK' i).le)] at h1
      exact h1.trans Finset.card_image_le
    · -- upper bound
      unfold occurrences
      have hsub : (Finset.univ.filter (fun j => (r' j).1 = i)).image (fun j => (r' j).2) ⊆
          Finset.univ.filter (fun c : Fin K => c.val < a' i) := by
        intro c hc
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        have := hrS' j
        simp only [S', Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at this
        rw [← hj]; exact this.2
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_image_of_injOn, Fin.card_filter_val_lt, min_eq_right (hK' i).le] at h1
      · exact h1
      · intro j hj k hk h
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj hk
        exact hr' (Prod.ext (hj.trans hk.symm) h)
