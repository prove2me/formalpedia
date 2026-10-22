-- Prove2me | solution 1 for FlowsNetworks.Representatives.sdr_partition_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:09:08.320448+00:00
-- url     : https://prove2.me/submissions/a1f2e21a-1432-49b5-b548-f762a3afa729

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

theorem g70fn2_pc {m p : ℕ} (P : Fin p → Finset (Fin m))
    (hP_disj : ∀ k l, k ≠ l → Disjoint (P k) (P l)) (A : Finset (Fin m)) (U : Finset (Fin p)) :
    (A ∩ U.biUnion P).card = ∑ k ∈ U, (A ∩ P k).card := by
  rw [Finset.inter_biUnion, Finset.card_biUnion]
  intro k _ l _ hkl
  exact Finset.disjoint_of_subset_left Finset.inter_subset_right
    (Finset.disjoint_of_subset_right Finset.inter_subset_right (hP_disj k l hkl))

theorem g70fn2_pc_univ {m p : ℕ} (P : Fin p → Finset (Fin m))
    (hP_disj : ∀ k l, k ≠ l → Disjoint (P k) (P l))
    (hP_cover : ∀ e : Fin m, ∃ k, e ∈ P k) (A : Finset (Fin m)) :
    ∑ k, (A ∩ P k).card = A.card := by
  rw [← g70fn2_pc P hP_disj A Finset.univ]
  congr 1
  ext e
  simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and, and_iff_left_iff_imp]
  exact fun _ => hP_cover e

theorem g70fn2_pc_compl {m p : ℕ} (P : Fin p → Finset (Fin m))
    (hP_disj : ∀ k l, k ≠ l → Disjoint (P k) (P l))
    (hP_cover : ∀ e : Fin m, ∃ k, e ∈ P k) (A : Finset (Fin m)) (U : Finset (Fin p)) :
    (A ∩ U.biUnion P).card + (A ∩ Uᶜ.biUnion P).card = A.card := by
  rw [g70fn2_pc P hP_disj, g70fn2_pc P hP_disj, Finset.sum_add_sum_compl,
    g70fn2_pc_univ P hP_disj hP_cover]

theorem g70fn2_sum_ind {p : ℕ} (U : Finset (Fin p)) (f : Fin p → ℕ) :
    ∑ k ∈ U, f k = ∑ k, if k ∈ U then f k else 0 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem solution {m n p : ℕ} (P : Fin p → Finset (Fin m))
    (hP_ne : ∀ k, (P k).Nonempty)
    (hP_disj : ∀ k l, k ≠ l → Disjoint (P k) (P l))
    (hP_cover : ∀ e : Fin m, ∃ k, e ∈ P k)
    (a a' : Fin p → ℕ) (ha : ∀ k, a k ≤ a' k) (S : Fin n → Finset (Fin m)) :
    (∃ r : Fin n → Fin m, IsSDR S r ∧
        ∀ k, a k ≤ (Finset.univ.image r ∩ P k).card ∧ (Finset.univ.image r ∩ P k).card ≤ a' k) ↔
      ∀ (U : Finset (Fin p)) (V : Finset (Fin n)),
        ((U.biUnion P ∩ indexSet S V).card : ℤ) ≥
          max ((V.card : ℤ) - ∑ k ∈ Uᶜ, (a' k : ℤ))
            ((V.card : ℤ) - (n : ℤ) + ∑ k ∈ U, (a k : ℤ)) := by
  constructor
  · rintro ⟨r, ⟨hr, hrS⟩, hb⟩ U V
    set R := Finset.univ.image r
    have hV : (V.image r).card = V.card := Finset.card_image_of_injective V hr
    have hsub : V.image r ⊆ indexSet S V := by
      intro e he
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 he
      exact Finset.mem_biUnion.2 ⟨j, hj, hrS j⟩
    have hge : (V.image r ∩ U.biUnion P).card ≤ (U.biUnion P ∩ indexSet S V).card := by
      rw [Finset.inter_comm]
      exact Finset.card_le_card (Finset.inter_subset_inter_left hsub)
    have hc := g70fn2_pc_compl P hP_disj hP_cover (V.image r) U
    -- part A
    have hA : (V.image r ∩ Uᶜ.biUnion P).card ≤ ∑ k ∈ Uᶜ, a' k := by
      rw [g70fn2_pc P hP_disj]
      refine Finset.sum_le_sum fun k _ => le_trans ?_ (hb k).2
      exact Finset.card_le_card (Finset.inter_subset_inter_right
        (Finset.image_subset_image (Finset.subset_univ V)))
    -- part B
    have hB1 : ∑ k ∈ U, a k ≤ (R ∩ U.biUnion P).card := by
      rw [g70fn2_pc P hP_disj]
      exact Finset.sum_le_sum fun k _ => (hb k).1
    have hB2 : R ∩ U.biUnion P ⊆ (V.image r ∩ U.biUnion P) ∪ Vᶜ.image r := by
      intro e he
      rw [Finset.mem_inter] at he
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 he.1
      by_cases hj : j ∈ V
      · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨Finset.mem_image_of_mem r hj, he.2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem r (Finset.mem_compl.2 hj))
    have hB3 := (Finset.card_le_card hB2).trans (Finset.card_union_le _ _)
    have hB4 : (Vᶜ.image r).card ≤ n - V.card := by
      have := Finset.card_image_le (s := Vᶜ) (f := r)
      rw [Finset.card_compl, Fintype.card_fin] at this; exact this
    have hVn : V.card ≤ n := by simpa using Finset.card_le_univ V
    rw [ge_iff_le, max_le_iff, ← Nat.cast_sum, ← Nat.cast_sum]
    constructor <;> omega
  · intro H
    have hak : ∀ k, a k ≤ (P k).card := by
      intro k
      have := le_of_max_le_right (H {k} Finset.univ)
      simp only [Finset.singleton_biUnion, Finset.card_univ, Fintype.card_fin,
        Finset.sum_singleton] at this
      have h2 := Finset.card_le_card (Finset.inter_subset_left (s₁ := P k) (s₂ := indexSet S Finset.univ))
      omega
    -- extended family
    let c : Fin p → ℕ := fun k => (P k).card - a k
    let d : Fin p → ℕ := fun k => (P k).card - a' k
    have hdc : ∀ k, d k ≤ c k := fun k => by have := ha k; simp only [c, d]; omega
    let S' : Fin n ⊕ (Σ k, Fin (c k)) → Finset (Fin m ⊕ (Σ k, Fin (c k))) := fun z =>
      Sum.elim (fun j => (S j).map Function.Embedding.inl)
        (fun w => (P w.1).map Function.Embedding.inl ∪
          (if d w.1 ≤ w.2.val then {Sum.inr w} else ∅)) z
    let M : Finset (Fin m ⊕ (Σ k, Fin (c k))) := Finset.univ.map Function.Embedding.inl
    have key := g70fn2_marg S' M
    have hcard : Fintype.card (Fin n ⊕ (Σ k, Fin (c k))) = n + ∑ k, c k := by
      simp [Fintype.card_sum, Fintype.card_sigma]
    rw [hcard] at key
    have hMc : M.card = m := by simp [M]
    obtain ⟨f, hf, hfS, hfM⟩ := key.2 (by
      intro Z
      set V := Z.toLeft
      set W := Z.toRight
      set U := W.image Sigma.fst
      set I := indexSet S V with hIdef
      have hZ : V.card + W.card = Z.card := Finset.card_toLeft_add_card_toRight
      have hN : (I ∪ U.biUnion P).disjSum (W.filter (fun w => d w.1 ≤ w.2.val)) ⊆
          Z.biUnion S' := by
        intro x hx
        rcases x with e | w
        · rw [Finset.inl_mem_disjSum, Finset.mem_union] at hx
          rcases hx with he | he
          · obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.1 he
            exact Finset.mem_biUnion.2 ⟨Sum.inl j, Finset.mem_toLeft.1 hj, by simp [S', hej]⟩
          · obtain ⟨k, hk, hek⟩ := Finset.mem_biUnion.1 he
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hk
            exact Finset.mem_biUnion.2 ⟨Sum.inr w, Finset.mem_toRight.1 hw, by simp [S', hek]⟩
        · rw [Finset.inr_mem_disjSum, Finset.mem_filter] at hx
          exact Finset.mem_biUnion.2 ⟨Sum.inr w, Finset.mem_toRight.1 hx.1, by simp [S', hx.2]⟩
      have hNM : (I ∪ U.biUnion P).map Function.Embedding.inl ⊆ M ∩ Z.biUnion S' := by
        intro x hx
        obtain ⟨e, he, rfl⟩ := Finset.mem_map.1 hx
        exact Finset.mem_inter.2 ⟨by simp [M], hN (Finset.inl_mem_disjSum.2 he)⟩
      have h1 := Finset.card_le_card hN
      rw [Finset.card_disjSum] at h1
      have h2 := Finset.card_le_card hNM
      rw [Finset.card_map] at h2
      have hWU : W.card ≤ ∑ k ∈ U, c k := by
        have : W ⊆ U.sigma (fun k => Finset.univ) := by
          intro w hw
          rw [Finset.mem_sigma]
          exact ⟨Finset.mem_image_of_mem _ hw, Finset.mem_univ _⟩
        refine (Finset.card_le_card this).trans (le_of_eq ?_)
        rw [Finset.card_sigma]; simp
      have hWlt : (W.filter (fun w => ¬ d w.1 ≤ w.2.val)).card ≤ ∑ k ∈ U, d k := by
        have : W.filter (fun w => ¬ d w.1 ≤ w.2.val) ⊆
            U.sigma (fun k => Finset.univ.filter (fun i : Fin (c k) => i.val < d k)) := by
          intro w hw
          rw [Finset.mem_filter] at hw
          rw [Finset.mem_sigma, Finset.mem_filter]
          exact ⟨Finset.mem_image_of_mem _ hw.1, Finset.mem_univ _, by omega⟩
        refine (Finset.card_le_card this).trans ?_
        rw [Finset.card_sigma]
        refine Finset.sum_le_sum fun k _ => ?_
        rw [Fin.card_filter_val_lt]; exact min_le_right _ _
      have hWs := Finset.card_filter_add_card_filter_not (s := W) (fun w => d w.1 ≤ w.2.val)
      have hun := Finset.card_union_add_card_inter I (U.biUnion P)
      have hcI := g70fn2_pc_compl P hP_disj hP_cover I U
      have hBU : (U.biUnion P).card = ∑ k ∈ U, (P k).card := by
        have := g70fn2_pc P hP_disj Finset.univ U
        simpa using this
      have hm : m = ∑ k, (P k).card := by
        have := g70fn2_pc_univ P hP_disj hP_cover Finset.univ
        simp at this; exact this.symm
      have hVn : V.card ≤ n := by simpa using Finset.card_le_univ V
      constructor
      · -- inequality 1
        let U₀ : Finset (Fin p) := Finset.univ.filter (fun k => k ∉ U ∨ (P k).card < a' k)
        have HA := le_of_max_le_left (H U₀ V)
        rw [Finset.inter_comm, ← Nat.cast_sum, ← hIdef] at HA
        have hI0 := g70fn2_pc P hP_disj I U₀
        have hI1 := g70fn2_pc P hP_disj I Uᶜ
        have hsum : ∑ k ∈ U₀ᶜ, a' k + ∑ k ∈ U₀, (I ∩ P k).card + ∑ k ∈ U, d k ≤
            ∑ k ∈ U, (P k).card + ∑ k ∈ Uᶜ, (I ∩ P k).card := by
          simp only [g70fn2_sum_ind U₀ᶜ, g70fn2_sum_ind U₀, g70fn2_sum_ind U, g70fn2_sum_ind Uᶜ,
            ← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun k _ => ?_
          have hIP := Finset.card_le_card (Finset.inter_subset_right (s₁ := I) (s₂ := P k))
          simp only [U₀, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, d]
          by_cases hk : k ∈ U
          · by_cases hk2 : (P k).card < a' k
            · simp [hk, hk2]; omega
            · simp [hk, hk2]; omega
          · simp [hk]
        omega
      · -- inequality 2
        have HB := le_of_max_le_right (H Uᶜ V)
        rw [Finset.inter_comm, ← Nat.cast_sum, ← hIdef] at HB
        have hI1 := g70fn2_pc P hP_disj I Uᶜ
        have hsum : ∑ k ∈ U, c k + ∑ k, (P k).card ≤
            ∑ k, c k + ∑ k ∈ U, (P k).card + ∑ k ∈ Uᶜ, a k := by
          rw [g70fn2_sum_ind U, g70fn2_sum_ind U, g70fn2_sum_ind Uᶜ]
          simp only [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun k _ => ?_
          have := hak k
          by_cases hk : k ∈ U
          · simp [hk]
          · simp only [hk, Finset.mem_compl, c]; simp; omega
        rw [hMc]
        omega)
    -- extract r
    have hS : ∀ j, ∃ e, f (Sum.inl j) = Sum.inl e ∧ e ∈ S j := by
      intro j
      have := hfS (Sum.inl j)
      simp only [S', Sum.elim_inl, Finset.mem_map, Function.Embedding.inl_apply] at this
      obtain ⟨e, he, h⟩ := this
      exact ⟨e, h.symm, he⟩
    choose r hr1 hr2 using hS
    have hrinj : Function.Injective r := by
      intro x y h
      have : f (Sum.inl x) = f (Sum.inl y) := by rw [hr1, hr1, h]
      exact Sum.inl_injective (hf this)
    have hD : ∀ w : Σ k, Fin (c k), (∃ e, f (Sum.inr w) = Sum.inl e ∧ e ∈ P w.1) ∨
        (d w.1 ≤ w.2.val ∧ f (Sum.inr w) = Sum.inr w) := by
      intro w
      have := hfS (Sum.inr w)
      simp only [S', Sum.elim_inr, Finset.mem_union, Finset.mem_map,
        Function.Embedding.inl_apply] at this
      rcases this with ⟨e, he, h⟩ | h
      · exact Or.inl ⟨e, h.symm, he⟩
      · split_ifs at h with hd
        · exact Or.inr ⟨hd, Finset.mem_singleton.1 h⟩
        · simp at h
    refine ⟨r, ⟨hrinj, hr2⟩, fun k => ⟨?_, ?_⟩⟩
    · -- lower bound
      set D0 := (Finset.univ : Finset (Fin (c k))).image (fun i => f (Sum.inr ⟨k, i⟩)) with hD0
      have h2 : D0.card ≤ (P k).card - a k := by
        rw [hD0]; exact Finset.card_image_le.trans (by simp [c])
      have hsub : (P k).map (Function.Embedding.inl (β := Σ k, Fin (c k))) ⊆
          ((Finset.univ.image r ∩ P k).map Function.Embedding.inl) ∪ D0 := by
        intro x hx
        obtain ⟨e, he, rfl⟩ := Finset.mem_map.1 hx
        have hxM : Sum.inl e ∈ M := by simp [M]
        obtain ⟨z, -, hz⟩ := Finset.mem_image.1 (hfM hxM)
        rcases z with j | ⟨k', i⟩
        · rw [hr1] at hz
          cases hz
          exact Finset.mem_union_left _ (Finset.mem_map.2 ⟨r j, Finset.mem_inter.2
            ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), he⟩, rfl⟩)
        · rcases hD ⟨k', i⟩ with ⟨e', h', he'⟩ | ⟨-, h'⟩
          · rw [h'] at hz
            cases hz
            have hkk : k' = k := by
              by_contra hne
              exact Finset.disjoint_left.1 (hP_disj k' k hne) he' he
            subst hkk
            exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h'⟩)
          · rw [h'] at hz; cases hz
      have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [Finset.card_map, Finset.card_map] at h1
      have := hak k
      omega
    · -- upper bound
      let D := (Finset.univ.filter (fun i : Fin (c k) => i.val < d k)).image
        (fun i => f (Sum.inr ⟨k, i⟩))
      have hDc : D.card = d k := by
        rw [Finset.card_image_of_injective _ (fun i i' h => by
          have := hf h; simpa using this), Fin.card_filter_val_lt]
        exact min_eq_right (hdc k)
      have hsub : (Finset.univ.image r ∩ P k).map
          (Function.Embedding.inl (β := Σ k, Fin (c k))) ∪ D ⊆ (P k).map Function.Embedding.inl := by
        intro x hx
        rcases Finset.mem_union.1 hx with hx | hx
        · obtain ⟨e, he, rfl⟩ := Finset.mem_map.1 hx
          exact Finset.mem_map_of_mem _ (Finset.mem_inter.1 he).2
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
          rw [Finset.mem_filter] at hi
          rcases hD ⟨k, i⟩ with ⟨e', h', he'⟩ | ⟨hd, -⟩
          · rw [h']; exact Finset.mem_map_of_mem _ he'
          · exact absurd hd (by simp only; omega)
      have hdisj : Disjoint ((Finset.univ.image r ∩ P k).map
          (Function.Embedding.inl (β := Σ k, Fin (c k)))) D := by
        rw [Finset.disjoint_left]
        intro x hx hxD
        obtain ⟨e, he, rfl⟩ := Finset.mem_map.1 hx
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_inter.1 he).1
        obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hxD
        have hi' : f (Sum.inr ⟨k, i⟩) = f (Sum.inl j) := by rw [hr1]; exact hi
        exact absurd (hf hi') (by simp)
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map, hDc] at h1
      simp only [d] at h1
      omega
