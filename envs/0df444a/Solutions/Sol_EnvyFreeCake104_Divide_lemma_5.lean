-- Prove2me | solution 1 for EnvyFreeCake104.Divide.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T17:00:19.364207+00:00
-- url     : https://prove2.me/submissions/bba4d950-a3fb-4af8-aae6-246933f98251

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_lemma_3

open EnvyFreeCake104.Divide

namespace L5Aux

theorem interval_measurable (I : Interval) : MeasurableSet I.toSet := by
  unfold Interval.toSet; split_ifs
  · exact measurableSet_Icc
  · exact measurableSet_Ico

theorem piece_measurable (P : Piece) : MeasurableSet P.toSet := by
  have : P.toSet = ⋃ I ∈ P, I.toSet := by ext x; simp [Piece.toSet]
  rw [this]
  exact MeasurableSet.biUnion P.finite_toSet.countable (fun I _ => interval_measurable I)

theorem value_mono (v : Valuation) {A B : Set ℝ} (h : A ⊆ B) (hB : MeasurableSet B) :
    v.value A ≤ v.value B := by
  unfold Valuation.value
  apply MeasureTheory.setIntegral_mono_set (v.integrable.mono_set Set.inter_subset_right)
  · exact MeasureTheory.ae_restrict_of_forall_mem (hB.inter measurableSet_Icc)
      (fun x hx => v.nonneg x hx.2)
  · exact (Set.inter_subset_inter_left _ h).eventuallyLE

theorem value_union (v : Valuation) {A B : Set ℝ} (hB : MeasurableSet B) (hd : Disjoint A B) :
    v.value (A ∪ B) = v.value A + v.value B := by
  unfold Valuation.value
  rw [Set.union_inter_distrib_right]
  apply MeasureTheory.setIntegral_union
  · exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left hd
  · exact hB.inter measurableSet_Icc
  · exact v.integrable.mono_set Set.inter_subset_right
  · exact v.integrable.mono_set Set.inter_subset_right

theorem value_empty (v : Valuation) : v.value ∅ = 0 := by simp [Valuation.value]

theorem value_nonneg (v : Valuation) {A : Set ℝ} (hA : MeasurableSet A) : 0 ≤ v.value A := by
  have := value_mono v (Set.empty_subset A) hA
  rwa [value_empty] at this

theorem value_biUnion {ι : Type} [DecidableEq ι] (v : Valuation) (A : ι → Set ℝ) (s : Finset ι)
    (hm : ∀ i ∈ s, MeasurableSet (A i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j)) :
    v.value (⋃ i ∈ s, A i) = ∑ i ∈ s, v.value (A i) := by
  induction s using Finset.induction_on with
  | empty => simp [value_empty]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    have hms : MeasurableSet (⋃ i ∈ s, A i) :=
      Finset.measurableSet_biUnion s (fun i hi => hm i (Finset.mem_insert_of_mem hi))
    rw [value_union v hms, ih (fun i hi => hm i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj hij => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)]
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨j, hj, hxj⟩ := hx'
    exact Set.disjoint_left.mp (hd a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)
      (fun h => ha (h ▸ hj))) hx hxj

/-- A simple path from `a` to `b` out of a reflexive-transitive chain. -/
theorem simple_path {ι : Type} [DecidableEq ι] (r : ι → ι → Prop) (a b : ι)
    (h : Relation.ReflTransGen r a b) :
    ∃ l : List ι, l.Nodup ∧ l.head? = some a ∧ l.getLast? = some b ∧ List.IsChain r l := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[b], List.nodup_singleton b, rfl, rfl, List.isChain_singleton b⟩
  | @head a c hac _ ih =>
    obtain ⟨l, hnd, hhd, hlast, hch⟩ := ih
    cases l with
    | nil => simp at hhd
    | cons x xs =>
      simp only [List.head?_cons, Option.some.injEq] at hhd
      subst hhd
      by_cases ha : a ∈ x :: xs
      · obtain ⟨l1, l2, hl⟩ := List.append_of_mem ha
        refine ⟨a :: l2, ?_, rfl, ?_, ?_⟩
        · rw [hl] at hnd; exact hnd.sublist (List.sublist_append_right _ _)
        · rw [hl, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at hlast; exact hlast
        · rw [hl] at hch; exact hch.right_of_append
      · refine ⟨a :: x :: xs, List.nodup_cons.mpr ⟨ha, hnd⟩, rfl, ?_, ?_⟩
        · rw [List.getLast?_cons_cons]; exact hlast
        · exact List.isChain_cons_cons.mpr ⟨hac, hch⟩

theorem perm_bijOn {ι : Type} (N : Finset ι) (π : Equiv.Perm ι) (h : ∀ a, a ∉ N → π a = a) :
    Set.BijOn π (N : Set ι) (N : Set ι) := by
  have hmap : ∀ a, a ∈ N → π a ∈ N := by
    intro a ha
    by_contra hn
    have := h _ hn
    exact hn (by rw [π.injective this]; exact ha)
  refine ⟨fun a ha => hmap a ha, π.injective.injOn, fun b hb => ⟨π.symm b, ?_, by simp⟩⟩
  by_contra hn
  have := h _ hn
  simp at this
  exact hn (this ▸ hb)

theorem alpha_pos (n t : ℕ) (hn : 1 ≤ n) : 0 < alphaOf n t := by
  unfold alphaOf; have : (1:ℝ) ≤ n := by exact_mod_cast hn
  positivity

theorem alpha_succ (n t : ℕ) (hn : 1 ≤ n) :
    4 * (n : ℝ) ^ 2 * alphaOf n (t + 1) = alphaOf n t := by
  unfold alphaOf
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hq0 : (4 * (n:ℝ) ^ 2) ≠ 0 := by positivity
  rw [pow_succ (4 * (n:ℝ) ^ 2) t, mul_inv, mul_comm ((4 * (n:ℝ) ^ 2) ^ t)⁻¹, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul]

theorem alpha_anti (n t₁ t₂ : ℕ) (hn : 1 ≤ n) (h : t₁ ≤ t₂) : alphaOf n t₂ ≤ alphaOf n t₁ := by
  unfold alphaOf
  have hq : (1 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by
    have : (1:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  apply inv_anti₀ (by positivity)
  exact pow_le_pow_right₀ hq h

theorem alpha_one (n : ℕ) (hn : 1 ≤ n) : alphaOf n 1 < 1 / (n : ℝ) := by
  unfold alphaOf
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  rw [pow_one, one_div]
  apply inv_strictAnti₀ (by positivity)
  nlinarith

end L5Aux

open L5Aux in
theorem solution {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 3 ≤ N.card) (X : ι → Piece) (R : Piece) (hX : ∀ i ∈ N, (X i).WF) (hR : R.WF)
    (hXdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (X i).toSet (X j).toSet)
    (hXR : ∀ i ∈ N, Disjoint (X i).toSet R.toSet)
    (hEF : EnvyFree V N (fun i => (X i).toSet)) (c : ι) (hc : c ∈ N)
    (s : Rec ι) (hs : s.Valid V N) (hXs : ∀ i ∈ N, s.Aligned (X i)) (hRs : s.Aligned R)
    (o : ChoiceOracle ι) (Y : ι → Piece) (U : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : exec V o (core N c R) s = some ((Y, U), s', tr))
    (hnone : ¬ ∃ E : Finset ι,
      IsDominatedGroup V N (fun i => (X i).toSet ∪ (Y i).toSet) U.toSet E) :
    (∀ i ∈ N, 0 < (V i).value U.toSet) ∧
    ∃ t : ℕ, 2 ≤ t ∧ t ≤ N.card + 1 ∧
      ∃ istar ∈ N, ∃ jstar ∈ N, istar ≠ jstar ∧
      ∃ π : ι → ι, Set.BijOn π (N : Set ι) (N : Set ι) ∧
        -- (S1)
        ¬ Dominates V (fun i => (X i).toSet) R.toSet istar jstar ∧
        -- (S2)
        (∀ i ∈ N, (V i).value (Y i).toSet - alphaOf N.card t * (V i).value U.toSet ≤
          (V i).value (Y (π i)).toSet) ∧
        -- (S3)
        (V istar).value (Y (π jstar)).toSet ≤ (V istar).value (Y istar).toSet -
          4 * (N.card : ℝ) ^ 2 * alphaOf N.card t * (V istar).value U.toSet := by
  classical
  -- properties of the Core run (Lemma 3)
  obtain ⟨Y', U', s'', tr', hex, hpa, hres, hEFY, hcut, -⟩ :=
    EnvyFreeCake104.Divide.lemma_3 V N (by omega) c hc R hR s hs hRs o
  rw [hrun] at hex
  simp only [Option.some.injEq, Prod.mk.injEq] at hex
  obtain ⟨⟨rfl, rfl⟩, -, -⟩ := hex
  set n := N.card with hn
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNne : N.Nonempty := Finset.card_pos.mp (by omega)
  -- notation
  have hmX : ∀ i, MeasurableSet (X i).toSet := fun i => piece_measurable _
  have hmY : ∀ i, MeasurableSet (Y i).toSet := fun i => piece_measurable _
  have hmU : MeasurableSet U.toSet := piece_measurable _
  have hmR : MeasurableSet R.toSet := piece_measurable _
  have hYR : ∀ i ∈ N, (Y i).toSet ⊆ R.toSet := hpa.1
  have hUR : U.toSet ⊆ R.toSet := by rw [hres]; exact Set.sdiff_subset
  have hXY : ∀ i ∈ N, ∀ j ∈ N, Disjoint (X i).toSet (Y j).toSet :=
    fun i hi j hj => Disjoint.mono_right (hYR j hj) (hXR i hi)
  have hvXY : ∀ k, ∀ i ∈ N, (V k).value ((X i).toSet ∪ (Y i).toSet) =
      (V k).value (X i).toSet + (V k).value (Y i).toSet :=
    fun k i hi => value_union (V k) (hmY i) (hXY i hi i hi)
  let u : ι → ℝ := fun i => (V i).value U.toSet
  have hu0 : ∀ i, 0 ≤ u i := fun i => value_nonneg _ hmU
  -- Step 1: every agent values the residue positively
  have hupos : ∀ i ∈ N, 0 < u i := by
    intro i hi
    by_contra hneg
    have hz : u i = 0 := le_antisymm (not_lt.mp hneg) (hu0 i)
    apply hnone
    refine ⟨N.erase i, Finset.erase_subset _ _, ?_, ?_, ?_⟩
    · exact Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hi]; omega)
    · intro h; have := Finset.mem_erase.mp (h ▸ hi); exact this.1 rfl
    · intro k hk hkE j hj
      have hki : k = i := by
        by_contra h; exact hkE (Finset.mem_erase.mpr ⟨h, hk⟩)
      subst hki
      have hjN := (Finset.mem_erase.mp hj).2
      show (V k).value ((X j).toSet ∪ (Y j).toSet) + (V k).value U.toSet ≤
        (V k).value ((X k).toSet ∪ (Y k).toSet)
      rw [hvXY k j hjN, hvXY k k hk]
      have := hEF k hk j hjN; have := hEFY k hk j hjN
      change u k = 0 at hz
      simp only [u] at hz
      linarith
  -- the domination graph and its cut property
  let G : ι → ι → Prop := fun a b =>
    a ∈ N ∧ b ∈ N ∧ a ≠ b ∧ ¬ Dominates V (fun i => (X i).toSet) R.toSet a b
  have hcutG : ∀ H : Finset ι, H ⊆ N → H.Nonempty → ∀ j0 ∈ N, j0 ∉ H →
      ∃ i ∈ H, ∃ j ∈ N, j ∉ H ∧ G i j := by
    intro H hH hHne j0 hj0 hj0H
    by_contra hcon
    push Not at hcon
    apply hnone
    refine ⟨N \ H, Finset.sdiff_subset, ⟨j0, Finset.mem_sdiff.mpr ⟨hj0, hj0H⟩⟩, ?_, ?_⟩
    · intro h
      obtain ⟨i, hi⟩ := hHne
      have : i ∈ N \ H := by rw [h]; exact hH hi
      exact (Finset.mem_sdiff.mp this).2 hi
    · intro i hi hiE j hj
      have hiH : i ∈ H := by
        by_contra h; exact hiE (Finset.mem_sdiff.mpr ⟨hi, h⟩)
      obtain ⟨hjN, hjH⟩ := Finset.mem_sdiff.mp hj
      have hdom : Dominates V (fun i => (X i).toSet) R.toSet i j := by
        by_contra hnd
        exact hcon i hiH j hjN hjH ⟨hi, hjN, fun h => hjH (h ▸ hiH), hnd⟩
      show (V i).value ((X j).toSet ∪ (Y j).toSet) + (V i).value U.toSet ≤
        (V i).value ((X i).toSet ∪ (Y i).toSet)
      rw [hvXY i j hjN, hvXY i i hi]
      have h1 := hEFY i hi j hjN
      have h2 := value_mono (V i) hUR hmR
      unfold Dominates at hdom
      linarith
  have hreach : ∀ a ∈ N, ∀ b ∈ N, Relation.ReflTransGen G a b := by
    intro a ha b hb
    by_contra hnr
    let H := N.filter (fun v => Relation.ReflTransGen G a v)
    obtain ⟨i, hiH, j, hjN, hjH, hij⟩ := hcutG H (Finset.filter_subset _ _)
      ⟨a, Finset.mem_filter.mpr ⟨ha, Relation.ReflTransGen.refl⟩⟩ b hb
      (fun h => hnr (Finset.mem_filter.mp h).2)
    exact hjH (Finset.mem_filter.mpr ⟨hjN, (Finset.mem_filter.mp hiH).2.tail hij⟩)
  -- normalized envy gaps
  let g : ι → ι → ℝ := fun i j => ((V i).value (Y i).toSet - (V i).value (Y j).toSet) / u i
  have hgii : ∀ i, g i i = 0 := fun i => by simp [g]
  have hg0 : ∀ i ∈ N, ∀ j ∈ N, 0 ≤ g i j := fun i hi j hj =>
    div_nonneg (by linarith [hEFY i hi j hj]) (hu0 i)
  have hS2iff : ∀ i ∈ N, ∀ j, ∀ a : ℝ, g i j ≤ a →
      (V i).value (Y i).toSet - a * u i ≤ (V i).value (Y j).toSet := by
    intro i hi j a h
    have := (div_le_iff₀ (hupos i hi)).mp h
    linarith
  have hS3iff : ∀ i ∈ N, ∀ j, ∀ a : ℝ, a ≤ g i j →
      (V i).value (Y j).toSet ≤ (V i).value (Y i).toSet - a * u i := by
    intro i hi j a h
    have := (le_div_iff₀ (hupos i hi)).mp h
    linarith
  set q : ℝ := 4 * (n : ℝ) ^ 2 with hq
  by_cases hcase : ∃ i j, G i j ∧ alphaOf n n ≤ g i j
  · -- Case 1
    obtain ⟨i, j, hG, hgij⟩ := hcase
    refine ⟨hupos, n + 1, by omega, le_rfl, i, hG.1, j, hG.2.1, hG.2.2.1, id, Set.bijOn_id _,
      hG.2.2.2, fun k hk => hS2iff k hk k _ (by rw [hgii]; exact (alpha_pos n _ hn1).le), ?_⟩
    have := hS3iff i hG.1 j (q * alphaOf n (n + 1)) (by rw [hq, alpha_succ n _ hn1]; exact hgij)
    simpa [mul_assoc] using this
  · -- Case 2
    push Not at hcase
    -- a heavily envied piece for the cutter
    have hsum : ∑ j ∈ N, g c j = 1 := by
      have hpart : R.toSet = (⋃ j ∈ N, (Y j).toSet) ∪ U.toSet := by
        rw [hres]; exact (Set.union_sdiff_cancel (Set.iUnion₂_subset hYR)).symm
      have hdisj : Disjoint (⋃ j ∈ N, (Y j).toSet) U.toSet := by
        rw [hres]; exact Set.disjoint_sdiff_right
      have hVR : (V c).value R.toSet = ∑ j ∈ N, (V c).value (Y j).toSet + u c := by
        rw [hpart, value_union (V c) hmU hdisj, value_biUnion (V c) _ N (fun j _ => hmY j) hpa.2]
      have hnR : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      rw [← Finset.sum_div, div_eq_one_iff_eq (ne_of_gt (hupos c hc)), Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, hcut, mul_div_cancel₀ _ hnR, hVR]
      simp only [u]; ring
    obtain ⟨jh, hjhN, hjh⟩ : ∃ j ∈ N, 1 / (n : ℝ) ≤ g c j := by
      apply Finset.exists_le_of_sum_le hNne
      rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_one_div_cancel (ne_of_gt hnpos)]
    have hgc_big : alphaOf n 1 < g c jh := lt_of_lt_of_le (alpha_one n hn1) hjh
    have hjhc : jh ≠ c := by rintro rfl; rw [hgii] at hgc_big; linarith [alpha_pos n 1 hn1]
    -- pigeonhole over the scales
    obtain ⟨ts, htsI, hgap⟩ : ∃ ts ∈ Finset.Icc 1 (n - 1), ∀ i ∈ N,
        ¬ (alphaOf n (ts + 1) < g i jh ∧ g i jh ≤ alphaOf n ts) := by
      by_contra hcon
      push Not at hcon
      choose f hfN hf using hcon
      have hmaps : ∀ t (ht : t ∈ Finset.Icc 1 (n - 1)), f t ht ∈ (N.erase c).erase jh := by
        intro t ht
        have h := hf t ht
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hfN t ht⟩⟩
        · intro he; rw [he, hgii] at h; linarith [alpha_pos n (t + 1) hn1]
        · intro he; rw [he] at h
          have := alpha_anti n 1 t hn1 (Finset.mem_Icc.mp ht).1
          linarith [h.2]
      let F : ℕ → ι := fun t => if ht : t ∈ Finset.Icc 1 (n - 1) then f t ht else c
      have hcard := Finset.card_le_card_of_injOn (s := Finset.Icc 1 (n - 1))
        (t := (N.erase c).erase jh) F
        (fun t ht => by
          have ht' : t ∈ Finset.Icc 1 (n - 1) := by simpa using ht
          have := hmaps t ht'
          simp only [F, dif_pos ht']
          exact Finset.mem_coe.mpr this)
        (by
          intro t₁ ht₁ t₂ ht₂ he
          simp only [F, dif_pos (Finset.mem_coe.mp ht₁), dif_pos (Finset.mem_coe.mp ht₂)] at he
          have h1 := hf t₁ ht₁; have h2 := hf t₂ ht₂
          rw [he] at h1
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
          · have := alpha_anti n (t₁ + 1) t₂ hn1 hlt; linarith [h1.1, h2.2]
          · have := alpha_anti n (t₂ + 1) t₁ hn1 hlt; linarith [h1.2, h2.1])
      rw [Nat.card_Icc, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hjhc, hjhN⟩),
        Finset.card_erase_of_mem hc] at hcard
      omega
    obtain ⟨hts1, htsn⟩ := Finset.mem_Icc.mp htsI
    set α := alphaOf n (ts + 1) with hα
    have hαq : q * α = alphaOf n ts := by rw [hq, hα, alpha_succ n _ hn1]
    have hαlow : alphaOf n n ≤ α := alpha_anti n (ts + 1) n hn1 (by omega)
    let H := N.filter (fun i => α < g i jh)
    have hHbig : ∀ i ∈ H, q * α < g i jh := by
      intro i hi
      obtain ⟨hiN, hgi⟩ := Finset.mem_filter.mp hi
      rw [hαq]
      by_contra hle
      exact hgap i hiN ⟨hgi, not_lt.mp hle⟩
    have hcH : c ∈ H := Finset.mem_filter.mpr ⟨hc,
      lt_of_le_of_lt (alpha_anti n 1 (ts + 1) hn1 (by omega)) hgc_big⟩
    have hjhH : jh ∉ H := by
      intro h; have := (Finset.mem_filter.mp h).2; rw [hgii] at this
      linarith [alpha_pos n (ts + 1) hn1]
    obtain ⟨is, hisH, js, hjsN, hjsH, hG⟩ :=
      hcutG H (Finset.filter_subset _ _) ⟨c, hcH⟩ jh hjhN hjhH
    have hisN : is ∈ N := (Finset.mem_filter.mp hisH).1
    have hjsL : g js jh ≤ α := by
      by_contra h; exact hjsH (Finset.mem_filter.mpr ⟨hjsN, not_le.mp h⟩)
    have hgis := hHbig is hisH
    have hjsjh : js ≠ jh := by
      rintro rfl
      have h1 := hcase is js hG
      have h2 := alpha_anti n ts n hn1 (by omega)
      rw [← hαq] at h2
      linarith
    -- a simple path from jh to js, rotated
    obtain ⟨l, hnd, hhd, hlast, hch⟩ := simple_path G jh js (hreach jh hjhN js hjsN)
    have hlne : l ≠ [] := by intro h; rw [h] at hhd; simp at hhd
    have hlen : 0 < l.length := List.length_pos_of_ne_nil hlne
    have hl0 : l[0] = jh := by
      rw [List.head?_eq_getElem?] at hhd
      exact (List.getElem?_eq_some_iff.mp hhd).2
    have hlL : l[l.length - 1] = js := by
      rw [List.getLast?_eq_getElem?] at hlast
      exact (List.getElem?_eq_some_iff.mp hlast).2
    have hedge : ∀ k (hk : k + 1 < l.length), G l[k] l[k + 1] :=
      fun k hk => List.isChain_iff_getElem.mp hch k hk
    have hlN : ∀ a ∈ l, a ∈ N := by
      intro a ha
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      by_cases hk' : k + 1 < l.length
      · exact (hedge k hk').1
      · have : k = l.length - 1 := by omega
        subst this; rw [hlL]; exact hjsN
    set π := l.formPerm with hπ
    have hπfix : ∀ a, a ∉ l → π a = a := fun a ha => List.formPerm_apply_of_notMem ha
    have hπjs : π js = jh := by
      rw [← hlL, hπ, List.formPerm_apply_getElem l hnd _ (by omega)]
      simp only [Nat.sub_add_cancel hlen, Nat.mod_self]; exact hl0
    have hπedge : ∀ a ∈ l, a ≠ js → G a (π a) := by
      intro a ha hajs
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      have hk' : k + 1 < l.length := by
        by_contra h
        have : k = l.length - 1 := by omega
        subst this; exact hajs hlL
      rw [hπ, List.formPerm_apply_getElem l hnd k hk]
      have e : (k + 1) % l.length = k + 1 := Nat.mod_eq_of_lt hk'
      simp only [e]
      exact hedge k hk'
    refine ⟨hupos, ts + 1, by omega, by omega, is, hisN, js, hjsN, hG.2.2.1, π,
      perm_bijOn N π (fun a ha => hπfix a (fun h => ha (hlN a h))), hG.2.2.2, ?_, ?_⟩
    · intro i hi
      apply hS2iff i hi
      by_cases hil : i ∈ l
      · by_cases hijs : i = js
        · subst hijs; rw [hπjs]; exact hjsL
        · exact ((hcase i (π i) (hπedge i hil hijs)).le).trans hαlow
      · rw [hπfix i hil, hgii]; exact (alpha_pos n _ hn1).le
    · rw [hπjs]
      have := hS3iff is hisN jh (q * α) hgis.le
      simpa [mul_assoc] using this
