-- Prove2me | solution 1 for CountingLLL.DetCount.marginal_expansion_eq11
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:28:37.2522+00:00
-- url     : https://prove2.me/submissions/976dbd13-39dd-49fc-a51b-6067174b336a

import Theorems.Thm_CountingLLL_DetCount_lemma_3_4
import Theorems.Thm_CountingLLL_DetCount_lemma_3_2
import Theorems.Thm_CountingLLL_DetCount_condition11_partition_positive

set_option autoImplicit false
open scoped Classical

open CountingLLL.DetCount
open CountingLLL.DetCount.CSP

set_option autoImplicit false

/-- A finite product of consecutive nonzero ratios telescopes, including the empty product. -/
theorem telescoping_nonzero_ratios (f : ℕ → ℝ) (n : ℕ)
    (hf : ∀ i ≤ n, f i ≠ 0) :
    (∏ i ∈ Finset.range n, f i / f (i + 1)) = f 0 / f n := by
  induction n with
  | zero =>
    simp [hf 0 (by omega)]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih (fun i hi => hf i (by omega))]
    have h : f n ≠ 0 := hf n (by omega)
    field_simp

/-- The numerical telescoping identity in the form used by the marginal expansion. -/
theorem reciprocal_marginal_telescope (f : ℕ → ℝ) (n : ℕ)
    (hf : ∀ i ≤ n, f i ≠ 0) :
    (∏ j : Fin n, 1 / (1 - (1 - f (j.val + 1) / f j.val))) = f 0 / f n := by
  simp only [sub_sub_cancel, one_div_div]
  calc
    _ = ∏ i ∈ Finset.range n, f i / f (i + 1) :=
      Fin.prod_univ_eq_prod_range (fun i : ℕ => f i / f (i + 1)) n
    _ = f 0 / f n := telescoping_nonzero_ratios f n hf


namespace CountingLLL.DetCount
open CSP

/-- The free constraints of a rooted 2-tree form a subset of the family with its root removed. -/
theorem free_subset_erase (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (T : Finset (Fin Φ.m)) (hT : T ∈ Φ.twoTrees E c₀) :
    Φ.free E c₀ T ⊆ E.erase c₀ := by
  classical
  have hroot : c₀ ∈ T := (Finset.mem_filter.mp hT).2.1
  intro c hc
  have hd := Finset.mem_sdiff.mp hc
  apply Finset.mem_erase.mpr
  refine ⟨?_, hd.1⟩
  intro heq
  subst c
  exact hd.2 (Finset.mem_union.mpr (Or.inl hroot))

/-- The rest set is exactly the complement of free constraints in the root-deleted family. -/
theorem rest_eq_erase_sdiff_free (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (T : Finset (Fin Φ.m)) :
    Φ.rest E c₀ T = (E.erase c₀) \ Φ.free E c₀ T := by
  classical
  ext c
  simp [CSP.rest, and_assoc, and_left_comm, and_comm]

/-- Every injective enumeration of the prescribed length whose values lie in `rest` is onto. -/
theorem enum_rest_onto (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (T : Finset (Fin Φ.m)) (e : Fin (Φ.ell E c₀ T) → Fin Φ.m)
    (he : Function.Injective e ∧ ∀ j, e j ∈ Φ.rest E c₀ T) :
    Finset.univ.image e = Φ.rest E c₀ T := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
    exact he.2 j
  · rw [Finset.card_image_of_injective _ he.1]
    change (Φ.rest E c₀ T).card ≤ (Finset.univ : Finset (Fin (Φ.ell E c₀ T))).card
    rw [Finset.card_fin]
    exact le_rfl

private noncomputable def basePrefix (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (T : Finset (Fin Φ.m)) (e : Fin (Φ.ell E c₀ T) → Fin Φ.m) (i : ℕ) :
    Finset (Fin Φ.m) :=
  Φ.free E c₀ T ∪ (Finset.univ.filter (fun j : Fin (Φ.ell E c₀ T) => j.val < i)).image e

private theorem basePrefix_zero (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (T : Finset (Fin Φ.m)) (e : Fin (Φ.ell E c₀ T) → Fin Φ.m) :
    basePrefix Φ E c₀ T e 0 = Φ.free E c₀ T := by
  classical
  simp [basePrefix]

private theorem basePrefix_succ (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (T : Finset (Fin Φ.m)) (e : Fin (Φ.ell E c₀ T) → Fin Φ.m) (i : Fin (Φ.ell E c₀ T)) :
    basePrefix Φ E c₀ T e (i.val + 1) = insert (e i) (basePrefix Φ E c₀ T e i.val) := by
  classical
  ext c
  simp only [basePrefix, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro (hfree | ⟨j, hj, rfl⟩)
    · exact Or.inr (Or.inl hfree)
    · have hj' : j.val ≤ i.val := Nat.lt_succ_iff.mp hj
      rcases eq_or_lt_of_le hj' with h | h
      · left; congr 1; exact Fin.ext h
      · exact Or.inr (Or.inr ⟨j, h, rfl⟩)
  · rintro (rfl | hfree | ⟨j, hj, rfl⟩)
    · exact Or.inr ⟨i, Nat.lt_succ_self _, rfl⟩
    · exact Or.inl hfree
    · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, rfl⟩

private theorem basePrefix_fresh (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (T : Finset (Fin Φ.m)) (e : Fin (Φ.ell E c₀ T) → Fin Φ.m)
    (he : Function.Injective e ∧ ∀ j, e j ∈ Φ.rest E c₀ T)
    (i : Fin (Φ.ell E c₀ T)) : e i ∉ basePrefix Φ E c₀ T e i.val := by
  classical
  simp only [basePrefix, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, not_or, not_exists]
  constructor
  · exact (Finset.mem_sdiff.mp (he.2 i)).2 ∘ Finset.mem_union.mpr ∘ Or.inr
  · intro j hj
    have hh : j = i := he.1 hj.2
    subst j
    exact Nat.lt_irrefl _ hj.1

private theorem basePrefix_erase (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (T : Finset (Fin Φ.m)) (e : Fin (Φ.ell E c₀ T) → Fin Φ.m)
    (he : Function.Injective e ∧ ∀ j, e j ∈ Φ.rest E c₀ T)
    (i : Fin (Φ.ell E c₀ T)) :
    (basePrefix Φ E c₀ T e (i.val + 1)).erase (e i) = basePrefix Φ E c₀ T e i.val := by
  classical
  rw [basePrefix_succ]
  simp [basePrefix_fresh Φ E c₀ T e he]

private theorem basePrefix_full (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (T : Finset (Fin Φ.m)) (hT : T ∈ Φ.twoTrees E c₀)
    (e : Fin (Φ.ell E c₀ T) → Fin Φ.m)
    (he : Function.Injective e ∧ ∀ j, e j ∈ Φ.rest E c₀ T) :
    basePrefix Φ E c₀ T e (Φ.ell E c₀ T) = E.erase c₀ := by
  classical
  have hU : Finset.univ.filter (fun j : Fin (Φ.ell E c₀ T) => j.val < Φ.ell E c₀ T) = Finset.univ := by
    ext j; simp [j.isLt]
  rw [basePrefix, hU, enum_rest_onto Φ E c₀ T e he, rest_eq_erase_sdiff_free]
  exact Finset.union_sdiff_of_subset (free_subset_erase Φ E c₀ T hT)

private theorem basePrefix_mono (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (T : Finset (Fin Φ.m)) (e : Fin (Φ.ell E c₀ T) → Fin Φ.m) {i j : ℕ} (h : i ≤ j) :
    basePrefix Φ E c₀ T e i ⊆ basePrefix Φ E c₀ T e j := by
  classical
  unfold basePrefix
  apply Finset.union_subset_union_right
  apply Finset.image_mono
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact lt_of_lt_of_le hx h

private theorem prefix_is_base_succ (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (T : Finset (Fin Φ.m)) (e : Fin (Φ.ell E c₀ T) → Fin Φ.m)
    (i : Fin (Φ.ell E c₀ T)) :
    Φ.prefixFam (Φ.free E c₀ T) e i = basePrefix Φ E c₀ T e (i.val+1) := by
  classical
  unfold CSP.prefixFam basePrefix
  congr 1
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => Nat.lt_succ_of_le h, fun h => Nat.le_of_lt_succ h⟩

private theorem z_antitone (Φ : CSP) {E F : Finset (Fin Φ.m)} (h : E ⊆ F) : Φ.Z F ≤ Φ.Z E := by
  classical
  apply Finset.card_le_card
  intro σ hσ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  intro c hc
  exact hσ c (h hc)

/-- The source's telescoping identity under the sole semantic hypothesis that the
root-deleted family has a satisfying assignment. Condition 1.1 supplies this via LLL. -/
theorem probability_ratio_telescope_of_pos (Φ : CSP)
    (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (T : Finset (Fin Φ.m)) (hT : T ∈ Φ.twoTrees E c₀)
    (e : Fin (Φ.ell E c₀ T) → Fin Φ.m)
    (he : Function.Injective e ∧ ∀ j, e j ∈ Φ.rest E c₀ T)
    (hpos : 0 < Φ.Z (E.erase c₀)) :
    Φ.prob (Φ.SatAll (Φ.free E c₀ T)) / Φ.prob (Φ.SatAll (E.erase c₀)) =
      ∏ j : Fin (Φ.ell E c₀ T),
        1 / (1 - Φ.r (Φ.prefixFam (Φ.free E c₀ T) e j) (e j)) := by
  classical
  let f : ℕ → ℝ := fun i => (Φ.Z (basePrefix Φ E c₀ T e i) : ℝ)
  have hf : ∀ i ≤ Φ.ell E c₀ T, f i ≠ 0 := by
    intro i hi
    have hz := z_antitone Φ (basePrefix_mono Φ E c₀ T e hi)
    rw [basePrefix_full Φ E c₀ T hT e he] at hz
    have hp : 0 < Φ.Z (basePrefix Φ E c₀ T e i) := lt_of_lt_of_le hpos hz
    change (Φ.Z (basePrefix Φ E c₀ T e i) : ℝ) ≠ 0
    exact_mod_cast (ne_of_gt hp)
  have hc : (Fintype.card Φ.Config : ℝ) ≠ 0 := by
    letI : Nonempty Φ.Config := ⟨fun v => ⟨0, lt_of_lt_of_le (by decide) (Φ.two_le_q v)⟩⟩
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card Φ.Config))
  have hleft : Φ.prob (Φ.SatAll (Φ.free E c₀ T)) / Φ.prob (Φ.SatAll (E.erase c₀)) =
      f 0 / f (Φ.ell E c₀ T) := by
    change ((Φ.Z (Φ.free E c₀ T) : ℝ) / (Fintype.card Φ.Config : ℝ)) /
      ((Φ.Z (E.erase c₀) : ℝ) / (Fintype.card Φ.Config : ℝ)) = _
    rw [div_div_div_cancel_right₀ hc]
    simp only [f, basePrefix_zero, basePrefix_full Φ E c₀ T hT e he]
  rw [hleft, ← reciprocal_marginal_telescope f (Φ.ell E c₀ T) hf]
  apply Finset.prod_congr rfl
  intro j hj
  rw [prefix_is_base_succ, CSP.r, basePrefix_erase Φ E c₀ T e he j]

end CountingLLL.DetCount

private theorem alternating_powerset {α : Type*} [DecidableEq α] (B : Finset α) :
    (∑ S ∈ B.powerset, (-1 : ℝ) ^ S.card) = if B = ∅ then 1 else 0 := by
  have h := Finset.prod_one_add (R := ℝ) (f := fun _ : α => -1) B
  simp only [Finset.prod_const, add_neg_cancel, one_pow] at h
  by_cases hB : B = ∅
  · subst B; simp
  · rw [if_neg hB]
    have hcard : B.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hB)
    simpa [hcard] using h.symm

private theorem rooted_alternating {α : Type*} [DecidableEq α] (B : Finset α) (r : α)
    (hr : r ∈ B) :
    (∑ D ∈ B.powerset.filter (r ∈ ·), (-1 : ℝ) ^ (D.card - 1)) =
      if B = {r} then 1 else 0 := by
  have himage : B.powerset.filter (r ∈ ·) = (B.erase r).powerset.image (insert r) := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hDB, hrD⟩
      refine ⟨D.erase r, ?_, ?_⟩
      · intro x hx
        have hx' := Finset.mem_erase.mp hx
        exact Finset.mem_erase.mpr ⟨hx'.1, hDB hx'.2⟩
      · exact Finset.insert_erase hrD
    · rintro ⟨S, hS, rfl⟩
      constructor
      · exact Finset.insert_subset hr (hS.trans (Finset.erase_subset r B))
      · simp
  rw [himage]
  rw [Finset.sum_image]
  · have hs : ∀ S ⊆ B.erase r, r ∉ S := by
      intro S hS hrS
      exact (Finset.mem_erase.mp (hS hrS)).1 rfl
    calc
      _ = ∑ S ∈ (B.erase r).powerset, (-1 : ℝ) ^ S.card := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.card_insert_of_notMem (hs S (Finset.mem_powerset.mp hS))]
        simp
      _ = if B.erase r = ∅ then 1 else 0 := alternating_powerset _
      _ = if B = {r} then 1 else 0 := by
        have hn : B ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨r, hr⟩
        simp [Finset.erase_eq_empty_iff, hn]
  · intro S hS U hU h
    have hS' : r ∉ S := fun hrS => (Finset.mem_erase.mp ((Finset.mem_powerset.mp hS) hrS)).1 rfl
    have hU' : r ∉ U := fun hrU => (Finset.mem_erase.mp ((Finset.mem_powerset.mp hU) hrU)).1 rfl
    have h' := congrArg (Finset.erase · r) h
    simpa [hS', hU'] using h'

private theorem tree_fiber (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (hr : r ∈ E)
    (B T : Finset (Fin Φ.m)) (hBE : B ⊆ E) (hT : T ∈ Φ.twoTrees E r) :
    (B.powerset.filter (r ∈ ·)).filter (fun D => Φ.Tree E r D = T) =
      if T ⊆ B then ((B ∩ Φ.free E r T).powerset.image (fun S => S ∪ T)) else ∅ := by
  classical
  have hinv := lemma_3_4 Φ E r hr T hT
  by_cases hTB : T ⊆ B
  · rw [if_pos hTB]
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨⟨hDB, hrD⟩, htree⟩
      have hl : D ⊆ E ∧ r ∈ D ∧ Φ.Tree E r D = T := ⟨hDB.trans hBE, hrD, htree⟩
      have hex : ∃ S ⊆ Φ.free E r T, D = S ∪ T := by
        have hh := Set.ext_iff.mp hinv D
        exact hh.mp hl
      obtain ⟨S, hS, hD⟩ := hex
      refine ⟨S, ?_, hD.symm⟩
      intro c hc
      exact Finset.mem_inter.mpr ⟨hDB (hD ▸ Finset.mem_union_left T hc), hS hc⟩
    · rintro ⟨S, hS, rfl⟩
      have hfree : S ⊆ Φ.free E r T := fun c hc => (Finset.mem_inter.mp (hS hc)).2
      have hl : S ∪ T ⊆ E ∧ r ∈ S ∪ T ∧ Φ.Tree E r (S ∪ T) = T := by
        have hh := Set.ext_iff.mp hinv (S ∪ T)
        exact hh.mpr ⟨S, hfree, rfl⟩
      refine ⟨⟨?_, hl.2.1⟩, hl.2.2⟩
      exact Finset.union_subset (fun c hc => (Finset.mem_inter.mp (hS hc)).1) hTB
  · rw [if_neg hTB]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro D hD
    have hd := Finset.mem_filter.mp hD
    have hb := Finset.mem_filter.mp hd.1
    have hDE : D ⊆ E := (Finset.mem_powerset.mp hb.1).trans hBE
    have hin := (Set.ext_iff.mp hinv D).mp ⟨hDE, hb.2, hd.2⟩
    obtain ⟨S, _, hST⟩ := hin
    apply hTB
    rw [hST] at hb
    exact Finset.subset_union_right.trans (Finset.mem_powerset.mp hb.1)

private theorem free_disjoint_tree (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m) :
    Disjoint (Φ.free E r T) T := by
  classical
  apply Finset.disjoint_left.mpr
  intro c hc ht
  exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_union.mpr (Or.inl ht))

private theorem fiber_alternating (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (hr : r ∈ E)
    (B T : Finset (Fin Φ.m)) (hBE : B ⊆ E) (hT : T ∈ Φ.twoTrees E r) :
    (∑ D ∈ (B.powerset.filter (r ∈ ·)).filter (fun D => Φ.Tree E r D = T),
      (-1 : ℝ) ^ (D.card - 1)) =
      if T ⊆ B ∧ B ⊆ T ∪ Φ.rejected E r T then (-1 : ℝ) ^ (T.card - 1) else 0 := by
  classical
  rw [tree_fiber Φ E r hr B T hBE hT]
  by_cases hTB : T ⊆ B
  · rw [if_pos hTB]
    have ht : 1 ≤ T.card := Finset.card_pos.mpr ⟨r, (Finset.mem_filter.mp hT).2.1⟩
    let F := B ∩ Φ.free E r T
    have hdis : Disjoint F T := (free_disjoint_tree Φ E T r).mono_left Finset.inter_subset_right
    have hinj : Set.InjOn (fun S : Finset (Fin Φ.m) => S ∪ T) ↑F.powerset := by
      intro S hS U hU heq
      have hST : Disjoint S T := hdis.mono_left (Finset.mem_powerset.mp hS)
      have hUT : Disjoint U T := hdis.mono_left (Finset.mem_powerset.mp hU)
      ext x
      have hmem := congrArg (fun Z : Finset (Fin Φ.m) => x ∈ Z) heq
      simp only [Finset.mem_union] at hmem
      have hs : x ∈ S → x ∉ T := fun hs ht => Finset.disjoint_left.mp hST hs ht
      have hu : x ∈ U → x ∉ T := fun hu ht => Finset.disjoint_left.mp hUT hu ht
      tauto
    rw [Finset.sum_image hinj]
    have hpow : ∀ S ∈ F.powerset, (-1 : ℝ) ^ ((S ∪ T).card - 1) =
        (-1 : ℝ) ^ (T.card - 1) * (-1 : ℝ) ^ S.card := by
      intro S hS
      have hst : Disjoint S T := hdis.mono_left (Finset.mem_powerset.mp hS)
      rw [Finset.card_union_of_disjoint hst]
      have heq : S.card + T.card - 1 = (T.card - 1) + S.card := by omega
      rw [heq, pow_add]
    rw [Finset.sum_congr rfl hpow, ← Finset.mul_sum, alternating_powerset]
    have hiff : F = ∅ ↔ B ⊆ T ∪ Φ.rejected E r T := by
      constructor
      · intro hF c hc
        by_contra hn
        have hmem : c ∈ F := Finset.mem_inter.mpr ⟨hc, Finset.mem_sdiff.mpr ⟨hBE hc, hn⟩⟩
        rw [hF] at hmem
        exact Finset.notMem_empty c hmem
      · intro hsub
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro c hc
        have hm := Finset.mem_inter.mp hc
        exact (Finset.mem_sdiff.mp hm.2).2 (hsub hm.1)
    simp only [hTB, true_and]
    simp only [hiff]
    split_ifs <;> simp
  · rw [if_neg hTB]
    simp [hTB]

/-- The pointwise canonical 2-tree inversion, equation (10) in the source. -/
theorem canonical_tree_pointwise (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (hr : r ∈ E)
    (B : Finset (Fin Φ.m)) (hBE : B ⊆ E) :
    (∑ T ∈ Φ.twoTrees E r,
      if T ⊆ B ∧ B ⊆ T ∪ Φ.rejected E r T then (-1 : ℝ) ^ (T.card - 1) else 0) =
      if B = {r} then 1 else 0 := by
  classical
  by_cases hrB : r ∈ B
  · have hmap : ∀ D ∈ B.powerset.filter (r ∈ ·), Φ.Tree E r D ∈ Φ.twoTrees E r := by
      intro D hD
      have hh := Finset.mem_filter.mp hD
      exact (lemma_3_2 Φ E r).1 D hh.2 ((Finset.mem_powerset.mp hh.1).trans hBE)
    calc
      _ = ∑ T ∈ Φ.twoTrees E r,
          ∑ D ∈ (B.powerset.filter (r ∈ ·)).filter (fun D => Φ.Tree E r D = T),
            (-1 : ℝ) ^ (D.card - 1) := by
          apply Finset.sum_congr rfl
          intro T hT
          exact (fiber_alternating Φ E r hr B T hBE hT).symm
      _ = ∑ D ∈ B.powerset.filter (r ∈ ·), (-1 : ℝ) ^ (D.card - 1) :=
          Finset.sum_fiberwise_of_maps_to hmap _
      _ = _ := rooted_alternating B r hrB
  · have hBr : B ≠ {r} := by intro h; rw [h] at hrB; simp at hrB
    rw [if_neg hBr]
    apply Finset.sum_eq_zero
    intro T hT
    have hTr : r ∈ T := (Finset.mem_filter.mp hT).2.1
    have hnot : ¬ T ⊆ B := fun ht => hrB (ht hTr)
    simp [hnot]

private noncomputable def violated (Φ : CSP) (E : Finset (Fin Φ.m)) (σ : Φ.Config) : Finset (Fin Φ.m) :=
  by
    classical
    exact E.filter (fun c => ¬ Φ.Sat c σ)

private theorem mem_violated (Φ : CSP) (E : Finset (Fin Φ.m)) (σ : Φ.Config) (c : Fin Φ.m) :
    c ∈ violated Φ E σ ↔ c ∈ E ∧ ¬ Φ.Sat c σ := by
  classical
  simp [violated]

private theorem violated_subset (Φ : CSP) (E : Finset (Fin Φ.m)) (σ : Φ.Config) :
    violated Φ E σ ⊆ E := by
  classical
  intro c hc
  exact ((mem_violated Φ E σ c).mp hc).1

private theorem singleton_violated_iff (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hr : r ∈ E) (σ : Φ.Config) :
    violated Φ E σ = {r} ↔ ¬ Φ.Sat r σ ∧ Φ.SatAll (E.erase r) σ := by
  classical
  constructor
  · intro h
    constructor
    · have hh : r ∈ violated Φ E σ := by rw [h]; simp
      exact ((mem_violated Φ E σ r).mp hh).2
    · intro c hc
      by_contra hn
      have hh : c ∈ violated Φ E σ := (mem_violated Φ E σ c).mpr ⟨(Finset.mem_erase.mp hc).2, hn⟩
      rw [h] at hh
      exact (Finset.mem_erase.mp hc).1 (Finset.mem_singleton.mp hh)
  · rintro ⟨hrbad, hgood⟩
    ext c
    simp only [violated, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, hn⟩
      by_contra hne
      exact hn (hgood c (Finset.mem_erase.mpr ⟨hne, hc⟩))
    · intro hc
      subst c
      exact ⟨hr, hrbad⟩

private theorem tree_event_iff (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (T : Finset (Fin Φ.m)) (hT : T ∈ Φ.twoTrees E r) (σ : Φ.Config) :
    (T ⊆ violated Φ E σ ∧ violated Φ E σ ⊆ T ∪ Φ.rejected E r T) ↔
      (Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free E r T) σ) := by
  classical
  have hTE : T ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  constructor
  · rintro ⟨htbad, hcover⟩
    constructor
    · intro c hc
      exact ((mem_violated Φ E σ c).mp (htbad hc)).2
    · intro c hc
      by_contra hn
      have hcbad : c ∈ violated Φ E σ := (mem_violated Φ E σ c).mpr ⟨(Finset.mem_sdiff.mp hc).1, hn⟩
      exact (Finset.mem_sdiff.mp hc).2 (hcover hcbad)
  · rintro ⟨htbad, hfree⟩
    constructor
    · intro c hc
      exact (mem_violated Φ E σ c).mpr ⟨hTE hc, htbad c hc⟩
    · intro c hc
      by_contra hn
      have hh := (mem_violated Φ E σ c).mp hc
      have hf : c ∈ Φ.free E r T := Finset.mem_sdiff.mpr ⟨hh.1, hn⟩
      exact hh.2 (hfree c hf)

private theorem pointwise_assignment (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hr : r ∈ E) (σ : Φ.Config) :
    (∑ T ∈ Φ.twoTrees E r,
      if Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free E r T) σ then (-1 : ℝ) ^ (T.card - 1) else 0) =
      if ¬ Φ.Sat r σ ∧ Φ.SatAll (E.erase r) σ then 1 else 0 := by
  classical
  have h := canonical_tree_pointwise Φ E r hr (violated Φ E σ) (violated_subset Φ E σ)
  have ht : (∑ T ∈ Φ.twoTrees E r,
      if T ⊆ violated Φ E σ ∧ violated Φ E σ ⊆ T ∪ Φ.rejected E r T
        then (-1 : ℝ) ^ (T.card - 1) else 0) =
      ∑ T ∈ Φ.twoTrees E r,
        if Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free E r T) σ then (-1 : ℝ) ^ (T.card - 1) else 0 := by
    apply Finset.sum_congr rfl
    intro T hT
    simp only [tree_event_iff Φ E r T hT σ]
  rw [ht] at h
  simp only [singleton_violated_iff Φ E r hr σ] at h
  exact h

private theorem prob_as_indicator (Φ : CSP) (A : Φ.Config → Prop) :
    Φ.prob A = (∑ σ : Φ.Config, if A σ then (1 : ℝ) else 0) / Fintype.card Φ.Config := by
  classical
  unfold CSP.prob
  congr 1
  simp [Finset.sum_ite]

/-- The unnormalized expectation of source equation (10), before conditioning. -/
theorem unconditioned_tree_expansion (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hr : r ∈ E) :
    Φ.prob (fun σ => ¬ Φ.Sat r σ ∧ Φ.SatAll (E.erase r) σ) =
      ∑ T ∈ Φ.twoTrees E r, (-1 : ℝ) ^ (T.card - 1) *
        Φ.prob (fun σ => Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free E r T) σ) := by
  classical
  have hcount : (∑ σ : Φ.Config,
      if ¬ Φ.Sat r σ ∧ Φ.SatAll (E.erase r) σ then (1 : ℝ) else 0) =
      ∑ T ∈ Φ.twoTrees E r, (-1 : ℝ) ^ (T.card - 1) *
        ∑ σ : Φ.Config, if Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free E r T) σ then (1 : ℝ) else 0 := by
    calc
      _ = ∑ σ : Φ.Config, ∑ T ∈ Φ.twoTrees E r,
          if Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free E r T) σ then (-1 : ℝ) ^ (T.card - 1) else 0 := by
          apply Finset.sum_congr rfl
          intro σ hσ
          exact (pointwise_assignment Φ E r hr σ).symm
      _ = ∑ T ∈ Φ.twoTrees E r, ∑ σ : Φ.Config,
          if Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free E r T) σ then (-1 : ℝ) ^ (T.card - 1) else 0 :=
          Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro σ hσ
        split_ifs <;> simp_all
  simp only [prob_as_indicator, ← mul_div_assoc, ← Finset.sum_div]
  congr 1
  convert hcount using 1
  · apply Finset.sum_congr rfl
    intro σ hσ
    by_cases h : ¬ Φ.Sat r σ ∧ Φ.SatAll (E.erase r) σ <;> simp [h]
  · apply Finset.sum_congr rfl
    intro T hT
    congr 1
    apply Finset.sum_congr rfl
    intro σ hσ
    by_cases h : Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free E r T) σ <;> simp [h]

private theorem satall_decompose (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hr : r ∈ E) (σ : Φ.Config) :
    Φ.SatAll E σ ↔ Φ.Sat r σ ∧ Φ.SatAll (E.erase r) σ := by
  classical
  constructor
  · intro h
    exact ⟨h r hr, fun c hc => h c (Finset.mem_of_mem_erase hc)⟩
  · rintro ⟨hrsat, hrest⟩ c hc
    by_cases hcr : c = r
    · subst c; exact hrsat
    · exact hrest c (Finset.mem_erase.mpr ⟨hcr, hc⟩)

private theorem probability_partition (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hr : r ∈ E) :
    Φ.prob (Φ.SatAll E) + Φ.prob (fun σ => ¬ Φ.Sat r σ ∧ Φ.SatAll (E.erase r) σ) =
      Φ.prob (Φ.SatAll (E.erase r)) := by
  classical
  simp only [prob_as_indicator, ← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  have h := satall_decompose Φ E r hr σ
  by_cases h1 : Φ.Sat r σ <;> by_cases h2 : Φ.SatAll (E.erase r) σ <;> simp [h1, h2, h]

private theorem card_config_nonzero (Φ : CSP) : (Fintype.card Φ.Config : ℝ) ≠ 0 := by
  letI : Nonempty Φ.Config := ⟨fun v => ⟨0, lt_of_lt_of_le (by decide) (Φ.two_le_q v)⟩⟩
  exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card Φ.Config))

private theorem prob_satall (Φ : CSP) (E : Finset (Fin Φ.m)) :
    Φ.prob (Φ.SatAll E) = (Φ.Z E : ℝ) / Fintype.card Φ.Config := by rfl

private theorem prob_satall_ne_zero (Φ : CSP) (E : Finset (Fin Φ.m)) (h : 0 < Φ.Z E) :
    Φ.prob (Φ.SatAll E) ≠ 0 := by
  rw [prob_satall]
  apply div_ne_zero
  · exact_mod_cast (ne_of_gt h)
  · exact card_config_nonzero Φ

/-- Equation (11) under positivity of the root-deleted family. -/
theorem marginal_expansion_of_pos (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hr : r ∈ E) (hpos : 0 < Φ.Z (E.erase r)) :
    Φ.r E r = ∑ T ∈ Φ.twoTrees E r,
      (-1 : ℝ) ^ (T.card - 1) * Φ.treeCoeff E r T *
        (Φ.prob (Φ.SatAll (Φ.free E r T)) / Φ.prob (Φ.SatAll (E.erase r))) := by
  classical
  have hbase := prob_satall_ne_zero Φ (E.erase r) hpos
  have hpart := probability_partition Φ E r hr
  have hratio : Φ.r E r =
      Φ.prob (fun σ => ¬ Φ.Sat r σ ∧ Φ.SatAll (E.erase r) σ) /
        Φ.prob (Φ.SatAll (E.erase r)) := by
    have hh : Φ.prob (Φ.SatAll E) / Φ.prob (Φ.SatAll (E.erase r)) =
        (Φ.Z E : ℝ) / (Φ.Z (E.erase r) : ℝ) := by
      rw [prob_satall, prob_satall]
      exact div_div_div_cancel_right₀ (card_config_nonzero Φ) _ _
    rw [CSP.r, ← hh]
    field_simp
    linarith
  rw [hratio, unconditioned_tree_expansion Φ E r hr, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro T hT
  have hfpos : 0 < Φ.Z (Φ.free E r T) :=
    lt_of_lt_of_le hpos (z_antitone Φ (free_subset_erase Φ E r T hT))
  have hfree := prob_satall_ne_zero Φ (Φ.free E r T) hfpos
  unfold CSP.treeCoeff CSP.condProb
  field_simp

/-- Lemma 3.5 assuming positivity of the root-deleted family, the local-lemma consequence. -/

theorem solution (Φ : CSP) (hΦ : Φ.Condition11)
    (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (hr : r ∈ E) :
    Φ.r E r = ∑ T ∈ Φ.twoTrees E r,
      (-1 : ℝ) ^ (T.card - 1) * Φ.treeCoeff E r T *
        (Φ.prob (Φ.SatAll (Φ.free E r T)) / Φ.prob (Φ.SatAll (E.erase r))) :=
  marginal_expansion_of_pos Φ E r hr (condition11_partition_positive Φ hΦ (E.erase r))
