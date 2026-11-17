-- Prove2me | solution 1 for EDPHardness.IntegralityGap.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T08:09:51.182203+00:00
-- url     : https://prove2.me/submissions/9463a456-4d85-4d30-ad16-10b5d2ba1089

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance

namespace EDPHardness.IntegralityGap

open Finset

/-- The set of "labelled closed sequences" of length `L+1`. -/
abbrev labeledGood {n m c : ℕ} (H : Hyp n m c) (L : ℕ)
    (p : (Fin (L + 1) → Fin m) × (Fin (L + 1) → Fin n)) : Prop :=
  Function.Injective p.1 ∧ p.2 (Fin.last L) ≠ p.2 0 ∧
    ∀ j, p.2 j ∈ (H (p.1 j)).1 ∧ p.2 j ∈ (H (p.1 (finRotate (L + 1) j))).1

lemma contracted_adj_witness {n m c : ℕ} (H : Hyp n m c) {a b : Fin m}
    (h : (contracted H).Adj a b) :
    ∃ x, x ∈ (H a).1 ∧ x ∈ (H b).1 ∧ ∀ j, min a b < j → j < max a b → x ∉ (H j).1 := by
  unfold contracted gapGraph at h
  rw [SimpleGraph.fromRel_adj] at h
  obtain ⟨hab, h⟩ := h
  rcases h with h | h
  · rw [SimpleGraph.fromRel_adj] at h
    obtain ⟨_, h⟩ := h
    rcases h with h | h
    · cases h with
      | consec v a b hlt ha hb hbet =>
        refine ⟨v, ha, hb, fun j h1 h2 => hbet j ?_ ?_⟩
        · simpa [min_eq_left hlt.le] using h1
        · simpa [max_eq_right hlt.le] using h2
    · cases h with
      | special i => exact absurd rfl hab
  · rw [SimpleGraph.fromRel_adj] at h
    obtain ⟨_, h⟩ := h
    rcases h with h | h
    · cases h with
      | consec v b a hlt hb ha hbet =>
        refine ⟨v, ha, hb, fun j h1 h2 => hbet j ?_ ?_⟩
        · simpa [min_eq_right hlt.le] using h1
        · simpa [max_eq_left hlt.le] using h2
    · cases h with
      | special i => exact absurd rfl hab

theorem cycleCount_le_labeled {n m c : ℕ} (H : Hyp n m c) (g : ℕ) :
    cycleCount H g ≤ ∑ L ∈ Finset.Icc 2 (g - 1),
      (Finset.univ.filter (fun p : (Fin (L + 1) → Fin m) × (Fin (L + 1) → Fin n) =>
        Function.Injective p.1 ∧ p.2 (Fin.last L) ≠ p.2 0 ∧
          ∀ j, p.2 j ∈ (H (p.1 j)).1 ∧ p.2 j ∈ (H (p.1 (finRotate (L + 1) j))).1)).card := by
  classical
  let E : (L : ℕ) → (Fin (L + 1) → Fin m) → Finset (Sym2 (Fin m)) := fun L a =>
    Finset.univ.image (fun j => s(a j, a (finRotate (L + 1) j)))
  let T : (L : ℕ) → Finset ((Fin (L + 1) → Fin m) × (Fin (L + 1) → Fin n)) := fun L =>
    Finset.univ.filter (fun p => labeledGood H L p)
  let U : Finset (Finset (Sym2 (Fin m))) :=
    (Finset.Icc 2 (g - 1)).biUnion (fun L => (T L).image (fun p => E L p.1))
  have hsub : {S : Finset (Sym2 (Fin m)) |
      ∃ (u : Fin m) (p : (contracted H).Walk u u), p.IsCycle ∧ p.length ≤ g ∧
        p.edges.toFinset = S} ⊆ (U : Set (Finset (Sym2 (Fin m)))) := by
    rintro S ⟨u, p, hp, hlen, rfl⟩
    have h3 := hp.three_le_length
    -- maximal vertex
    have hne : p.support.toFinset.Nonempty := ⟨u, by simp⟩
    set w := p.support.toFinset.max' hne with hw
    have hwmem : w ∈ p.support := by
      have := Finset.max'_mem _ hne
      simpa using this
    set q := p.rotate w hwmem with hq
    have hqc : q.IsCycle := hp.rotate hwmem
    have hqlen : q.length = p.length := by simp [hq]
    have hqedges : q.edges.toFinset = p.edges.toFinset :=
      List.toFinset_eq_of_perm _ _ (p.rotate_edges w hwmem).perm
    have hle : ∀ i, q.getVert i ≤ w := by
      intro i
      have : q.getVert i ∈ q.support := q.getVert_mem_support i
      rw [hq, SimpleGraph.Walk.mem_support_rotate_iff] at this
      exact Finset.le_max' _ _ (by simpa using this)
    obtain ⟨L, hL⟩ : ∃ L, p.length = L + 1 := ⟨p.length - 1, by omega⟩
    have hLq : q.length = L + 1 := by rw [hqlen, hL]
    have hadj : ∀ j : Fin (L + 1), (contracted H).Adj (q.getVert j) (q.getVert (j + 1)) :=
      fun j => q.adj_getVert_succ (by rw [hLq]; exact j.isLt)
    let a : Fin (L + 1) → Fin m := fun j => q.getVert j
    let v : Fin (L + 1) → Fin n := fun j => (contracted_adj_witness H (hadj j)).choose
    have hv : ∀ j : Fin (L + 1), v j ∈ (H (q.getVert j)).1 ∧ v j ∈ (H (q.getVert (j + 1))).1 ∧
        ∀ i, min (q.getVert j) (q.getVert (j + 1)) < i →
          i < max (q.getVert j) (q.getVert (j + 1)) → v j ∉ (H i).1 :=
      fun j => (contracted_adj_witness H (hadj j)).choose_spec
    have hrot : ∀ j : Fin (L + 1), a (finRotate (L + 1) j) = q.getVert (j + 1) := by
      intro j
      simp only [a]
      by_cases hj : j = Fin.last L
      · subst hj
        rw [finRotate_last]
        simp only [Fin.val_last, Fin.val_zero, SimpleGraph.Walk.getVert_zero]
        rw [← hLq, SimpleGraph.Walk.getVert_length]
      · rw [coe_finRotate_of_ne_last hj]
    have hinj : Function.Injective a := by
      intro i j hij
      have := hqc.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) hij
      exact Fin.ext this
    have hgood : labeledGood H L (a, v) := by
      refine ⟨hinj, ?_, ?_⟩
      · intro heq
        change v (Fin.last L) = v 0 at heq
        have e0 := hv 0
        have eL := hv (Fin.last L)
        simp only [Fin.val_zero, zero_add, Fin.val_last] at e0 eL
        rw [show L + 1 = q.length from hLq.symm, SimpleGraph.Walk.getVert_length] at eL
        rw [SimpleGraph.Walk.getVert_zero] at e0
        have h1w : q.getVert 1 ≠ w := by
          intro h
          rcases (hqc.getVert_endpoint_iff (by omega)).1 h with h | h <;> omega
        have hLw : q.getVert L ≠ w := by
          intro h
          rcases (hqc.getVert_endpoint_iff (by omega)).1 h with h | h <;> omega
        have h1L : q.getVert 1 ≠ q.getVert L := by
          intro h
          have := hqc.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
            (by simp only [Set.mem_ofPred_eq]; omega) h
          omega
        have h1lt : q.getVert 1 < w := lt_of_le_of_ne (hle 1) h1w
        have hLlt : q.getVert L < w := lt_of_le_of_ne (hle L) hLw
        rcases lt_or_gt_of_ne h1L with hlt | hlt
        · -- getVert L strictly between getVert 1 and w
          apply e0.2.2 (q.getVert L)
          · rw [min_eq_right h1lt.le]; exact hlt
          · rw [max_eq_left h1lt.le]; exact hLlt
          · rw [show v 0 = v (Fin.last L) from heq.symm]; exact eL.1
        · apply eL.2.2 (q.getVert 1)
          · rw [min_eq_left hLlt.le]; exact hlt
          · rw [max_eq_right hLlt.le]; exact h1lt
          · rw [heq]; exact e0.2.1
      · intro j
        refine ⟨(hv j).1, ?_⟩
        show v j ∈ (H (a (finRotate (L + 1) j))).1
        rw [hrot j]; exact (hv j).2.1
    have hE : E L a = p.edges.toFinset := by
      rw [← hqedges]
      ext e
      simp only [E, Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset]
      rw [List.mem_iff_getElem]
      constructor
      · rintro ⟨j, rfl⟩
        refine ⟨j, by rw [SimpleGraph.Walk.length_edges, hLq]; exact j.isLt, ?_⟩
        rw [SimpleGraph.Walk.getElem_edges, hrot j]
      · rintro ⟨i, hi, rfl⟩
        rw [SimpleGraph.Walk.length_edges, hLq] at hi
        refine ⟨⟨i, hi⟩, ?_⟩
        rw [SimpleGraph.Walk.getElem_edges, hrot]
    simp only [U, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Finset.mem_Icc,
      Finset.mem_image]
    refine ⟨L, ⟨by omega, by omega⟩, (a, v), ?_, hE⟩
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hgood
  unfold cycleCount
  calc _ ≤ (U : Set (Finset (Sym2 (Fin m)))).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet U)
    _ = U.card := Set.ncard_coe_finset U
    _ ≤ ∑ L ∈ Finset.Icc 2 (g - 1), ((T L).image (fun p => E L p.1)).card := Finset.card_biUnion_le
    _ ≤ ∑ L ∈ Finset.Icc 2 (g - 1), (T L).card := by
        apply Finset.sum_le_sum; intro L _; exact Finset.card_image_le


lemma path_sum {α : Type*} [Fintype α] (q : α → α → ℝ) (s : ℝ) (hq : ∀ y, ∑ x, q x y = s) :
    ∀ L : ℕ, ∑ v : Fin (L + 1) → α, ∏ i : Fin L, q (v i.castSucc) (v i.succ) =
      Fintype.card α * s ^ L := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (L + 2) => α)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.castSucc_zero, Fin.cons_zero,
      Fin.cons_succ, ← Fin.succ_castSucc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hq, ← Finset.mul_sum, ih]
    ring

lemma card_filter_pi_inj {m k : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (a : Fin k → Fin m) (ha : Function.Injective a) (F : Fin k → Finset β) :
    (univ.filter (fun H : Fin m → β => ∀ j, H (a j) ∈ F j)).card * Fintype.card β ^ k =
      Fintype.card β ^ m * ∏ j, (F j).card := by
  classical
  let G : Fin m → Finset β := fun i => if h : ∃ j, a j = i then F h.choose else univ
  have hG : ∀ j, G (a j) = F j := by
    intro j
    have h : ∃ j', a j' = a j := ⟨j, rfl⟩
    simp only [G, dif_pos h]
    rw [ha h.choose_spec]
  have hfil : univ.filter (fun H : Fin m → β => ∀ j, H (a j) ∈ F j) = Fintype.piFinset G := by
    ext H
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hH i
      by_cases h : ∃ j, a j = i
      · obtain ⟨j, rfl⟩ := h
        rw [hG]; exact hH j
      · simp [G, dif_neg h]
    · intro hH j
      rw [← hG]; exact hH (a j)
  rw [hfil, Fintype.card_piFinset]
  have hkm : k ≤ m := by simpa using Fintype.card_le_of_injective a ha
  rw [← Finset.prod_sdiff (Finset.subset_univ (univ.image a))]
  rw [Finset.prod_image (fun x _ y _ h => ha h)]
  simp_rw [hG]
  have hrest : ∀ i ∈ univ \ univ.image a, (G i).card = Fintype.card β := by
    intro i hi
    have h : ¬ ∃ j, a j = i := by simpa using hi
    simp [G, dif_neg h]
  rw [Finset.prod_congr rfl hrest, Finset.prod_const, Finset.card_univ_sdiff,
    Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  have : Fintype.card β ^ m = Fintype.card β ^ (m - k) * Fintype.card β ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkm]
  rw [this]; ring

lemma card_sub_superset (n c : ℕ) (S : Finset (Fin n)) (hS : S.card ≤ c) :
    (univ.filter (fun s : {s : Finset (Fin n) // s.card = c} => S ⊆ s.1)).card =
      (n - S.card).choose (c - S.card) := by
  classical
  have : (univ.filter (fun s : {s : Finset (Fin n) // s.card = c} => S ⊆ s.1)).map
      (Function.Embedding.subtype _) = (univ.powersetCard c).filter (S ⊆ ·) := by
    ext t
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype,
      mem_powersetCard, subset_univ]
    constructor
    · rintro ⟨s, hs, rfl⟩; exact ⟨s.2, hs⟩
    · rintro ⟨ht, hs⟩; exact ⟨⟨t, ht⟩, hs, rfl⟩
  rw [← Finset.card_map, this, card_filter_powersetCard_subset S univ c (subset_univ _) hS,
    card_univ, Fintype.card_fin]

lemma ratio_bound (n c : ℕ) (hc : 2 ≤ c) (hcn : c ≤ n) (x y : Fin n) :
    ((univ.filter (fun s : {s : Finset (Fin n) // s.card = c} =>
        ({x, y} : Finset (Fin n)) ⊆ s.1)).card : ℝ) / (n.choose c : ℝ) ≤
      (c : ℝ) ^ 2 / (n : ℝ) ^ 2 + (if x = y then (c : ℝ) / n else 0) := by
  classical
  have hcard : ({x, y} : Finset (Fin n)).card ≤ c := by
    calc _ ≤ 2 := Finset.card_le_two
      _ ≤ c := hc
  rw [card_sub_superset n c _ hcard]
  by_cases hxy : x = y
  · subst hxy
    simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self x), Finset.card_singleton,
      if_true]
    obtain ⟨n', rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨c', rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h1 := Nat.add_one_mul_choose_eq n' c'
    have hR : (0 : ℝ) < ((n' + 1).choose (c' + 1) : ℝ) := by
      exact_mod_cast Nat.choose_pos hcn
    have h1' : ((n' : ℝ) + 1) * (n'.choose c' : ℝ) =
        ((n' + 1).choose (c' + 1) : ℝ) * ((c' : ℝ) + 1) := by exact_mod_cast h1
    have : (n'.choose c' : ℝ) / ((n' + 1).choose (c' + 1) : ℝ) =
        (((c' + 1 : ℕ) : ℝ)) / ((n' + 1 : ℕ) : ℝ) := by
      rw [div_eq_div_iff hR.ne' (by positivity)]
      push_cast; linarith
    rw [this]
    have : (0 : ℝ) ≤ ((c' + 1 : ℕ) : ℝ) ^ 2 / ((n' + 1 : ℕ) : ℝ) ^ 2 := by positivity
    linarith
  · rw [if_neg hxy, Finset.card_pair hxy, add_zero]
    obtain ⟨n', rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    obtain ⟨c', rfl⟩ : ∃ k, c = k + 2 := ⟨c - 2, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h1 := Nat.add_one_mul_choose_eq n' c'
    have h2 := Nat.add_one_mul_choose_eq (n' + 1) (c' + 1)
    have hR : (0 : ℝ) < ((n' + 2).choose (c' + 2) : ℝ) := by
      exact_mod_cast Nat.choose_pos hcn
    have h1' : ((n' : ℝ) + 1) * (n'.choose c' : ℝ) =
        ((n' + 1).choose (c' + 1) : ℝ) * ((c' : ℝ) + 1) := by exact_mod_cast h1
    have h2' : ((n' : ℝ) + 2) * ((n' + 1).choose (c' + 1) : ℝ) =
        ((n' + 2).choose (c' + 2) : ℝ) * ((c' : ℝ) + 2) := by
      exact_mod_cast h2
    set P : ℝ := (n'.choose c' : ℝ)
    set Q : ℝ := ((n' + 1).choose (c' + 1) : ℝ)
    set R : ℝ := ((n' + 2).choose (c' + 2) : ℝ)
    have hcn' : (c' : ℝ) ≤ n' := by exact_mod_cast (show c' ≤ n' by omega)
    have h3 : P * ((n' : ℝ) + 1) * ((n' : ℝ) + 2) = R * ((c' : ℝ) + 1) * ((c' : ℝ) + 2) := by
      linear_combination ((n' : ℝ) + 2) * h1' + ((c' : ℝ) + 1) * h2'
    have hR0 : 0 ≤ R := hR.le
    have key : ((c' : ℝ) + 2) ^ 2 * R * ((n' : ℝ) + 1) - P * ((n' : ℝ) + 2) ^ 2 * ((n' : ℝ) + 1)
        = R * ((c' : ℝ) + 2) * ((n' : ℝ) - c') := by
      linear_combination (-((n' : ℝ) + 2)) * h3
    have key2 : P * ((n' : ℝ) + 2) ^ 2 ≤ ((c' : ℝ) + 2) ^ 2 * R := by
      have : 0 ≤ R * ((c' : ℝ) + 2) * ((n' : ℝ) - c') := by
        apply mul_nonneg (mul_nonneg hR0 (by positivity)); linarith
      have hpos : (0 : ℝ) < (n' : ℝ) + 1 := by positivity
      nlinarith
    rw [div_le_div_iff₀ hR (by positivity)]
    push_cast
    linarith

theorem labeled_first_moment (n m c L : ℕ) (hc : 2 ≤ c) (hcn : c ≤ n) :
    (∑ H : Hyp n m c,
      ((Finset.univ.filter (fun p : (Fin (L + 1) → Fin m) × (Fin (L + 1) → Fin n) =>
        Function.Injective p.1 ∧ p.2 (Fin.last L) ≠ p.2 0 ∧
          ∀ j, p.2 j ∈ (H (p.1 j)).1 ∧ p.2 j ∈ (H (p.1 (finRotate (L + 1) j))).1)).card : ℝ)) ≤
      (Fintype.card (Hyp n m c) : ℝ) * ((m : ℝ) * ((c : ℝ) ^ 2 + c) / n) ^ (L + 1) := by
  classical
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set C : ℝ := (n.choose c : ℝ) with hC
  have hCpos : 0 < C := by rw [hC]; exact_mod_cast Nat.choose_pos hcn
  set N : ℝ := (Fintype.card (Hyp n m c) : ℝ) with hN
  have hN0 : 0 ≤ N := by positivity
  set A : ℝ := (c : ℝ) ^ 2 / (n : ℝ) ^ 2 with hA
  set B : ℝ := (c : ℝ) / n with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  let r : Fin n → Fin n → ℝ := fun x y =>
    ((univ.filter (fun s : {s : Finset (Fin n) // s.card = c} =>
      ({x, y} : Finset (Fin n)) ⊆ s.1)).card : ℝ) / C
  let q : Fin n → Fin n → ℝ := fun x y => A + if x = y then B else 0
  have hq0 : ∀ x y, 0 ≤ q x y := by
    intro x y; simp only [q]; split_ifs <;> linarith
  have hr0 : ∀ x y, 0 ≤ r x y := fun x y => by positivity
  have hrq : ∀ x y, r x y ≤ q x y := fun x y => ratio_bound n c hc hcn x y
  have hrA : ∀ x y, x ≠ y → r x y ≤ A := by
    intro x y hxy
    have := hrq x y
    simp only [q, if_neg hxy, add_zero] at this
    exact this
  have hrsymm : ∀ x y, r x y = r y x := by
    intro x y; simp only [r, Finset.pair_comm]
  have hcardSub : Fintype.card {s : Finset (Fin n) // s.card = c} = n.choose c := by
    simp
  have hNeq : N = C ^ m := by
    simp only [hN, hC, Fintype.card_fun, Fintype.card_fin, hcardSub]; push_cast; ring
  -- swap sums
  have hswap : (∑ H : Hyp n m c, ((univ.filter (fun p => labeledGood H L p)).card : ℝ)) =
      ∑ p : (Fin (L + 1) → Fin m) × (Fin (L + 1) → Fin n),
        ((univ.filter (fun H : Hyp n m c => labeledGood H L p)).card : ℝ) := by
    simp only [Finset.card_filter]
    push_cast
    exact Finset.sum_comm
  have hsymm0 : (finRotate (L + 1)).symm 0 = Fin.last L := by
    rw [Equiv.symm_apply_eq]; exact (finRotate_last).symm
  have hsymmS : ∀ i : Fin L, (finRotate (L + 1)).symm i.succ = i.castSucc := by
    intro i
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last i).ne]
    simp
  have hterm : ∀ p : (Fin (L + 1) → Fin m) × (Fin (L + 1) → Fin n),
      ((univ.filter (fun H : Hyp n m c => labeledGood H L p)).card : ℝ) ≤
        N * (A * ∏ i : Fin L, q (p.2 i.castSucc) (p.2 i.succ)) := by
    rintro ⟨a, v⟩
    have hrhs : 0 ≤ N * (A * ∏ i : Fin L, q (v i.castSucc) (v i.succ)) :=
      mul_nonneg hN0 (mul_nonneg hA0 (Finset.prod_nonneg (fun i _ => hq0 _ _)))
    by_cases hp : Function.Injective a ∧ v (Fin.last L) ≠ v 0
    · let F : Fin (L + 1) → Finset {s : Finset (Fin n) // s.card = c} := fun j =>
        univ.filter (fun s => ({v j, v ((finRotate (L + 1)).symm j)} : Finset (Fin n)) ⊆ s.1)
      have hfil : univ.filter (fun H : Hyp n m c => labeledGood H L (a, v)) =
          univ.filter (fun H : Hyp n m c => ∀ j, H (a j) ∈ F j) := by
        ext H
        simp only [mem_filter, mem_univ, true_and, F, Finset.insert_subset_iff,
          Finset.singleton_subset_iff]
        constructor
        · rintro ⟨-, -, h⟩ j
          refine ⟨(h j).1, ?_⟩
          have := (h ((finRotate (L + 1)).symm j)).2
          simpa using this
        · intro h
          refine ⟨hp.1, hp.2, fun j => ⟨(h j).1, ?_⟩⟩
          have := (h (finRotate (L + 1) j)).2
          simpa using this
      rw [hfil]
      have hcnt := card_filter_pi_inj a hp.1 F
      rw [hcardSub] at hcnt
      have hcnt' : ((univ.filter (fun H : Hyp n m c => ∀ j, H (a j) ∈ F j)).card : ℝ) =
          N * ∏ j, r (v j) (v ((finRotate (L + 1)).symm j)) := by
        have hc' : ((univ.filter (fun H : Hyp n m c => ∀ j, H (a j) ∈ F j)).card : ℝ) * C ^ (L + 1)
            = C ^ m * ∏ j, ((F j).card : ℝ) := by
          rw [hC]; exact_mod_cast hcnt
        have hCk : 0 < C ^ (L + 1) := pow_pos hCpos _
        rw [hNeq]
        simp only [r, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        field_simp
        linarith [hc']
      rw [hcnt']
      apply mul_le_mul_of_nonneg_left _ hN0
      rw [Fin.prod_univ_succ, hsymm0]
      apply mul_le_mul (hrA _ _ (Ne.symm hp.2)) _ (Finset.prod_nonneg (fun i _ => hr0 _ _)) hA0
      apply Finset.prod_le_prod (fun i _ => hr0 _ _)
      intro i _
      rw [hsymmS, hrsymm]
      exact hrq _ _
    · have : univ.filter (fun H : Hyp n m c => labeledGood H L (a, v)) = ∅ := by
        apply Finset.filter_eq_empty_iff.2
        intro H _ hH
        exact hp ⟨hH.1, hH.2.1⟩
      rw [this, Finset.card_empty, Nat.cast_zero]
      exact hrhs
  have hqsum : ∀ y, ∑ x, q x y = n * A + B := by
    intro y
    simp only [q, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hps := path_sum q (n * A + B) hqsum L
  rw [Fintype.card_fin] at hps
  have e1 : (n : ℝ) * A + B = ((c : ℝ) ^ 2 + c) / n := by
    rw [hA, hB]; field_simp
  have e2 : A * n ≤ ((c : ℝ) ^ 2 + c) / n := by
    rw [hA, le_div_iff₀ hn]
    have : (c : ℝ) ^ 2 / (n : ℝ) ^ 2 * n * n = (c : ℝ) ^ 2 := by field_simp
    rw [this]; have : (0 : ℝ) ≤ c := by positivity
    linarith
  show (∑ H : Hyp n m c, ((univ.filter (fun p => labeledGood H L p)).card : ℝ)) ≤ _
  rw [hswap]
  calc _ ≤ ∑ p : (Fin (L + 1) → Fin m) × (Fin (L + 1) → Fin n),
        N * (A * ∏ i : Fin L, q (p.2 i.castSucc) (p.2 i.succ)) :=
        Finset.sum_le_sum (fun p _ => hterm p)
    _ = (m : ℝ) ^ (L + 1) * (N * (A * (n * (n * A + B) ^ L))) := by
        rw [Fintype.sum_prod_type]
        simp only [← Finset.mul_sum, hps]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
    _ = N * ((m : ℝ) ^ (L + 1) * ((A * n) * (((c : ℝ) ^ 2 + c) / n) ^ L)) := by
        rw [e1]; ring
    _ ≤ N * ((m : ℝ) ^ (L + 1) * ((((c : ℝ) ^ 2 + c) / n) * (((c : ℝ) ^ 2 + c) / n) ^ L)) := by
        gcongr
    _ = N * ((m : ℝ) * ((c : ℝ) ^ 2 + c) / n) ^ (L + 1) := by
        rw [mul_div_assoc, mul_pow, pow_succ' (((c : ℝ) ^ 2 + c) / n)]


theorem cycleCount_first_moment (n m c g : ℕ) (hc : 2 ≤ c) (hcn : c ≤ n) :
    (∑ H : Hyp n m c, (cycleCount H g : ℝ)) ≤
      (Fintype.card (Hyp n m c) : ℝ) *
        ∑ k ∈ Finset.Icc 3 g, (2 * (m : ℝ) * ((c : ℝ) ^ 2 + c) / n) ^ k := by
  classical
  set N : ℝ := (Fintype.card (Hyp n m c) : ℝ)
  set y : ℝ := (m : ℝ) * ((c : ℝ) ^ 2 + c) / n
  have hy0 : 0 ≤ y := by positivity
  have hreidx : ∀ F : ℕ → ℝ, ∑ L ∈ Finset.Icc 2 (g - 1), F (L + 1) = ∑ k ∈ Finset.Icc 3 g, F k := by
    intro F
    rcases Nat.eq_zero_or_pos g with rfl | hg
    · simp
    · have : Finset.Icc 3 g = (Finset.Icc 2 (g - 1)).map (addRightEmbedding 1) := by
        rw [Finset.map_add_right_Icc, Nat.sub_add_cancel hg]
      rw [this, Finset.sum_map]
      rfl
  calc (∑ H : Hyp n m c, (cycleCount H g : ℝ))
      ≤ ∑ H : Hyp n m c, ∑ L ∈ Finset.Icc 2 (g - 1),
          ((Finset.univ.filter (fun p : (Fin (L + 1) → Fin m) × (Fin (L + 1) → Fin n) =>
            Function.Injective p.1 ∧ p.2 (Fin.last L) ≠ p.2 0 ∧
              ∀ j, p.2 j ∈ (H (p.1 j)).1 ∧ p.2 j ∈ (H (p.1 (finRotate (L + 1) j))).1)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro H _
        exact_mod_cast cycleCount_le_labeled H g
    _ = ∑ L ∈ Finset.Icc 2 (g - 1), ∑ H : Hyp n m c,
          ((Finset.univ.filter (fun p : (Fin (L + 1) → Fin m) × (Fin (L + 1) → Fin n) =>
            Function.Injective p.1 ∧ p.2 (Fin.last L) ≠ p.2 0 ∧
              ∀ j, p.2 j ∈ (H (p.1 j)).1 ∧ p.2 j ∈ (H (p.1 (finRotate (L + 1) j))).1)).card : ℝ) :=
        Finset.sum_comm
    _ ≤ ∑ L ∈ Finset.Icc 2 (g - 1), N * y ^ (L + 1) := by
        apply Finset.sum_le_sum
        intro L _
        exact labeled_first_moment n m c L hc hcn
    _ ≤ ∑ L ∈ Finset.Icc 2 (g - 1), N * (2 * y) ^ (L + 1) := by
        apply Finset.sum_le_sum
        intro L _
        gcongr
        linarith
    _ = N * ∑ k ∈ Finset.Icc 3 g, (2 * (m : ℝ) * ((c : ℝ) ^ 2 + c) / n) ^ k := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← hreidx (fun k => (2 * (m : ℝ) * ((c : ℝ) ^ 2 + c) / n) ^ k)]
        apply Finset.sum_congr rfl
        intro L _
        congr 1
        simp only [y]; ring

lemma geom_half_Icc (g : ℕ) (hg : 2 ≤ g) :
    (∑ k ∈ Finset.Icc 3 g, (1 / 2 : ℝ) ^ k) + (1 / 2 : ℝ) ^ g ≤ 1 / 4 := by
  induction g, hg using Nat.le_induction with
  | base => norm_num
  | succ g hg ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have : (1 / 2 : ℝ) ^ (g + 1) = (1 / 2) ^ g / 2 := by rw [pow_succ]; ring
    rw [this]; linarith

theorem lemma_8_main (n c : ℕ) (hc : 2 ≤ c) (hcn : c ≤ n) (hβ₂ : 0 < beta2 n c) (g : ℕ) (hg : 2 < g) :
    hypProb n (numEdges n c) c (E3 n c g) ≤ 1 / 4 := by
  classical
  set m := numEdges n c with hm
  set β := beta2 n c with hβ
  set z : ℝ := 3 * β * (c : ℝ) ^ 2 with hz
  set T : ℝ := (6 * β * (c : ℝ) ^ 2) ^ (g + 1) with hT
  set x : ℝ := 2 * (m : ℝ) * ((c : ℝ) ^ 2 + c) / n with hx
  set M : ℝ := max T 1 with hM
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hmle : (m : ℝ) ≤ β * n := Nat.floor_le (by positivity)
  have hx0 : 0 ≤ x := by positivity
  have hxz : x ≤ z := by
    rw [hx, div_le_iff₀ hn]
    have h1 : 2 * (m : ℝ) * ((c : ℝ) ^ 2 + c) ≤ 2 * (β * n) * ((c : ℝ) ^ 2 + c) := by
      gcongr
    have h2 : (c : ℝ) ^ 2 + c ≤ 3 / 2 * (c : ℝ) ^ 2 := by nlinarith
    have h3 : 2 * (β * n) * ((c : ℝ) ^ 2 + c) ≤ 2 * (β * n) * (3 / 2 * (c : ℝ) ^ 2) := by
      gcongr
    nlinarith
  have hT0 : 0 ≤ T := by positivity
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 < M := by linarith
  -- termwise bound
  have hterm : ∀ k ∈ Finset.Icc 3 g, x ^ k ≤ M * (1 / 2 : ℝ) ^ k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hxk : x ^ k ≤ z ^ k := pow_le_pow_left₀ hx0 hxz k
    rcases lt_or_ge z (1 / 2) with hzs | hzl
    · have : z ^ k ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hzs.le k
      nlinarith [pow_nonneg (show (0:ℝ) ≤ 1/2 by norm_num) k]
    · have h2z : (1 : ℝ) ≤ 2 * z := by linarith
      have e1 : z ^ k = (2 * z) ^ k * (1 / 2 : ℝ) ^ k := by
        rw [← mul_pow]; congr 1; ring
      have e2 : (2 * z) ^ k ≤ T := by
        rw [hT, show 6 * β * (c : ℝ) ^ 2 = 2 * z by rw [hz]; ring]
        exact pow_le_pow_right₀ h2z (by omega)
      have e3 : T ≤ M := le_max_left _ _
      have : (2 * z) ^ k * (1 / 2 : ℝ) ^ k ≤ M * (1 / 2 : ℝ) ^ k := by
        gcongr; linarith
      linarith
  have hsum : ∑ k ∈ Finset.Icc 3 g, x ^ k ≤ M * (1 / 4) := by
    calc ∑ k ∈ Finset.Icc 3 g, x ^ k ≤ ∑ k ∈ Finset.Icc 3 g, M * (1 / 2 : ℝ) ^ k :=
          Finset.sum_le_sum hterm
      _ = M * ∑ k ∈ Finset.Icc 3 g, (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
      _ ≤ M * (1 / 4) := by
          gcongr
          have := geom_half_Icc g (by omega)
          have : (0 : ℝ) ≤ (1 / 2) ^ g := by positivity
          linarith
  have hFM := cycleCount_first_moment n m c g hc hcn
  rw [← hx] at hFM
  -- nonempty
  have hne : Nonempty (Hyp n m c) := by
    obtain ⟨s, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
      (n := c) (by simpa using hcn)
    exact ⟨fun _ => ⟨s, hs.2⟩⟩
  have hN : (0 : ℝ) < Fintype.card (Hyp n m c) := by
    exact_mod_cast Fintype.card_pos
  -- events have cycleCount ≥ M
  have hev : ((Finset.univ.filter (E3 n c g : Hyp n m c → Prop)).card : ℝ) * M ≤
      ∑ H : Hyp n m c, (cycleCount H g : ℝ) := by
    calc ((Finset.univ.filter (E3 n c g : Hyp n m c → Prop)).card : ℝ) * M
        = ∑ H ∈ Finset.univ.filter (E3 n c g), M := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ H ∈ Finset.univ.filter (E3 n c g), (cycleCount H g : ℝ) := by
          apply Finset.sum_le_sum
          intro H hH
          rw [Finset.mem_filter] at hH
          have h1 : T < cycleCount H g := hH.2
          have h2 : (1 : ℝ) ≤ cycleCount H g := by
            have : 0 < cycleCount H g := by
              have : (0 : ℝ) < cycleCount H g := lt_of_le_of_lt hT0 h1
              exact_mod_cast this
            exact_mod_cast this
          exact max_le h1.le h2
      _ ≤ ∑ H : Hyp n m c, (cycleCount H g : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intros; positivity
  unfold hypProb
  rw [div_le_iff₀ hN]
  have key : ((Finset.univ.filter (E3 n c g : Hyp n m c → Prop)).card : ℝ) * M ≤
      (1 / 4 * (Fintype.card (Hyp n m c) : ℝ)) * M := by
    calc _ ≤ _ := hev
      _ ≤ _ := hFM
      _ ≤ (Fintype.card (Hyp n m c) : ℝ) * (M * (1 / 4)) := by gcongr
      _ = _ := by ring
  exact le_of_mul_le_mul_right key hM0

end EDPHardness.IntegralityGap

open EDPHardness.IntegralityGap

theorem solution (n c : ℕ) (hc : 2 ≤ c) (hcn : c ≤ n) (hβ₂ : 0 < beta2 n c) (g : ℕ) (hg : 2 < g) :
    hypProb n (numEdges n c) c (E3 n c g) ≤ 1 / 4 :=
  lemma_8_main n c hc hcn hβ₂ g hg
