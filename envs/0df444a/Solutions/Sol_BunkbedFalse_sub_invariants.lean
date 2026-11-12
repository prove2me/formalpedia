-- Prove2me | solution 1 for BunkbedFalse.sub_invariants
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T04:23:23.081758+00:00
-- url     : https://prove2.me/submissions/e717a336-8bac-41fe-a4e9-918b0007d731

import Definitions.Def_BunkbedSubstituted

/-!
# Edge count and connectivity of the substituted graph

We substitute a copy of the gadget `G_n` with `n = 1204` for each of the six hyperedges of
Hollom's hypergraph, identifying the gadget's apex with the hyperedge's transversal vertex
`hollomTr i` and the gadget's two path-ends with `hollomPath i.castSucc`, `hollomPath i.succ`.
The resulting graph lives on `Fin 7222 = Fin (10 + 6 * 1202)`.

This file proves the two graph invariants of Theorem 1.2:

* `Bunkbed.Sub.sub_edgeFinset_card : (ofEdges subEdges).edgeFinset.card = 14442`
* `Bunkbed.Sub.sub_connected : (ofEdges subEdges).Connected`

The vertex maps `iota`, `emb`, the edge set `subEdges` and the auxiliary injectivity facts are
copied verbatim from `Solutions/Sub_graph.lean` (that file is not importable as a library), with
the four `decide`-proved finite facts about Hollom's hypergraph replaced by symbolic proofs:
nothing in this file uses `decide`.
-/

set_option maxRecDepth 100000

namespace Bunkbed.Sub

open Bunkbed Bunkbed.Hyper SimpleGraph Finset

/-! ## Finite facts about Hollom's hypergraph, proved without `decide`

`hollomPath = ![0, 2, 5, 4, 3, 7, 9]` and `hollomTr = ![1, 8, 6, 1, 6, 8]`, so the three
attachment vertices of hyperedge `i` are read off from a six-row table. -/

/-- The attachment table: hyperedge `i` has transversal vertex `hollomTr i` and path ends
`hollomPath i.castSucc`, `hollomPath i.succ`. -/
lemma tri_val (i : Fin 6) :
    (i.val = 0 ∧ (hollomTr i).val = 1 ∧ (hollomPath i.castSucc).val = 0 ∧
        (hollomPath i.succ).val = 2) ∨
    (i.val = 1 ∧ (hollomTr i).val = 8 ∧ (hollomPath i.castSucc).val = 2 ∧
        (hollomPath i.succ).val = 5) ∨
    (i.val = 2 ∧ (hollomTr i).val = 6 ∧ (hollomPath i.castSucc).val = 5 ∧
        (hollomPath i.succ).val = 4) ∨
    (i.val = 3 ∧ (hollomTr i).val = 1 ∧ (hollomPath i.castSucc).val = 4 ∧
        (hollomPath i.succ).val = 3) ∨
    (i.val = 4 ∧ (hollomTr i).val = 6 ∧ (hollomPath i.castSucc).val = 3 ∧
        (hollomPath i.succ).val = 7) ∨
    (i.val = 5 ∧ (hollomTr i).val = 8 ∧ (hollomPath i.castSucc).val = 7 ∧
        (hollomPath i.succ).val = 9) := by
  fin_cases i
  · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))))

/-- The transversal vertices are `1`, `6`, `8`. -/
lemma trv (i : Fin 6) : (hollomTr i).val = 1 ∨ (hollomTr i).val = 8 ∨ (hollomTr i).val = 6 := by
  rcases tri_val i with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ <;>
    omega

/-- The path vertices are `0, 2, 5, 4, 3, 7, 9`. -/
lemma pathv (j : Fin 7) : (hollomPath j).val = 0 ∨ (hollomPath j).val = 2 ∨
    (hollomPath j).val = 5 ∨ (hollomPath j).val = 4 ∨ (hollomPath j).val = 3 ∨
    (hollomPath j).val = 7 ∨ (hollomPath j).val = 9 := by
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

lemma tr_ne_path : ∀ (i : Fin 6) (j : Fin 7), hollomTr i ≠ hollomPath j := by
  intro i j h
  have hv : (hollomTr i).val = (hollomPath j).val := by rw [h]
  have h1 := trv i
  have h2 := pathv j
  omega

lemma cs_ne_succ : ∀ i : Fin 6, hollomPath i.castSucc ≠ hollomPath i.succ := by
  intro i h
  have hv : (hollomPath i.castSucc).val = (hollomPath i.succ).val := by rw [h]
  rcases tri_val i with ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ |
    ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ <;> omega

/-- Two distinct hyperedges sharing a transversal vertex share no path end. -/
lemma bdry_val (i j : Fin 6) (hij : i.val ≠ j.val)
    (h : (hollomTr i).val = (hollomTr j).val) :
    (hollomPath i.castSucc).val ≠ (hollomPath j.castSucc).val ∧
    (hollomPath i.castSucc).val ≠ (hollomPath j.succ).val ∧
    (hollomPath i.succ).val ≠ (hollomPath j.castSucc).val ∧
    (hollomPath i.succ).val ≠ (hollomPath j.succ).val := by
  rcases tri_val i with hi | hi | hi | hi | hi | hi <;>
    rcases tri_val j with hj | hj | hj | hj | hj | hj <;> omega

lemma bdry : ∀ i j : Fin 6, i ≠ j →
    ¬ (hollomTr i = hollomTr j ∧ hollomPath i.castSucc = hollomPath j.castSucc) ∧
    ¬ (hollomTr i = hollomTr j ∧ hollomPath i.castSucc = hollomPath j.succ) ∧
    ¬ (hollomTr i = hollomTr j ∧ hollomPath i.succ = hollomPath j.castSucc) ∧
    ¬ (hollomTr i = hollomTr j ∧ hollomPath i.succ = hollomPath j.succ) := by
  intro i j hij
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro ⟨h1, h2⟩ <;>
    · have e1 : (hollomTr i).val = (hollomTr j).val := by rw [h1]
      obtain ⟨b1, b2, b3, b4⟩ := bdry_val i j hne e1
      have e2 := congrArg Fin.val h2
      omega

/-! ## The vertex maps -/

/-- The ten hypergraph vertices sit at `0, …, 9` of `Fin 7222`. -/

lemma iota_inj : Function.Injective iota := by
  intro a b h
  have hv : (iota a).val = (iota b).val := by rw [h]
  exact Fin.ext hv




lemma emb_val (i : Fin 6) (k : Fin 1205) : (emb i k).val = embN i k.val := rfl

lemma emb_val_eq {i j : Fin 6} {k l : Fin 1205} (h : emb i k = emb j l) :
    embN i k.val = embN j l.val := by
  rw [← emb_val i k, ← emb_val j l, h]

lemma embN_zero (i : Fin 6) : embN i 0 = (hollomTr i).val := by simp [embN]
lemma embN_one (i : Fin 6) : embN i 1 = (hollomPath i.castSucc).val := by simp [embN]
lemma embN_last (i : Fin 6) : embN i 1204 = (hollomPath i.succ).val := by simp [embN]

lemma embN_interior (i : Fin 6) (k : ℕ) (h2 : 2 ≤ k) (h3 : k ≤ 1203) :
    embN i k = 10 + 1202 * i.val + (k - 2) := by
  unfold embN; split_ifs <;> omega

lemma embN_bdry (i : Fin 6) (k : ℕ) (h : k = 0 ∨ k = 1 ∨ k = 1204) : embN i k < 10 := by
  have h3 : (hollomTr i).val < 10 := (hollomTr i).isLt
  have h4 : (hollomPath i.castSucc).val < 10 := (hollomPath i.castSucc).isLt
  have h5 : (hollomPath i.succ).val < 10 := (hollomPath i.succ).isLt
  rcases h with rfl | rfl | rfl <;> (unfold embN; split_ifs <;> omega)

/-- Every gadget index is one of the three attachment indices or interior. -/
lemma idx_cases (k : Fin 1205) :
    k.val = 0 ∨ k.val = 1 ∨ k.val = 1204 ∨ (2 ≤ k.val ∧ k.val ≤ 1203) := by
  have := k.isLt; omega

/-- An interior index pins down the copy *and* the index. -/
lemma emb_eq_block {i j : Fin 6} {k l : Fin 1205}
    (hk : 2 ≤ k.val) (hk' : k.val ≤ 1203) (h : emb i k = emb j l) : i = j ∧ k = l := by
  have hv : embN i k.val = embN j l.val := emb_val_eq h
  have h2 : embN i k.val = 10 + 1202 * i.val + (k.val - 2) := embN_interior i k.val hk hk'
  have hi6 : i.val < 6 := i.isLt
  have hj6 : j.val < 6 := j.isLt
  have hl : 2 ≤ l.val ∧ l.val ≤ 1203 := by
    rcases idx_cases l with hl | hl | hl | hl
    · have := embN_bdry j l.val (by omega); omega
    · have := embN_bdry j l.val (by omega); omega
    · have := embN_bdry j l.val (by omega); omega
    · exact hl
  have h3 : embN j l.val = 10 + 1202 * j.val + (l.val - 2) := embN_interior j l.val hl.1 hl.2
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

lemma embN_bdry_inj (i : Fin 6) (k l : ℕ) (hk : k = 0 ∨ k = 1 ∨ k = 1204)
    (hl : l = 0 ∨ l = 1 ∨ l = 1204) (h : embN i k = embN i l) : k = l := by
  have n1 : (hollomTr i).val ≠ (hollomPath i.castSucc).val :=
    fun hh => tr_ne_path i i.castSucc (Fin.ext hh)
  have n2 : (hollomTr i).val ≠ (hollomPath i.succ).val :=
    fun hh => tr_ne_path i i.succ (Fin.ext hh)
  have n3 : (hollomPath i.castSucc).val ≠ (hollomPath i.succ).val :=
    fun hh => cs_ne_succ i (Fin.ext hh)
  rcases hk with rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl <;>
    simp only [embN_zero, embN_one, embN_last] at h <;> omega

lemma emb_inj (i : Fin 6) : Function.Injective (emb i) := by
  intro k l h
  rcases idx_cases k with hk | hk | hk | hk
  · rcases idx_cases l with hl | hl | hl | hl
    · exact Fin.ext (by omega)
    · exact absurd (embN_bdry_inj i k.val l.val (by omega) (by omega) (emb_val_eq h))
        (by omega)
    · exact absurd (embN_bdry_inj i k.val l.val (by omega) (by omega) (emb_val_eq h))
        (by omega)
    · exact ((emb_eq_block hl.1 hl.2 h.symm).2).symm
  · rcases idx_cases l with hl | hl | hl | hl
    · exact absurd (embN_bdry_inj i k.val l.val (by omega) (by omega) (emb_val_eq h))
        (by omega)
    · exact Fin.ext (by omega)
    · exact absurd (embN_bdry_inj i k.val l.val (by omega) (by omega) (emb_val_eq h))
        (by omega)
    · exact ((emb_eq_block hl.1 hl.2 h.symm).2).symm
  · rcases idx_cases l with hl | hl | hl | hl
    · exact absurd (embN_bdry_inj i k.val l.val (by omega) (by omega) (emb_val_eq h))
        (by omega)
    · exact absurd (embN_bdry_inj i k.val l.val (by omega) (by omega) (emb_val_eq h))
        (by omega)
    · exact Fin.ext (by omega)
    · exact ((emb_eq_block hl.1 hl.2 h.symm).2).symm
  · exact (emb_eq_block hk.1 hk.2 h).2

/-! ## The substituted graph -/



/-! ## The edge count of the gadget `Gₙ`: `2n - 1` -/

/-- Reduction `ℕ → Fin (n+1)`; this Mathlib has no `NatCast (Fin _)` instance. -/
def fc (n : ℕ) (m : ℕ) : Fin (n + 1) := ⟨m % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

lemma fc_val (n m : ℕ) (h : m < n + 1) : (fc n m).val = m := Nat.mod_eq_of_lt h

lemma fc_self {n : ℕ} (k : Fin (n + 1)) : fc n k.val = k := Fin.ext (fc_val n k.val k.isLt)

lemma mem_gadgetE_iff {n : ℕ} (e : Sym2 (Fin (n + 1))) :
    e ∈ gadgetE n ↔ ∃ p : Fin (n + 1) × Fin (n + 1),
      ((p.1 = 0 ∧ p.2 ≠ 0) ∨ (1 ≤ p.1.val ∧ p.2.val = p.1.val + 1)) ∧ s(p.1, p.2) = e := by
  simp only [gadgetE, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The `n` spokes of `Gₙ`. -/
def spokeS (n : ℕ) : Finset (Sym2 (Fin (n + 1))) :=
  (Finset.Ico 1 (n + 1)).image (fun m : ℕ => s((0 : Fin (n + 1)), fc n m))

/-- The `n - 1` path edges of `Gₙ`. -/
def pathS (n : ℕ) : Finset (Sym2 (Fin (n + 1))) :=
  (Finset.Ico 1 n).image (fun m : ℕ => s(fc n m, fc n (m + 1)))

lemma gadgetE_eq (n : ℕ) : gadgetE n = spokeS n ∪ pathS n := by
  ext e
  rw [mem_gadgetE_iff, Finset.mem_union]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine Finset.mem_image.2 ⟨p.2.val, Finset.mem_Ico.2 ⟨?_, p.2.isLt⟩, ?_⟩
      · rcases Nat.eq_zero_or_pos p.2.val with h | h
        · exact absurd (Fin.ext h : p.2 = 0) h2
        · exact h
      · show s((0 : Fin (n + 1)), fc n p.2.val) = s(p.1, p.2)
        rw [h1, fc_self]
    · right
      have h3 := p.2.isLt
      refine Finset.mem_image.2 ⟨p.1.val, Finset.mem_Ico.2 ⟨h1, by omega⟩, ?_⟩
      show s(fc n p.1.val, fc n (p.1.val + 1)) = s(p.1, p.2)
      rw [fc_self]
      congr 1
      exact Fin.ext (by rw [fc_val n _ (by omega), h2])
  · rintro (h | h)
    · obtain ⟨m, hm, he⟩ := Finset.mem_image.1 h
      rw [Finset.mem_Ico] at hm
      refine ⟨(0, fc n m), Or.inl ⟨rfl, ?_⟩, he⟩
      intro hc
      have hc' : fc n m = 0 := hc
      have hv : (fc n m).val = 0 := by rw [hc']; rfl
      rw [fc_val n m (by omega)] at hv
      omega
    · obtain ⟨m, hm, he⟩ := Finset.mem_image.1 h
      rw [Finset.mem_Ico] at hm
      refine ⟨(fc n m, fc n (m + 1)), Or.inr ⟨?_, ?_⟩, he⟩
      · rw [fc_val n m (by omega)]; omega
      · rw [fc_val n m (by omega), fc_val n (m + 1) (by omega)]

lemma spokeS_card (n : ℕ) : (spokeS n).card = n := by
  have hinj : Set.InjOn (fun m : ℕ => s((0 : Fin (n + 1)), fc n m))
      (Finset.Ico 1 (n + 1)) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    rcases Sym2.eq_iff.mp hab with ⟨-, h⟩ | ⟨h1, -⟩
    · have hv : (fc n a).val = (fc n b).val := by rw [h]
      rw [fc_val n a (by omega), fc_val n b (by omega)] at hv
      exact hv
    · exfalso
      have hv : (0 : Fin (n + 1)).val = (fc n b).val := by rw [h1]
      rw [fc_val n b (by omega)] at hv
      simp only [Fin.val_zero] at hv
      omega
  have hc : (Finset.Ico 1 (n + 1)).card = n := by rw [Nat.card_Ico]; omega
  rw [spokeS, Finset.card_image_of_injOn hinj, hc]

lemma pathS_card (n : ℕ) : (pathS n).card = n - 1 := by
  have hinj : Set.InjOn (fun m : ℕ => s(fc n m, fc n (m + 1))) (Finset.Ico 1 n) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    rcases Sym2.eq_iff.mp hab with ⟨h, -⟩ | ⟨h1, h2⟩
    · have hv : (fc n a).val = (fc n b).val := by rw [h]
      rw [fc_val n a (by omega), fc_val n b (by omega)] at hv
      exact hv
    · exfalso
      have e1 : (fc n a).val = (fc n (b + 1)).val := by rw [h1]
      have e2 : (fc n (a + 1)).val = (fc n b).val := by rw [h2]
      rw [fc_val n a (by omega), fc_val n (b + 1) (by omega)] at e1
      rw [fc_val n (a + 1) (by omega), fc_val n b (by omega)] at e2
      omega
  have hc : (Finset.Ico 1 n).card = n - 1 := by rw [Nat.card_Ico]
  rw [pathS, Finset.card_image_of_injOn hinj, hc]

lemma spokeS_disjoint_pathS (n : ℕ) : Disjoint (spokeS n) (pathS n) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 he
  obtain ⟨b, hb, hb2⟩ := Finset.mem_image.1 he'
  rw [Finset.mem_Ico] at ha hb
  rcases Sym2.eq_iff.mp hb2 with ⟨h1, -⟩ | ⟨-, h2⟩
  · have hv : (fc n b).val = (0 : Fin (n + 1)).val := by rw [h1]
    rw [fc_val n b (by omega)] at hv
    simp only [Fin.val_zero] at hv
    omega
  · have hv : (fc n (b + 1)).val = (0 : Fin (n + 1)).val := by rw [h2]
    rw [fc_val n (b + 1) (by omega)] at hv
    simp only [Fin.val_zero] at hv
    omega

lemma gadgetE_card (n : ℕ) : (gadgetE n).card = 2 * n - 1 := by
  rw [gadgetE_eq, Finset.card_union_of_disjoint (spokeS_disjoint_pathS n), spokeS_card,
    pathS_card]
  omega

/-! ## The six copies are pairwise disjoint -/

lemma mem_copy_iff (i : Fin 6) (e : Sym2 (Fin 7222)) :
    e ∈ (gadgetE 1204).image (Sym2.map (emb i)) ↔
      ∃ p : Fin 1205 × Fin 1205,
        ((p.1 = 0 ∧ p.2 ≠ 0) ∨ (1 ≤ p.1.val ∧ p.2.val = p.1.val + 1)) ∧
        s(emb i p.1, emb i p.2) = e := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨p, hp, rfl⟩ := (mem_gadgetE_iff (n := 1204) a).1 ha
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨s(p.1, p.2), (mem_gadgetE_iff (n := 1204) _).2 ⟨p, hp, rfl⟩, rfl⟩

/-- Every gadget edge either has an interior endpoint, or is one of the two edges joining the
apex to a path end. -/
lemma cond_cases {p : Fin 1205 × Fin 1205}
    (hp : (p.1 = 0 ∧ p.2 ≠ 0) ∨ (1 ≤ p.1.val ∧ p.2.val = p.1.val + 1)) :
    (2 ≤ p.1.val ∧ p.1.val ≤ 1203) ∨ (2 ≤ p.2.val ∧ p.2.val ≤ 1203) ∨
      (p.1.val = 0 ∧ (p.2.val = 1 ∨ p.2.val = 1204)) := by
  have h1 := p.1.isLt
  have h2 := p.2.isLt
  rcases hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have ha' : p.1.val = 0 := by rw [ha]; rfl
    have hb' : p.2.val ≠ 0 := fun hh => hb (Fin.ext hh)
    omega
  · omega

lemma emb_bdry_cross {i j : Fin 6} (hij : i ≠ j) {p1 p2 q1 q2 : Fin 1205}
    (hp1 : p1.val = 0) (hp2 : p2.val = 1 ∨ p2.val = 1204)
    (hq1 : q1.val = 0) (hq2 : q2.val = 1 ∨ q2.val = 1204)
    (key : s(emb i p1, emb i p2) = s(emb j q1, emb j q2)) : False := by
  obtain ⟨b1, b2, b3, b4⟩ := bdry i j hij
  rcases Sym2.eq_iff.mp key with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have f1 := emb_val_eq e1
    have f2 := emb_val_eq e2
    rw [hp1, hq1, embN_zero, embN_zero] at f1
    rcases hp2 with h | h <;> rcases hq2 with h' | h' <;>
      rw [h, h'] at f2 <;> simp only [embN_one, embN_last] at f2
    · exact b1 ⟨Fin.ext f1, Fin.ext f2⟩
    · exact b2 ⟨Fin.ext f1, Fin.ext f2⟩
    · exact b3 ⟨Fin.ext f1, Fin.ext f2⟩
    · exact b4 ⟨Fin.ext f1, Fin.ext f2⟩
  · have f1 := emb_val_eq e1
    rw [hp1, embN_zero] at f1
    rcases hq2 with h' | h' <;> rw [h'] at f1 <;> simp only [embN_one, embN_last] at f1
    · exact tr_ne_path i j.castSucc (Fin.ext f1)
    · exact tr_ne_path i j.succ (Fin.ext f1)

lemma copies_disjoint :
    ((Finset.univ : Finset (Fin 6)) : Set (Fin 6)).PairwiseDisjoint
      (fun i : Fin 6 => (gadgetE 1204).image (Sym2.map (emb i))) := by
  intro i _ j _ hij
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro e hei hej
  obtain ⟨p, hp, hpe⟩ := (mem_copy_iff i e).1 hei
  obtain ⟨q, hq, hqe⟩ := (mem_copy_iff j e).1 hej
  have key : s(emb i p.1, emb i p.2) = s(emb j q.1, emb j q.2) := by rw [hpe, hqe]
  have noint : ∀ k : Fin 1205, 2 ≤ k.val → k.val ≤ 1203 →
      (emb i k = emb j q.1 ∨ emb i k = emb j q.2) → False := by
    intro k h1 h2 hor
    rcases hor with h | h
    · exact hij (emb_eq_block h1 h2 h).1
    · exact hij (emb_eq_block h1 h2 h).1
  have noint' : ∀ k : Fin 1205, 2 ≤ k.val → k.val ≤ 1203 →
      (emb j k = emb i p.1 ∨ emb j k = emb i p.2) → False := by
    intro k h1 h2 hor
    rcases hor with h | h
    · exact hij (emb_eq_block h1 h2 h).1.symm
    · exact hij (emb_eq_block h1 h2 h).1.symm
  have hmem1 : emb i p.1 = emb j q.1 ∨ emb i p.1 = emb j q.2 := by
    rcases Sym2.eq_iff.mp key with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hmem2 : emb i p.2 = emb j q.1 ∨ emb i p.2 = emb j q.2 := by
    rcases Sym2.eq_iff.mp key with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr h
    · exact Or.inl h
  have hmem1' : emb j q.1 = emb i p.1 ∨ emb j q.1 = emb i p.2 := by
    rcases Sym2.eq_iff.mp key with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hmem2' : emb j q.2 = emb i p.1 ∨ emb j q.2 = emb i p.2 := by
    rcases Sym2.eq_iff.mp key with ⟨-, h⟩ | ⟨h, -⟩
    · exact Or.inr h.symm
    · exact Or.inl h.symm
  rcases cond_cases hp with h | h | h
  · exact noint p.1 h.1 h.2 hmem1
  · exact noint p.2 h.1 h.2 hmem2
  · rcases cond_cases hq with h' | h' | h'
    · exact noint' q.1 h'.1 h'.2 hmem1'
    · exact noint' q.2 h'.1 h'.2 hmem2'
    · exact emb_bdry_cross hij h.1 h.2 h'.1 h'.2 key

/-! ## (a) The edge count of the substituted graph -/

theorem subEdges_card : subEdges.card = 14442 := by
  have h1 : ∀ i : Fin 6, ((gadgetE 1204).image (Sym2.map (emb i))).card = 2407 := by
    intro i
    rw [Finset.card_image_of_injective _ (Sym2.map.injective (emb_inj i)), gadgetE_card]
  rw [subEdges, Finset.card_biUnion copies_disjoint, Finset.sum_congr rfl (fun i _ => h1 i)]
  simp

lemma subEdges_not_isDiag : ∀ e ∈ subEdges, ¬ e.IsDiag := by
  intro e he
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 he
  obtain ⟨p, hp, rfl⟩ := (mem_copy_iff i e).1 hi
  rw [Sym2.mk_isDiag_iff]
  intro hc
  have hpp : p.1 = p.2 := emb_inj i hc
  rcases hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact hb (hpp ▸ ha)
  · have : p.1.val = p.2.val := congrArg Fin.val hpp
    omega

lemma edgeFinset_ofEdges {E : Finset (Sym2 (Fin 7222))} (h : ∀ e ∈ E, ¬ e.IsDiag) :
    (ofEdges E).edgeFinset = E := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet]
  simp only [Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet]
  exact ⟨fun hh => hh.1, fun hh => ⟨hh, h e hh⟩⟩

theorem sub_edgeFinset_card : (ofEdges subEdges).edgeFinset.card = 14442 := by
  rw [edgeFinset_ofEdges subEdges_not_isDiag, subEdges_card]

/-! ## (b) Connectivity of the substituted graph

Inside the copy glued in at hyperedge `i` the apex `emb i 0` is adjacent to every other vertex
of the copy, so the copy is connected. The copies are glued along the path
`hollomPath = ![0, 2, 5, 4, 3, 7, 9]`: copy `i` contains both `hollomPath i.castSucc` and
`hollomPath i.succ`. Walking down that chain of six copies reaches `iota 0` from everywhere. -/

lemma one_val : (1 : Fin 1205).val = 1 := rfl
lemma last_val : (1204 : Fin 1205).val = 1204 := rfl

lemma emb_apex_eq (i : Fin 6) : emb i 0 = iota (hollomTr i) :=
  Fin.ext (by rw [emb_val]; exact embN_zero i)

lemma emb_one_eq (i : Fin 6) : emb i 1 = iota (hollomPath i.castSucc) :=
  Fin.ext (by rw [emb_val, one_val]; exact embN_one i)

lemma emb_last_eq (i : Fin 6) : emb i 1204 = iota (hollomPath i.succ) :=
  Fin.ext (by rw [emb_val, last_val]; exact embN_last i)

/-- The apex of a copy is adjacent to every other vertex of that copy. -/
lemma adj_apex (i : Fin 6) (k : Fin 1205) (hk : k ≠ 0) :
    (ofEdges subEdges).Adj (emb i 0) (emb i k) := by
  have hmem : s(emb i 0, emb i k) ∈ subEdges :=
    Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i,
      (mem_copy_iff i _).2 ⟨((0 : Fin 1205), k), Or.inl ⟨rfl, hk⟩, rfl⟩⟩
  refine (SimpleGraph.fromEdgeSet_adj _).2 ⟨Finset.mem_coe.2 hmem, ?_⟩
  intro h
  exact hk (emb_inj i h).symm

/-- Every vertex of a copy is reachable from that copy's apex. -/
lemma reach_in_copy (i : Fin 6) (k : Fin 1205) :
    (ofEdges subEdges).Reachable (emb i 0) (emb i k) := by
  by_cases hk : k = 0
  · rw [hk]
  · exact (adj_apex i k hk).reachable

/-- Both path ends of copy `i` are reachable from its transversal vertex. -/
lemma reach_tri (i : Fin 6) :
    (ofEdges subEdges).Reachable (iota (hollomPath i.castSucc)) (iota (hollomTr i)) ∧
    (ofEdges subEdges).Reachable (iota (hollomTr i)) (iota (hollomPath i.succ)) := by
  refine ⟨?_, ?_⟩
  · rw [← emb_one_eq, ← emb_apex_eq]
    exact (reach_in_copy i 1).symm
  · rw [← emb_apex_eq, ← emb_last_eq]
    exact reach_in_copy i 1204

/-- All ten hypergraph vertices are reachable from `iota 0`. -/
lemma reach_base (w : Fin 10) : (ofEdges subEdges).Reachable (iota 0) (iota w) := by
  have h01 : (ofEdges subEdges).Reachable (iota 0) (iota 1) := (reach_tri 0).1
  have h12 : (ofEdges subEdges).Reachable (iota 1) (iota 2) := (reach_tri 0).2
  have h28 : (ofEdges subEdges).Reachable (iota 2) (iota 8) := (reach_tri 1).1
  have h85 : (ofEdges subEdges).Reachable (iota 8) (iota 5) := (reach_tri 1).2
  have h56 : (ofEdges subEdges).Reachable (iota 5) (iota 6) := (reach_tri 2).1
  have h64 : (ofEdges subEdges).Reachable (iota 6) (iota 4) := (reach_tri 2).2
  have h13 : (ofEdges subEdges).Reachable (iota 1) (iota 3) := (reach_tri 3).2
  have h67 : (ofEdges subEdges).Reachable (iota 6) (iota 7) := (reach_tri 4).2
  have h89 : (ofEdges subEdges).Reachable (iota 8) (iota 9) := (reach_tri 5).2
  have r1 : (ofEdges subEdges).Reachable (iota 0) (iota 1) := h01
  have r2 : (ofEdges subEdges).Reachable (iota 0) (iota 2) := r1.trans h12
  have r8 : (ofEdges subEdges).Reachable (iota 0) (iota 8) := r2.trans h28
  have r5 : (ofEdges subEdges).Reachable (iota 0) (iota 5) := r8.trans h85
  have r6 : (ofEdges subEdges).Reachable (iota 0) (iota 6) := r5.trans h56
  have r4 : (ofEdges subEdges).Reachable (iota 0) (iota 4) := r6.trans h64
  have r3 : (ofEdges subEdges).Reachable (iota 0) (iota 3) := r1.trans h13
  have r7 : (ofEdges subEdges).Reachable (iota 0) (iota 7) := r6.trans h67
  have r9 : (ofEdges subEdges).Reachable (iota 0) (iota 9) := r8.trans h89
  have hv : w.val = 0 ∨ w.val = 1 ∨ w.val = 2 ∨ w.val = 3 ∨ w.val = 4 ∨ w.val = 5 ∨
      w.val = 6 ∨ w.val = 7 ∨ w.val = 8 ∨ w.val = 9 := by have := w.isLt; omega
  rcases hv with h | h | h | h | h | h | h | h | h | h
  · rw [show w = (0 : Fin 10) from Fin.ext h]
  · rw [show w = (1 : Fin 10) from Fin.ext h]; exact r1
  · rw [show w = (2 : Fin 10) from Fin.ext h]; exact r2
  · rw [show w = (3 : Fin 10) from Fin.ext h]; exact r3
  · rw [show w = (4 : Fin 10) from Fin.ext h]; exact r4
  · rw [show w = (5 : Fin 10) from Fin.ext h]; exact r5
  · rw [show w = (6 : Fin 10) from Fin.ext h]; exact r6
  · rw [show w = (7 : Fin 10) from Fin.ext h]; exact r7
  · rw [show w = (8 : Fin 10) from Fin.ext h]; exact r8
  · rw [show w = (9 : Fin 10) from Fin.ext h]; exact r9

/-- Every vertex at or beyond `10` is an interior vertex of exactly one copy. -/
lemma exists_interior (v : Fin 7222) (hv : 10 ≤ v.val) :
    ∃ (i : Fin 6) (k : Fin 1205), emb i k = v := by
  have hlt := v.isLt
  refine ⟨⟨(v.val - 10) / 1202, by omega⟩, ⟨(v.val - 10) % 1202 + 2, by omega⟩, ?_⟩
  refine Fin.ext ?_
  rw [emb_val]
  show embN _ ((v.val - 10) % 1202 + 2) = v.val
  rw [embN_interior _ _ (by omega) (by omega)]
  show 10 + 1202 * ((v.val - 10) / 1202) + ((v.val - 10) % 1202 + 2 - 2) = v.val
  omega

/-- Every vertex is reachable from `iota 0`. -/
lemma reach_root (v : Fin 7222) : (ofEdges subEdges).Reachable (iota 0) v := by
  by_cases hv : v.val < 10
  · rw [show v = iota ⟨v.val, hv⟩ from Fin.ext rfl]
    exact reach_base _
  · obtain ⟨i, k, hik⟩ := exists_interior v (by omega)
    rw [← hik]
    have h1 : (ofEdges subEdges).Reachable (iota (hollomTr i)) (emb i k) := by
      rw [← emb_apex_eq i]
      exact reach_in_copy i k
    exact (reach_base (hollomTr i)).trans h1

theorem sub_connected : (ofEdges subEdges).Connected := by
  rw [SimpleGraph.connected_iff]
  exact ⟨fun u v => (reach_root u).symm.trans (reach_root v), ⟨iota 0⟩⟩



theorem subT_card' : subT.card = 3 := by
  rw [subT, Finset.card_image_of_injective _ iota_inj]
  decide

end Bunkbed.Sub

open Bunkbed SimpleGraph Finset in
/-- **The invariants of the substituted graph.** -/
theorem solution :
    (ofEdges Bunkbed.Sub.subEdges).edgeFinset.card = 14442 ∧ Bunkbed.Sub.subT.card = 3
      ∧ (ofEdges Bunkbed.Sub.subEdges).Connected :=
  ⟨Bunkbed.Sub.sub_edgeFinset_card, Bunkbed.Sub.subT_card', Bunkbed.Sub.sub_connected⟩

#print axioms solution
