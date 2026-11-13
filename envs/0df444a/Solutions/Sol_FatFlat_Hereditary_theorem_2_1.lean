-- Prove2me | solution 1 for FatFlat.Hereditary.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:51:50.323245+00:00
-- url     : https://prove2.me/submissions/adb44a32-a82b-42fd-9946-399954c347a9

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes

section
set_option autoImplicit false

namespace FatFlat.Dev.T21
open FatFlat.Hereditary

open Classical in
/-- The number of common neighbours of `a` and `b`. -/
noncomputable def codeg {V : Type} [Fintype V] (G : SimpleGraph V) (a b : V) : ℕ :=
  (Finset.univ.filter fun x => G.Adj x a ∧ G.Adj x b).card

lemma card_pairs_le (h : ℕ) :
    Fintype.card {p : Fin h × Fin h // p.1 < p.2} ≤ h.choose 2 := by
  classical
  have : Fintype.card {p : Fin h × Fin h // p.1 < p.2}
      ≤ Fintype.card (⊤ : SimpleGraph (Fin h)).edgeSet := by
    apply Fintype.card_le_of_injective
      (fun p => (⟨s(p.1.1, p.1.2), by simpa using ne_of_lt p.2⟩ : (⊤ : SimpleGraph (Fin h)).edgeSet))
    intro p q hpq
    have := congrArg Subtype.val hpq
    simp only [Sym2.eq_iff] at this
    apply Subtype.ext
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · have := p.2
      rw [h1, h2] at this
      exact absurd this (lt_asymm q.2)
  have h2 : Fintype.card (⊤ : SimpleGraph (Fin h)).edgeSet = h.choose 2 := by
    have e := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin h)
    rw [Fintype.card_fin] at e
    rw [← e]
    simp only [SimpleGraph.edgeFinset]
    rw [Set.toFinset_card]
  omega


theorem model_of_codeg {V : Type} [Fintype V] (G : SimpleGraph V) (h : ℕ) (f : Fin h → V)
    (hf : Function.Injective f)
    (hc : ∀ i j, i ≠ j → (h + 1).choose 2 ≤ codeg G (f i) (f j)) :
    IsShallowMinor (⊤ : SimpleGraph (Fin h)) G 1 := by
  classical
  let P := {p : Fin h × Fin h // p.1 < p.2}
  let S : P → Finset V := fun p =>
    (Finset.univ.filter fun x => G.Adj x (f p.1.1) ∧ G.Adj x (f p.1.2)) \ Finset.univ.image f
  have hS : ∀ p : P, Fintype.card P ≤ (S p).card := by
    intro p
    have h1 := hc p.1.1 p.1.2 (ne_of_lt p.2)
    have h2 := Finset.le_card_sdiff (Finset.univ.image f)
      (Finset.univ.filter fun x => G.Adj x (f p.1.1) ∧ G.Adj x (f p.1.2))
    have h3 : (Finset.univ.image f).card ≤ h := by
      simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin h))) (f := f)
    have h4 : Fintype.card P ≤ h.choose 2 := card_pairs_le h
    have h5 : (h + 1).choose 2 = h.choose 2 + h := by
      rw [Nat.choose_succ_succ]; simp; omega
    have h6 : codeg G (f p.1.1) (f p.1.2) =
        (Finset.univ.filter fun x => G.Adj x (f p.1.1) ∧ G.Adj x (f p.1.2)).card := by
      unfold codeg; congr
    have h7 : (Finset.univ.filter fun x => G.Adj x (f p.1.1) ∧ G.Adj x (f p.1.2)).card
        - (Finset.univ.image f).card ≤ (S p).card := h2
    omega
  obtain ⟨w, hw, hwS⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective S).mp (by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
    · simp
    · calc s.card ≤ Fintype.card P := Finset.card_le_univ s
        _ ≤ (S p).card := hS p
        _ ≤ (s.biUnion S).card :=
          Finset.card_le_card (Finset.subset_biUnion_of_mem S hp))
  have hw1 : ∀ p : P, G.Adj (w p) (f p.1.1) ∧ G.Adj (w p) (f p.1.2) := by
    intro p
    have := hwS p
    simp only [S, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.1
  have hw2 : ∀ p : P, ∀ i, w p ≠ f i := by
    intro p i he
    have := hwS p
    simp only [S, Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ, true_and] at this
    exact this.2 ⟨i, he.symm⟩
  let B : Fin h → Set V := fun j => {x | x = f j ∨ ∃ p : P, p.1.2 = j ∧ x = w p}
  have hBcen : ∀ j, f j ∈ B j := fun j => Or.inl rfl
  have hBadj : ∀ j (x : V), x ∈ B j → x ≠ f j → G.Adj x (f j) := by
    rintro j x (rfl | ⟨p, hp, rfl⟩) hne
    · exact absurd rfl hne
    · rw [← hp]; exact (hw1 p).2
  refine ⟨⟨B, fun j => ⟨f j, hBcen j⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hy
    rcases hx with e1 | ⟨p, hp, e1⟩ <;> rcases hy with e2 | ⟨q, hq, e2⟩
    · exact hij (hf (e1.symm.trans e2))
    · exact hw2 q i (e2.symm.trans e1)
    · exact hw2 p j (e1.symm.trans e2)
    · have : p = q := hw (e1.symm.trans e2)
      subst this
      exact hij (hp.symm.trans hq)
  · intro j
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨f j, hBcen j⟩, fun v => ?_⟩
    by_cases hv : v.1 = f j
    · have : v = ⟨f j, hBcen j⟩ := Subtype.ext hv
      rw [this]
    · exact SimpleGraph.Adj.reachable (show G.Adj (f j) v.1 from (hBadj j v.1 v.2 hv).symm)
  · intro u v huv
    rcases lt_or_gt_of_ne huv with hlt | hlt
    · refine ⟨f u, hBcen u, w ⟨(u, v), hlt⟩, Or.inr ⟨⟨(u, v), hlt⟩, rfl, rfl⟩, ?_⟩
      exact (hw1 ⟨(u, v), hlt⟩).1.symm
    · refine ⟨w ⟨(v, u), hlt⟩, Or.inr ⟨⟨(v, u), hlt⟩, rfl, rfl⟩, f v, hBcen v, ?_⟩
      exact (hw1 ⟨(v, u), hlt⟩).1
  · intro j
    refine ⟨⟨f j, hBcen j⟩, fun v => ?_⟩
    by_cases hv : v.1 = f j
    · have : v = ⟨f j, hBcen j⟩ := Subtype.ext hv
      rw [this]; simp
    · have : (G.induce (B j)).Adj ⟨f j, hBcen j⟩ v :=
        show G.Adj (f j) v.1 from (hBadj j v.1 v.2 hv).symm
      rw [SimpleGraph.edist_eq_one_iff_adj.mpr this]; simp

end FatFlat.Dev.T21
end

section
set_option autoImplicit false

namespace FatFlat.Dev.T21

open Classical

/-- Dependent random choice with two samples, as a double count: a graph with
`m^2 > k^2 n^3` where `m` is the number of edges has `h` vertices with pairwise codegree `≥ k`,
provided `h ≤ k^2`. -/
theorem exists_good {V : Type} [Fintype V] (G : SimpleGraph V) (h k n m : ℕ)
    (hhk : h ≤ k ^ 2) (hV : Fintype.card V = n) (hm : G.edgeFinset.card = m)
    (hmk : k ^ 2 * n ^ 3 < m ^ 2) :
    ∃ f : Fin h → V, Function.Injective f ∧ ∀ i j, i ≠ j → k ≤ codeg G (f i) (f j) := by
  let ind : V → V → ℕ := fun x a => if G.Adj x a then 1 else 0
  let U : V → V → Finset V := fun x1 x2 => Finset.univ.filter fun a => G.Adj x1 a ∧ G.Adj x2 a
  let Bad : V × V → Prop := fun ab => ab.1 ≠ ab.2 ∧ codeg G ab.1 ab.2 < k
  let P : V → V → Finset (V × V) := fun x1 x2 =>
    Finset.univ.filter fun ab => Bad ab ∧ ab.1 ∈ U x1 x2 ∧ ab.2 ∈ U x1 x2
  have sq : ∀ F : V → ℕ, ∑ x1, ∑ x2, F x1 * F x2 = (∑ x, F x) ^ 2 := by
    intro F; rw [sq, Finset.sum_mul_sum]
  -- sum of |U|
  have hU : ∀ x1 x2, (U x1 x2).card = ∑ a, ind x1 a * ind x2 a := by
    intro x1 x2
    simp only [U, Finset.card_filter, ind]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp_all
  have hdeg : ∀ a, (∑ x, ind x a) = G.degree a := by
    intro a
    simp only [ind, ← Finset.card_filter]
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    congr 1
    ext x; simp [G.adj_comm]
  have hsumdeg : ∑ a, G.degree a = 2 * m := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hSU : ∑ x1, ∑ x2, (U x1 x2).card = ∑ a, (G.degree a) ^ 2 := by
    simp only [hU]
    calc ∑ x1, ∑ x2, ∑ a, ind x1 a * ind x2 a
        = ∑ x1, ∑ a, ∑ x2, ind x1 a * ind x2 a :=
          Finset.sum_congr rfl fun x1 _ => Finset.sum_comm
      _ = ∑ a, ∑ x1, ∑ x2, ind x1 a * ind x2 a := Finset.sum_comm
      _ = ∑ a, (∑ x, ind x a) ^ 2 := Finset.sum_congr rfl fun a _ => sq (fun x => ind x a)
      _ = ∑ a, (G.degree a) ^ 2 := Finset.sum_congr rfl fun a _ => by rw [hdeg]
  have hcs : (2 * m) ^ 2 ≤ n * ∑ a, (G.degree a) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset V)) (f := fun a => G.degree a)
    rw [hsumdeg] at this
    simpa [hV] using this
  let g : V × V → V → ℕ := fun ab x => if G.Adj x ab.1 ∧ G.Adj x ab.2 then 1 else 0
  have hg : ∀ ab, (∑ x, g ab x) = codeg G ab.1 ab.2 := by
    intro ab
    simp only [g, codeg, Finset.card_filter]
  have hPc : ∀ x1 x2, (P x1 x2).card = ∑ ab : V × V, if Bad ab then g ab x1 * g ab x2 else 0 := by
    intro x1 x2
    simp only [P, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro ab _
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, g]
    split_ifs <;> simp_all
  have hSP : ∑ x1, ∑ x2, (P x1 x2).card = ∑ ab : V × V, if Bad ab then (codeg G ab.1 ab.2) ^ 2 else 0 := by
    simp only [hPc]
    calc ∑ x1, ∑ x2, ∑ ab : V × V, (if Bad ab then g ab x1 * g ab x2 else 0)
        = ∑ x1, ∑ ab : V × V, ∑ x2, (if Bad ab then g ab x1 * g ab x2 else 0) :=
          Finset.sum_congr rfl fun x1 _ => Finset.sum_comm
      _ = ∑ ab : V × V, ∑ x1, ∑ x2, (if Bad ab then g ab x1 * g ab x2 else 0) := Finset.sum_comm
      _ = ∑ ab : V × V, if Bad ab then (codeg G ab.1 ab.2) ^ 2 else 0 := by
          apply Finset.sum_congr rfl
          intro ab _
          by_cases hb : Bad ab
          · simp only [hb, if_true]
            rw [← hg, ← sq (g ab)]
          · simp [hb]
  have hPle : ∑ x1, ∑ x2, (P x1 x2).card ≤ n * n * k ^ 2 := by
    rw [hSP]
    calc ∑ ab : V × V, (if Bad ab then (codeg G ab.1 ab.2) ^ 2 else 0)
        ≤ ∑ ab : V × V, k ^ 2 := by
          apply Finset.sum_le_sum
          intro ab _
          split_ifs with hb
          · exact Nat.pow_le_pow_left hb.2.le 2
          · exact Nat.zero_le _
      _ = n * n * k ^ 2 := by simp [hV]
  have hn : 0 < n := by
    by_contra h0
    have : n = 0 := by omega
    subst this
    have h4 : (2 * m) ^ 2 ≤ 0 := by simpa using hcs
    nlinarith
  have hex : ∃ x1 x2, h + (P x1 x2).card ≤ (U x1 x2).card := by
    by_contra hcon
    push Not at hcon
    have hlt : ∑ x1, ∑ x2, (U x1 x2).card < ∑ x1 : V, ∑ x2 : V, (h + (P x1 x2).card) := by
      have hne : (Finset.univ : Finset V).Nonempty := by
        rw [Finset.univ_nonempty_iff]
        by_contra h0
        rw [not_nonempty_iff] at h0
        have : Fintype.card V = 0 := Fintype.card_eq_zero
        omega
      apply Finset.sum_lt_sum_of_nonempty hne
      intro x1 _
      apply Finset.sum_lt_sum_of_nonempty hne
      intro x2 _
      exact hcon x1 x2
    have e1 : ∑ x1 : V, ∑ x2 : V, (h + (P x1 x2).card) = n * n * h + ∑ x1, ∑ x2, (P x1 x2).card := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hV, smul_eq_mul]
      ring
    rw [hSU, e1] at hlt
    have h1 : n ^ 3 * h ≤ n ^ 3 * k ^ 2 := Nat.mul_le_mul_left _ hhk
    have h2 : n * (n * n * h + ∑ x1, ∑ x2, (P x1 x2).card) ≤ n * (n * n * h + n * n * k ^ 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have h3 : n * (∑ a, (G.degree a) ^ 2) < n * (n * n * h + ∑ x1, ∑ x2, (P x1 x2).card) :=
      Nat.mul_lt_mul_of_pos_left hlt hn
    nlinarith
  obtain ⟨x1, x2, hx⟩ := hex
  let U' : Finset V := U x1 x2 \ (P x1 x2).image Prod.fst
  have hU' : h ≤ U'.card := by
    change h ≤ (U x1 x2 \ (P x1 x2).image Prod.fst).card
    have := Finset.le_card_sdiff ((P x1 x2).image Prod.fst) (U x1 x2)
    have := Finset.card_image_le (s := P x1 x2) (f := Prod.fst)
    omega
  have hgood : ∀ a ∈ U', ∀ b ∈ U', a ≠ b → k ≤ codeg G a b := by
    intro a ha b hb hab
    by_contra hlt
    push Not at hlt
    apply (Finset.mem_sdiff.mp ha).2
    rw [Finset.mem_image]
    refine ⟨(a, b), ?_, rfl⟩
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨hab, hlt⟩, (Finset.mem_sdiff.mp ha).1, (Finset.mem_sdiff.mp hb).1⟩
  have hcard : Fintype.card (Fin h) ≤ Fintype.card U' := by
    rw [Fintype.card_fin, Fintype.card_coe]; exact hU'
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨fun i => (e i).1, fun i j hij => e.injective (Subtype.ext hij), ?_⟩
  intro i j hij
  exact hgood _ (e i).2 _ (e j).2 (fun he => hij (e.injective (Subtype.ext he)))

end FatFlat.Dev.T21
end

section
set_option autoImplicit false

namespace FatFlat.Hereditary

open FatFlat.Dev.T21 in
theorem chk_theorem_2_1 (h n : ℕ) (hh : 0 < h) (hn : 0 < n) (V : Type) [Fintype V]
    (hV : Fintype.card V = n) (G : SimpleGraph V)
    (hE : ((h + 1).choose 2 : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 2) < (G.edgeSet.ncard : ℝ)) :
    IsShallowMinor (⊤ : SimpleGraph (Fin h)) G 1 := by
  classical
  have hsq : ((n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (n : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have hm : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']; rfl
  have hR : (((h + 1).choose 2 : ℝ) ^ 2) * (n : ℝ) ^ 3 < (G.edgeFinset.card : ℝ) ^ 2 := by
    rw [hm] at hE
    have h0 : 0 ≤ ((h + 1).choose 2 : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 2) := by positivity
    have := pow_lt_pow_left₀ hE h0 (two_ne_zero)
    rw [mul_pow, hsq] at this
    exact this
  have hN : ((h + 1).choose 2) ^ 2 * n ^ 3 < G.edgeFinset.card ^ 2 := by exact_mod_cast hR
  have hk : h ≤ ((h + 1).choose 2) ^ 2 := by
    have : h ≤ (h + 1).choose 2 := by
      rw [Nat.choose_two_right]
      have : h * 2 ≤ (h + 1) * (h + 1 - 1) := by
        simp only [Nat.add_sub_cancel]; nlinarith
      omega
    nlinarith
  obtain ⟨f, hf, hc⟩ := exists_good G h ((h + 1).choose 2) n G.edgeFinset.card hk hV rfl hN
  exact model_of_codeg G h f hf hc

end FatFlat.Hereditary
end

theorem solution : type_of% @FatFlat.Hereditary.chk_theorem_2_1 := @FatFlat.Hereditary.chk_theorem_2_1
