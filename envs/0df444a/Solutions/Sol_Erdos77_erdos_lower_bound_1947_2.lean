-- Prove2me | solution 2 for Erdos77.erdos_lower_bound_1947
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T03:32:28.857461+00:00
-- url     : https://prove2.me/submissions/913abcd8-2b15-47da-b110-4710442b9d48

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey

open Filter Topology
open Finset

namespace Erdos77Aux

/-- Ramsey's theorem relative to a finite vertex subset `S`. -/
lemma ramsey_exists_aux : ∀ (m n : ℕ), ∃ N : ℕ, ∀ (V : Type) (G : SimpleGraph V) (S : Finset V),
    N ≤ S.card → (∃ s ⊆ S, G.IsNClique m s) ∨ (∃ s ⊆ S, G.IsNIndepSet n s) := by
  classical
  intro m
  induction m with
  | zero =>
    intro n
    exact ⟨0, fun V G S _ => Or.inl ⟨∅, Finset.empty_subset _, by simp⟩⟩
  | succ m ihm =>
    intro n
    induction n with
    | zero =>
      exact ⟨0, fun V G S _ => Or.inr ⟨∅, Finset.empty_subset _,
        (SimpleGraph.isNClique_compl G).1 (by simp)⟩⟩
    | succ n ihn =>
      obtain ⟨N1, h1⟩ := ihm (n + 1)
      obtain ⟨N2, h2⟩ := ihn
      refine ⟨N1 + N2 + 1, fun V G S hS => ?_⟩
      have hne : S.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨v, hv⟩ := hne
      set A := (S.erase v).filter (fun w => G.Adj v w) with hA
      set B := (S.erase v).filter (fun w => ¬ G.Adj v w) with hB
      have hcard : A.card + B.card = S.card - 1 := by
        rw [hA, hB, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]
      have hAS : A ⊆ S := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      have hBS : B ⊆ S := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      have hvA : v ∉ A := fun h => by
        have := (Finset.mem_filter.1 h).1
        simp at this
      have hvB : v ∉ B := fun h => by
        have := (Finset.mem_filter.1 h).1
        simp at this
      by_cases hA' : N1 ≤ A.card
      · rcases h1 V G A hA' with ⟨s, hsA, hs⟩ | ⟨s, hsA, hs⟩
        · left
          refine ⟨insert v s, Finset.insert_subset hv (hsA.trans hAS), ?_⟩
          rw [SimpleGraph.isNClique_iff, Finset.coe_insert]
          refine ⟨SimpleGraph.isClique_insert.2 ⟨hs.isClique, fun b hb _ =>
            (Finset.mem_filter.1 (hsA (Finset.mem_coe.1 hb))).2⟩, ?_⟩
          rw [Finset.card_insert_of_notMem (fun h => hvA (hsA h)), hs.card_eq]
        · exact Or.inr ⟨s, hsA.trans hAS, hs⟩
      · have hB' : N2 ≤ B.card := by omega
        rcases h2 V G B hB' with ⟨s, hsB, hs⟩ | ⟨s, hsB, hs⟩
        · exact Or.inl ⟨s, hsB.trans hBS, hs⟩
        · right
          refine ⟨insert v s, Finset.insert_subset hv (hsB.trans hBS), ?_⟩
          rw [← SimpleGraph.isNClique_compl G, SimpleGraph.isNClique_iff, Finset.coe_insert]
          have hs' : Gᶜ.IsNClique n s := (SimpleGraph.isNClique_compl G).2 hs
          refine ⟨SimpleGraph.isClique_insert.2 ⟨hs'.isClique, fun b hb hvb => ?_⟩, ?_⟩
          · rw [SimpleGraph.compl_adj]
            exact ⟨hvb, (Finset.mem_filter.1 (hsB (Finset.mem_coe.1 hb))).2⟩
          · rw [Finset.card_insert_of_notMem (fun h => hvB (hsB h)), hs'.card_eq]


/-- The graph on `Fin N` with edge set `F` (a family of two-element subsets). -/
def gr (N : ℕ) (F : Finset (Finset (Fin N))) : SimpleGraph (Fin N) where
  Adj x y := x ≠ y ∧ ({x, y} : Finset (Fin N)) ∈ F
  symm := ⟨fun x y h => ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

lemma gr_adj {N : ℕ} {F : Finset (Finset (Fin N))} {x y : Fin N} :
    (gr N F).Adj x y ↔ x ≠ y ∧ ({x, y} : Finset (Fin N)) ∈ F := Iff.rfl

lemma pow2_subset_of_clique {N n : ℕ} {F : Finset (Finset (Fin N))} {S : Finset (Fin N)}
    (h : (gr N F).IsNClique n S) : S.powersetCard 2 ⊆ F := by
  intro T hT
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨hTS, hT2⟩ := hT
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hT2
  have hx : x ∈ S := hTS (by simp)
  have hy : y ∈ S := hTS (by simp)
  exact (gr_adj.1 (h.isClique hx hy hxy)).2

lemma disjoint_of_indep {N n : ℕ} {F : Finset (Finset (Fin N))} {S : Finset (Fin N)}
    (h : (gr N F).IsNIndepSet n S) : Disjoint F (S.powersetCard 2) := by
  rw [Finset.disjoint_left]
  intro T hTF hTS
  rw [Finset.mem_powersetCard] at hTS
  obtain ⟨hTS, hT2⟩ := hTS
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hT2
  have hx : x ∈ S := hTS (by simp)
  have hy : y ∈ S := hTS (by simp)
  exact h.isIndepSet hx hy hxy (gr_adj.2 ⟨hxy, hTF⟩)

lemma exists_good_graph (N n : ℕ) (h : 2 * N.choose n < 2 ^ (n.choose 2)) :
    ∃ G : SimpleGraph (Fin N),
      (∀ s : Finset (Fin N), ¬ G.IsNClique n s) ∧ ∀ s : Finset (Fin N), ¬ G.IsNIndepSet n s := by
  classical
  by_contra hcon
  have key : ∀ G : SimpleGraph (Fin N),
      (∃ s, G.IsNClique n s) ∨ ∃ s, G.IsNIndepSet n s := fun G => by
    by_contra h'
    exact hcon ⟨G, fun s hs => h' (Or.inl ⟨s, hs⟩), fun s hs => h' (Or.inr ⟨s, hs⟩)⟩
  set E : Finset (Finset (Fin N)) := (Finset.univ : Finset (Fin N)).powersetCard 2 with hE
  have hEcard : E.card = N.choose 2 := by
    rw [hE, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  -- bad families for a given `n`-set
  let Bc : Finset (Fin N) → Finset (Finset (Finset (Fin N))) :=
    fun S => E.powerset.filter (fun F => S.powersetCard 2 ⊆ F)
  let Bi : Finset (Fin N) → Finset (Finset (Finset (Fin N))) :=
    fun S => E.powerset.filter (fun F => Disjoint F (S.powersetCard 2))
  have hcover : E.powerset ⊆ (Finset.univ.powersetCard n).biUnion (fun S => Bc S ∪ Bi S) := by
    intro F hF
    rw [Finset.mem_biUnion]
    rcases key (gr N F) with ⟨S, hS⟩ | ⟨S, hS⟩
    · refine ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS.card_eq⟩, ?_⟩
      exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hF, pow2_subset_of_clique hS⟩)
    · refine ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS.card_eq⟩, ?_⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hF, disjoint_of_indep hS⟩)
  have hBc : ∀ S : Finset (Fin N), S.card = n →
      (Bc S).card ≤ 2 ^ (E.card - n.choose 2) := by
    intro S hS
    have hsub : S.powersetCard 2 ⊆ E := Finset.powersetCard_mono (Finset.subset_univ S)
    have hES : (S.powersetCard 2).card = n.choose 2 := by rw [Finset.card_powersetCard, hS]
    calc (Bc S).card ≤ ((E \ S.powersetCard 2).powerset).card := by
          refine Finset.card_le_card_of_injOn (fun F => F \ S.powersetCard 2) ?_ ?_
          · intro F hF
            simp only [Finset.mem_coe, Bc, Finset.mem_filter, Finset.mem_powerset] at hF ⊢
            exact Finset.sdiff_subset_sdiff hF.1 (le_refl _)
          · intro F hF G hG hFG
            simp only [Finset.mem_coe, Bc, Finset.mem_filter] at hF hG
            have := congrArg (· ∪ S.powersetCard 2) hFG
            simp only [Finset.sdiff_union_of_subset hF.2, Finset.sdiff_union_of_subset hG.2] at this
            exact this
      _ = 2 ^ (E.card - n.choose 2) := by
          rw [Finset.card_powerset, Finset.card_sdiff_of_subset hsub, hES]
  have hBi : ∀ S : Finset (Fin N), S.card = n →
      (Bi S).card ≤ 2 ^ (E.card - n.choose 2) := by
    intro S hS
    have hsub : S.powersetCard 2 ⊆ E := Finset.powersetCard_mono (Finset.subset_univ S)
    have hES : (S.powersetCard 2).card = n.choose 2 := by rw [Finset.card_powersetCard, hS]
    calc (Bi S).card ≤ ((E \ S.powersetCard 2).powerset).card := by
          refine Finset.card_le_card ?_
          intro F hF
          simp only [Bi, Finset.mem_filter, Finset.mem_powerset] at hF ⊢
          exact Finset.subset_sdiff.2 ⟨hF.1, hF.2⟩
      _ = 2 ^ (E.card - n.choose 2) := by
          rw [Finset.card_powerset, Finset.card_sdiff_of_subset hsub, hES]
  have hbound : 2 ^ E.card ≤ N.choose n * (2 * 2 ^ (E.card - n.choose 2)) := by
    calc 2 ^ E.card = E.powerset.card := (Finset.card_powerset E).symm
      _ ≤ ((Finset.univ.powersetCard n).biUnion (fun S => Bc S ∪ Bi S)).card :=
          Finset.card_le_card hcover
      _ ≤ ∑ S ∈ Finset.univ.powersetCard n, (Bc S ∪ Bi S).card := Finset.card_biUnion_le
      _ ≤ ∑ S ∈ Finset.univ.powersetCard n, (2 * 2 ^ (E.card - n.choose 2)) := by
          refine Finset.sum_le_sum fun S hS => ?_
          have hSn : S.card = n := (Finset.mem_powersetCard.1 hS).2
          calc (Bc S ∪ Bi S).card ≤ (Bc S).card + (Bi S).card := Finset.card_union_le _ _
            _ ≤ 2 ^ (E.card - n.choose 2) + 2 ^ (E.card - n.choose 2) :=
                add_le_add (hBc S hSn) (hBi S hSn)
            _ = 2 * 2 ^ (E.card - n.choose 2) := by ring
      _ = N.choose n * (2 * 2 ^ (E.card - n.choose 2)) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
  rcases lt_or_ge N n with hNn | hnN
  · rw [Nat.choose_eq_zero_of_lt hNn, zero_mul] at hbound
    exact absurd hbound (not_le.2 (by positivity))
  · have ha : n.choose 2 ≤ E.card := by rw [hEcard]; exact Nat.choose_le_choose 2 hnN
    have h1 : 2 ^ (E.card - n.choose 2) * 2 ^ (n.choose 2) ≤
        2 ^ (E.card - n.choose 2) * (2 * N.choose n) := by
      calc 2 ^ (E.card - n.choose 2) * 2 ^ (n.choose 2) = 2 ^ E.card := by
            rw [← pow_add, Nat.sub_add_cancel ha]
        _ ≤ N.choose n * (2 * 2 ^ (E.card - n.choose 2)) := hbound
        _ = 2 ^ (E.card - n.choose 2) * (2 * N.choose n) := by ring
    have h2 := Nat.le_of_mul_le_mul_left h1 (by positivity)
    omega


/-! ### Existence of diagonal Ramsey thresholds -/

lemma ramsey_nonempty (k : ℕ) :
    ∃ N : ℕ, ∀ G : SimpleGraph (Fin N),
      (∃ s : Finset (Fin N), G.IsNClique k s) ∨ (∃ s : Finset (Fin N), Gᶜ.IsNClique k s) := by
  obtain ⟨N, h⟩ := ramsey_exists_aux k k
  refine ⟨N, fun G => ?_⟩
  have := h (Fin N) G Finset.univ (by rw [Finset.card_univ, Fintype.card_fin])
  rcases this with ⟨s, -, hs⟩ | ⟨s, -, hs⟩
  · exact Or.inl ⟨s, hs⟩
  · exact Or.inr ⟨s, (SimpleGraph.isNClique_compl G).2 hs⟩

/-! ### The numerical inequality -/

lemma fact_sq_gt (k : ℕ) (hk : 3 ≤ k) : 2 ^ (k + 2) < (k.factorial) ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ k hk ih =>
    rw [Nat.factorial_succ, mul_pow, show k + 1 + 2 = (k + 2) + 1 by ring, pow_succ]
    have h16 : 2 ≤ (k + 1) ^ 2 := by nlinarith
    nlinarith

lemma numeric (k N : ℕ) (hk : 3 ≤ k) (hN : N ^ 2 ≤ 2 ^ k) :
    2 * N.choose k < 2 ^ (k.choose 2) := by
  by_contra hcon
  push Not at hcon
  have h1 : 2 ^ (k.choose 2) * k.factorial ≤ 2 * N ^ k := by
    calc 2 ^ (k.choose 2) * k.factorial ≤ (2 * N.choose k) * k.factorial :=
          Nat.mul_le_mul_right _ hcon
      _ = 2 * (k.factorial * N.choose k) := by ring
      _ = 2 * N.descFactorial k := by rw [Nat.descFactorial_eq_factorial_mul_choose]
      _ ≤ 2 * N ^ k := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow N k)
  have h2 : (2 ^ (k.choose 2) * k.factorial) ^ 2 ≤ (2 * N ^ k) ^ 2 := Nat.pow_le_pow_left h1 2
  have hC : k.choose 2 * 2 = k * (k - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.div_mul_cancel (Nat.even_mul_pred_self k).two_dvd
  have h3 : (2 ^ (k.choose 2) * k.factorial) ^ 2 = 2 ^ (k * (k - 1)) * (k.factorial) ^ 2 := by
    rw [mul_pow, ← pow_mul, hC]
  have h4 : (2 * N ^ k) ^ 2 ≤ 4 * 2 ^ (k * k) := by
    calc (2 * N ^ k) ^ 2 = 4 * (N ^ 2) ^ k := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k 2]; norm_num
      _ ≤ 4 * (2 ^ k) ^ k := by gcongr
      _ = 4 * 2 ^ (k * k) := by rw [← pow_mul]
  have h5 : k * k = k * (k - 1) + k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have h6 : (k.factorial) ^ 2 ≤ 2 ^ (k + 2) := by
    have hpos : 0 < 2 ^ (k * (k - 1)) := by positivity
    have : 2 ^ (k * (k - 1)) * (k.factorial) ^ 2 ≤ 2 ^ (k * (k - 1)) * 2 ^ (k + 2) := by
      calc 2 ^ (k * (k - 1)) * (k.factorial) ^ 2
          = (2 ^ (k.choose 2) * k.factorial) ^ 2 := h3.symm
        _ ≤ (2 * N ^ k) ^ 2 := h2
        _ ≤ 4 * 2 ^ (k * k) := h4
        _ = 2 ^ (k * (k - 1)) * 2 ^ (k + 2) := by
          rw [h5, pow_add, pow_add]; ring
    exact Nat.le_of_mul_le_mul_left this hpos
  exact absurd (fact_sq_gt k hk) (not_lt.2 h6)

end Erdos77Aux

/-- Erdős 1947: `2^{k/2} < R(k)` for `k ≥ 3`. -/
theorem solution (k : ℕ) (hk : 3 ≤ k) :
    (2 : ℝ) ^ ((k : ℝ) / 2) < (Erdos77.diagonalRamsey k : ℝ) := by
  obtain ⟨N0, hN0⟩ := Erdos77Aux.ramsey_nonempty k
  have hmem := Nat.sInf_mem (s := {n : ℕ | ∀ G : SimpleGraph (Fin n),
    (∃ s : Finset (Fin n), G.IsNClique k s) ∨ (∃ s : Finset (Fin n), Gᶜ.IsNClique k s)})
    ⟨N0, hN0⟩
  change ∀ G : SimpleGraph (Fin (Erdos77.diagonalRamsey k)),
    (∃ s : Finset (Fin (Erdos77.diagonalRamsey k)), G.IsNClique k s) ∨
      (∃ s : Finset (Fin (Erdos77.diagonalRamsey k)), Gᶜ.IsNClique k s) at hmem
  by_contra hcon
  push Not at hcon
  set R := Erdos77.diagonalRamsey k with hR
  have hsq : R ^ 2 ≤ 2 ^ k := by
    have h : (R : ℝ) ^ 2 ≤ (2 : ℝ) ^ k := by
      calc (R : ℝ) ^ 2 ≤ ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hcon 2
        _ = (2 : ℝ) ^ k := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          rw [show (k : ℝ) / 2 * ((2 : ℕ) : ℝ) = (k : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact_mod_cast h
  obtain ⟨G, hG1, hG2⟩ := Erdos77Aux.exists_good_graph R k (Erdos77Aux.numeric k R hk hsq)
  rcases hmem G with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact hG1 s hs
  · exact hG2 s ((SimpleGraph.isNClique_compl G).1 hs)
