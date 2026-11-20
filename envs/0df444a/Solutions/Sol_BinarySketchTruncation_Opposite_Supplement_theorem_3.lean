-- Prove2me | solution 1 for BinarySketchTruncation.Opposite.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:28:21.36993+00:00
-- url     : https://prove2.me/submissions/13437823-d0a8-4077-94fe-261e229c2c79

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Supplement_Connectivity
import Definitions.Def_BinarySketchTruncation_Opposite_Supplement_UnateEvaluation
import Theorems.Thm_BinarySketchTruncation_Opposite_Supplement_theorem_2
import Theorems.Thm_BinarySketchTruncation_Opposite_Supplement_lemma_3

section
namespace BinarySketchTruncation.Dev.T3Upper

open BinarySketchTruncation.Opposite BinarySketchTruncation.Opposite.Supplement

lemma reach_iff {V : Type} (G : SimpleGraph V) (C : V → Prop)
    (hiso : ∀ x, ¬ C x → ∀ w, ¬ G.Adj x w)
    (hconn : ∀ x y, C x → C y → G.Reachable x y) (x y : V) :
    G.Reachable x y ↔ (x = y ∨ (C x ∧ C y)) := by
  have key : ∀ x y, ¬ C x → G.Reachable x y → x = y := by
    intro x y hx ⟨w⟩
    cases w with
    | nil => rfl
    | cons h _ => exact absurd h (hiso x hx _)
  constructor
  · intro h
    by_cases hxy : x = y
    · exact Or.inl hxy
    · right
      constructor
      · by_contra hx; exact hxy (key x y hx h)
      · by_contra hy; exact hxy (key y x hy h.symm).symm
  · rintro (rfl | ⟨hx, hy⟩)
    · exact SimpleGraph.Reachable.refl _
    · exact hconn x y hx hy

lemma sup_reach_mono {V : Type} (G G' H : SimpleGraph V)
    (h : ∀ x y, G.Adj x y → G'.Reachable x y) :
    ∀ x y, (G ⊔ H).Reachable x y → (G' ⊔ H).Reachable x y := by
  intro x y ⟨w⟩
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    refine SimpleGraph.Reachable.trans ?_ ih
    rw [SimpleGraph.sup_adj] at hadj
    rcases hadj with h1 | h1
    · exact SimpleGraph.Reachable.mono le_sup_left (h _ _ h1)
    · exact SimpleGraph.Adj.reachable (by rw [SimpleGraph.sup_adj]; exact Or.inr h1)

lemma conn_iff {V : Type} (G G' H : SimpleGraph V)
    (h : ∀ x y, G.Reachable x y ↔ G'.Reachable x y) :
    (G ⊔ H).Connected ↔ (G' ⊔ H).Connected := by
  rw [SimpleGraph.connected_iff, SimpleGraph.connected_iff]
  constructor
  · rintro ⟨hp, hn⟩
    exact ⟨fun x y => sup_reach_mono G G' H (fun a b hab => (h a b).mp hab.reachable) x y (hp x y), hn⟩
  · rintro ⟨hp, hn⟩
    exact ⟨fun x y => sup_reach_mono G' G H (fun a b hab => (h a b).mpr hab.reachable) x y (hp x y), hn⟩

/-- The vertices that are "ok" (not an isolated right vertex listed in `S`). -/
def okV {v N : ℕ} (S : Finset (Fin N)) : Fin v ⊕ Fin N → Prop :=
  Sum.elim (fun _ => True) (fun j => j ∉ S)

/-- Decoder graph: complete graph on the ok vertices. -/
def decG {v N : ℕ} (S : Finset (Fin N)) : SimpleGraph (Fin v ⊕ Fin N) where
  Adj x y := x ≠ y ∧ okV S x ∧ okV S y
  symm := ⟨fun x y h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

def isoSet {v N : ℕ} (z : Fin v × Fin N → Bit) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun j => ∀ i, z (i, j) = 0)

lemma mem_isoSet {v N : ℕ} (z : Fin v × Fin N → Bit) (j : Fin N) :
    j ∈ isoSet z ↔ ∀ i, z (i, j) = 0 := by
  classical
  simp [isoSet]

lemma bit_ne_zero {b : Bit} (h : b ≠ 0) : b = 1 := by
  revert b; decide

lemma good_correct {v N : ℕ} (hv : 0 < v) (z : Fin v × Fin N → Bit)
    (hpair : ∀ i i', i ≠ i' → ∃ j, z (i, j) = 1 ∧ z (i', j) = 1)
    (H : SimpleGraph (Fin v ⊕ Fin N)) :
    (edgeGraph z ⊔ H).Connected ↔ (decG (isoSet z) ⊔ H).Connected := by
  apply conn_iff
  intro x y
  have hadj : ∀ i j, (edgeGraph z).Adj (Sum.inl i) (Sum.inr j) ↔ z (i, j) = 1 := fun _ _ => Iff.rfl
  have hbase : ∀ x, okV (isoSet z) x → (edgeGraph z).Reachable x (Sum.inl ⟨0, hv⟩) := by
    intro x hx
    have hl : ∀ i : Fin v, (edgeGraph z).Reachable (Sum.inl i) (Sum.inl ⟨0, hv⟩) := by
      intro i
      by_cases hi : i = ⟨0, hv⟩
      · rw [hi]
      · obtain ⟨j, hj1, hj2⟩ := hpair i ⟨0, hv⟩ hi
        have a1 : (edgeGraph z).Adj (Sum.inl i) (Sum.inr j) := (hadj _ _).mpr hj1
        have a2 : (edgeGraph z).Adj (Sum.inl ⟨0, hv⟩) (Sum.inr j) := (hadj _ _).mpr hj2
        exact a1.reachable.trans a2.symm.reachable
    cases x with
    | inl i => exact hl i
    | inr j =>
      have hj : j ∉ isoSet z := hx
      rw [mem_isoSet] at hj
      push Not at hj
      obtain ⟨i, hi⟩ := hj
      have a1 : (edgeGraph z).Adj (Sum.inl i) (Sum.inr j) := (hadj _ _).mpr (bit_ne_zero hi)
      exact a1.symm.reachable.trans (hl i)
  have h1 : ∀ x : Fin v ⊕ Fin N, ¬ okV (isoSet z) x → ∀ w, ¬ (edgeGraph z).Adj x w := by
    intro x hx w hw
    cases x with
    | inl i => exact hx trivial
    | inr j =>
      have hj : j ∈ isoSet z := by simpa [okV] using hx
      rw [mem_isoSet] at hj
      cases w with
      | inl i =>
        have : z (i, j) = 1 := hw
        rw [hj i] at this
        exact absurd this (by decide)
      | inr j' => exact hw
  have h2 : ∀ x : Fin v ⊕ Fin N, ¬ okV (isoSet z) x → ∀ w, ¬ (decG (isoSet z)).Adj x w := by
    intro x hx w hw
    exact hx hw.2.1
  have h3 : ∀ x y : Fin v ⊕ Fin N, okV (isoSet z) x → okV (isoSet z) y → (decG (isoSet z)).Reachable x y := by
    intro x y hx hy
    by_cases hxy : x = y
    · rw [hxy]
    · exact (show (decG (isoSet z)).Adj x y from ⟨hxy, hx, hy⟩).reachable
  have h4 : ∀ x y : Fin v ⊕ Fin N, okV (isoSet z) x → okV (isoSet z) y → (edgeGraph z).Reachable x y := by
    intro x y hx hy
    exact (hbase x hx).trans (hbase y hy).symm
  rw [reach_iff (edgeGraph z) (okV (isoSet z)) h1 h4, reach_iff (decG (isoSet z)) (okV (isoSet z)) h2 h3]


/-- Columns of the edge vector. -/
def colEquiv (v N : ℕ) : (Fin v × Fin N → Bit) ≃ (Fin N → Fin v → Bit) where
  toFun z := fun j i => z (i, j)
  invFun c := fun p => c p.2 p.1
  left_inv z := rfl
  right_inv c := rfl

lemma count_cols {v N : ℕ} (S : Fin N → Finset (Fin v → Bit)) :
    (Finset.univ.filter (fun z : Fin v × Fin N → Bit => ∀ j, (fun i => z (i, j)) ∈ S j)).card
      = ∏ j, (S j).card := by
  rw [← Fintype.card_piFinset S]
  apply Finset.card_equiv (colEquiv v N)
  intro z
  simp [Fintype.mem_piFinset, colEquiv]

lemma card_total (v N : ℕ) : Fintype.card (Fin v × Fin N → Bit) = (2 ^ v) ^ N := by
  simp [Fintype.card_fun, ZMod.card, Fintype.card_prod, pow_mul]

lemma countA (v N : ℕ) (T : Finset (Fin N)) :
    (Finset.univ.filter (fun z : Fin v × Fin N → Bit => ∀ j ∈ T, ∀ i, z (i, j) = 0)).card
      = (2 ^ v) ^ (N - T.card) := by
  classical
  have h := count_cols (v := v) (N := N)
    (fun j => if j ∈ T then ({0} : Finset (Fin v → Bit)) else Finset.univ)
  have e : (Finset.univ.filter (fun z : Fin v × Fin N → Bit => ∀ j ∈ T, ∀ i, z (i, j) = 0))
      = Finset.univ.filter (fun z : Fin v × Fin N → Bit => ∀ j, (fun i => z (i, j)) ∈
          (if j ∈ T then ({0} : Finset (Fin v → Bit)) else Finset.univ)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h j
      by_cases hj : j ∈ T
      · simp only [hj, if_true, Finset.mem_singleton]
        funext i; exact h j hj i
      · simp [hj]
    · intro h j hj i
      have := h j
      simp only [hj, if_true, Finset.mem_singleton] at this
      exact congrFun this i
  rw [e, h]
  have hc : ∀ j, (if j ∈ T then ({0} : Finset (Fin v → Bit)) else Finset.univ).card
      = if j ∈ T then 1 else 2 ^ v := by
    intro j
    by_cases hj : j ∈ T <;> simp [hj, Fintype.card_fun, ZMod.card]
  simp only [hc]
  rw [Finset.prod_ite]
  simp [Finset.filter_not, Finset.card_sdiff]


lemma card_Q (v : ℕ) (i i' : Fin v) (hne : i ≠ i') :
    (Finset.univ.filter (fun d : Fin v → Bit => d i = 1 ∧ d i' = 1)).card * 4 = 2 ^ v := by
  classical
  have hv : 2 ≤ v := by
    have := Finset.card_le_univ ({i, i'} : Finset (Fin v))
    rw [Finset.card_pair hne] at this
    simpa using this
  have e : Finset.univ.filter (fun d : Fin v → Bit => d i = 1 ∧ d i' = 1)
      = Fintype.piFinset (fun k => if k = i ∨ k = i' then ({1} : Finset Bit) else Finset.univ) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ k
      by_cases hk : k = i ∨ k = i'
      · rcases hk with rfl | rfl <;> simp [h1, h2]
      · simp [hk]
    · intro h
      have a1 := h i
      have a2 := h i'
      simp at a1 a2
      exact ⟨a1, a2⟩
  have hc : ∀ k : Fin v, (if k = i ∨ k = i' then ({1} : Finset Bit) else Finset.univ).card
      = if k = i ∨ k = i' then 1 else 2 := by
    intro k
    by_cases hk : k = i ∨ k = i' <;> simp [hk, ZMod.card]
  rw [e, Fintype.card_piFinset]
  simp only [hc]
  rw [Finset.prod_ite]
  have e2 : Finset.univ.filter (fun k : Fin v => ¬ (k = i ∨ k = i')) = Finset.univ \ {i, i'} := by
    ext k; simp
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const, e2, Finset.card_univ_sdiff,
    Finset.card_pair hne, Fintype.card_fin]
  obtain ⟨m, rfl⟩ : ∃ m, v = m + 2 := ⟨v - 2, by omega⟩
  simp [pow_succ]
  ring

lemma card_S (v : ℕ) (i i' : Fin v) (hne : i ≠ i') :
    (Finset.univ.filter (fun d : Fin v → Bit => ¬ (d i = 1 ∧ d i' = 1))).card * 4 = 3 * 2 ^ v := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin v → Bit)))
    (fun d : Fin v → Bit => d i = 1 ∧ d i' = 1)
  have h2 := card_Q v i i' hne
  have h3 : (Finset.univ : Finset (Fin v → Bit)).card = 2 ^ v := by
    simp [Fintype.card_fun, ZMod.card]
  omega

lemma countB {v N : ℕ} (i i' : Fin v) (hne : i ≠ i') :
    (Finset.univ.filter (fun z : Fin v × Fin N → Bit => ∀ j, ¬ (z (i, j) = 1 ∧ z (i', j) = 1))).card
      = (Finset.univ.filter (fun d : Fin v → Bit => ¬ (d i = 1 ∧ d i' = 1))).card ^ N := by
  classical
  have h := count_cols (v := v) (N := N)
    (fun _ => Finset.univ.filter (fun d : Fin v → Bit => ¬ (d i = 1 ∧ d i' = 1)))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  congr 1
  ext z
  simp


lemma bad_card {v N : ℕ} (E : (Fin v × Fin N → Bit) → Prop) [DecidablePred E] (s : ℕ)
    (hs : ∀ i i' : Fin v, i ≠ i' →
      (Finset.univ.filter (fun d : Fin v → Bit => ¬ (d i = 1 ∧ d i' = 1))).card = s)
    (hE : ∀ z, E z → 4 ≤ (isoSet z).card ∨
      ∃ i i', i ≠ i' ∧ ∀ j, ¬ (z (i, j) = 1 ∧ z (i', j) = 1)) :
    (Finset.univ.filter E).card ≤ N.choose 4 * (2 ^ v) ^ (N - 4) + v * v * s ^ N := by
  classical
  let A : Finset (Fin v × Fin N → Bit) :=
    (Finset.powersetCard 4 (Finset.univ : Finset (Fin N))).biUnion
      (fun T => Finset.univ.filter (fun z : Fin v × Fin N → Bit => ∀ j ∈ T, ∀ i, z (i, j) = 0))
  let B : Finset (Fin v × Fin N → Bit) :=
    (Finset.univ.filter (fun p : Fin v × Fin v => p.1 ≠ p.2)).biUnion
      (fun p => Finset.univ.filter
        (fun z : Fin v × Fin N → Bit => ∀ j, ¬ (z (p.1, j) = 1 ∧ z (p.2, j) = 1)))
  have hsub : Finset.univ.filter E ⊆ A ∪ B := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    rw [Finset.mem_union]
    rcases hE z hz with h | ⟨i, i', hne, h⟩
    · left
      obtain ⟨T, hT, hT4⟩ := Finset.exists_subset_card_eq h
      simp only [A, Finset.mem_biUnion, Finset.mem_powersetCard, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨T, ⟨Finset.subset_univ _, hT4⟩, fun j hj i => ?_⟩
      exact (mem_isoSet z j).mp (hT hj) i
    · right
      simp only [B, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(i, i'), hne, h⟩
  have hA : A.card ≤ N.choose 4 * (2 ^ v) ^ (N - 4) := by
    calc A.card ≤ ∑ T ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin N)),
          (Finset.univ.filter (fun z : Fin v × Fin N → Bit => ∀ j ∈ T, ∀ i, z (i, j) = 0)).card :=
          Finset.card_biUnion_le
      _ = ∑ T ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin N)), (2 ^ v) ^ (N - 4) := by
          apply Finset.sum_congr rfl
          intro T hT
          rw [countA, (Finset.mem_powersetCard.mp hT).2]
      _ = N.choose 4 * (2 ^ v) ^ (N - 4) := by
          simp [Finset.card_powersetCard]
  have hB : B.card ≤ v * v * s ^ N := by
    calc B.card ≤ ∑ p ∈ Finset.univ.filter (fun p : Fin v × Fin v => p.1 ≠ p.2),
          (Finset.univ.filter
            (fun z : Fin v × Fin N → Bit => ∀ j, ¬ (z (p.1, j) = 1 ∧ z (p.2, j) = 1))).card :=
          Finset.card_biUnion_le
      _ = ∑ p ∈ Finset.univ.filter (fun p : Fin v × Fin v => p.1 ≠ p.2), s ^ N := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          rw [countB p.1 p.2 hp, hs p.1 p.2 hp]
      _ ≤ v * v * s ^ N := by
          rw [Finset.sum_const, smul_eq_mul]
          apply Nat.mul_le_mul_right
          calc _ ≤ (Finset.univ : Finset (Fin v × Fin v)).card := Finset.card_filter_le _ _
            _ = v * v := by simp
  calc (Finset.univ.filter E).card ≤ (A ∪ B).card := Finset.card_le_card hsub
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add hA hB


lemma prob_bound {v N : ℕ} (hv : 2 ≤ v) (hN : N = 2 ^ v)
    (E : (Fin v × Fin N → Bit) → Prop) [DecidablePred E]
    (hE : ∀ z, E z → 4 ≤ (isoSet z).card ∨
      ∃ i i', i ≠ i' ∧ ∀ j, ¬ (z (i, j) = 1 ∧ z (i', j) = 1)) :
    ((Finset.univ.filter E).card : ℝ) / Fintype.card (Fin v × Fin N → Bit)
      ≤ 1 / 24 + v * v * (3 / 4 : ℝ) ^ N := by
  classical
  let s := (Finset.univ.filter (fun d : Fin v → Bit =>
    ¬ (d ⟨0, by omega⟩ = 1 ∧ d ⟨1, by omega⟩ = 1))).card
  have hs4 : s * 4 = 3 * 2 ^ v := card_S v ⟨0, by omega⟩ ⟨1, by omega⟩ (by
    intro h; have := congrArg Fin.val h; simp at this)
  have hs : ∀ i i' : Fin v, i ≠ i' →
      (Finset.univ.filter (fun d : Fin v → Bit => ¬ (d i = 1 ∧ d i' = 1))).card = s := by
    intro i i' hne
    have := card_S v i i' hne
    omega
  have hb := bad_card E s hs hE
  rw [card_total]
  have hc : (0 : ℝ) < ((2 : ℝ) ^ v) ^ N := by positivity
  push_cast
  rw [div_le_iff₀ (by exact_mod_cast hc)]
  have hbR : ((Finset.univ.filter E).card : ℝ) ≤
      (N.choose 4 : ℝ) * ((2 : ℝ) ^ v) ^ (N - 4) + v * v * (s : ℝ) ^ N := by
    exact_mod_cast hb
  have hsR : (s : ℝ) = 3 / 4 * 2 ^ v := by
    have : (s : ℝ) * 4 = 3 * 2 ^ v := by exact_mod_cast hs4
    linarith
  have hN4 : 4 ≤ N := by
    rw [hN]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv
  have hch : (N.choose 4 : ℝ) ≤ ((2 : ℝ) ^ v) ^ 4 / 24 := by
    have := Nat.choose_le_pow_div (α := ℝ) 4 N
    have e : ((N : ℕ) : ℝ) = 2 ^ v := by rw [hN]; push_cast; rfl
    rw [e] at this
    simpa [Nat.factorial] using this
  have hpow : ((2 : ℝ) ^ v) ^ N = ((2 : ℝ) ^ v) ^ 4 * ((2 : ℝ) ^ v) ^ (N - 4) := by
    rw [← pow_add]; congr 1; omega
  have hpos : (0 : ℝ) ≤ ((2 : ℝ) ^ v) ^ (N - 4) := by positivity
  have t1 : (N.choose 4 : ℝ) * ((2 : ℝ) ^ v) ^ (N - 4) ≤ 1 / 24 * ((2 : ℝ) ^ v) ^ N := by
    rw [hpow]
    calc (N.choose 4 : ℝ) * ((2 : ℝ) ^ v) ^ (N - 4)
        ≤ ((2 : ℝ) ^ v) ^ 4 / 24 * ((2 : ℝ) ^ v) ^ (N - 4) :=
          mul_le_mul_of_nonneg_right hch hpos
      _ = _ := by ring
  have t2 : (s : ℝ) ^ N = (3 / 4 : ℝ) ^ N * ((2 : ℝ) ^ v) ^ N := by
    rw [hsR, mul_pow]
  rw [t2] at hbR
  calc ((Finset.univ.filter E).card : ℝ) ≤ _ := hbR
    _ ≤ _ := by nlinarith [t1]


lemma prob_eq {Ω : Type} [Fintype Ω] [Nonempty Ω] (E : Ω → Prop) [DecidablePred E] :
    uniformProbability E = ((Finset.univ.filter E).card : ℝ) / Fintype.card Ω := by
  classical
  unfold uniformProbability uniformMean
  simp only
  congr 2
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : E x <;> simp [h]

lemma card_small (N : ℕ) (hN : 1 ≤ N) :
    Fintype.card {S : Finset (Fin N) // S.card ≤ 3} ≤ 4 * N ^ 3 := by
  classical
  rw [Fintype.card_subtype]
  have hsub : (Finset.univ.filter (fun S : Finset (Fin N) => S.card ≤ 3)) ⊆
      (Finset.range 4).biUnion (fun k => Finset.powersetCard k (Finset.univ : Finset (Fin N))) := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
    exact ⟨S.card, by omega, Finset.subset_univ _, rfl⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range 4, (Finset.powersetCard k (Finset.univ : Finset (Fin N))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range 4, N ^ 3 := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
        calc N.choose k ≤ N ^ k := Nat.choose_le_pow _ _
          _ ≤ N ^ 3 := Nat.pow_le_pow_right hN (by simp at hk; omega)
    _ = 4 * N ^ 3 := by simp

lemma pow_ge (v : ℕ) (hv : 14 ≤ v) : 60 * (v * v) ≤ 2 ^ v := by
  induction v, hv using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    nlinarith

lemma small_tail (v : ℕ) (hv : 14 ≤ v) :
    (v : ℝ) * v * (3 / 4 : ℝ) ^ (2 ^ v) ≤ 1 / 20 := by
  have h1 : 1 + ((2 ^ v : ℕ) : ℝ) * (1 / 3) ≤ (4 / 3 : ℝ) ^ (2 ^ v) := by
    have := one_add_mul_le_pow (R := ℝ) (a := 1 / 3) (by norm_num) (2 ^ v)
    norm_num at this ⊢
    linarith
  have h2 : (3 / 4 : ℝ) ^ (2 ^ v) = 1 / (4 / 3 : ℝ) ^ (2 ^ v) := by
    rw [one_div, ← inv_pow]; norm_num
  have hpos : (0 : ℝ) < (4 / 3 : ℝ) ^ (2 ^ v) := by positivity
  have h3 : (60 : ℝ) * (v * v) ≤ 2 ^ v := by exact_mod_cast pow_ge v hv
  rw [h2, mul_one_div, div_le_iff₀ hpos]
  push_cast at h1
  nlinarith

theorem upper : ∃ v₀ : ℕ, ∀ v ≥ v₀,
    ∃ (φ : ((Fin v × Fin (2 ^ v)) → Bit) → Vec (3 * v + 3))
      (g : Vec (3 * v + 3) → SimpleGraph (Fin v ⊕ Fin (2 ^ v)) → Bool),
      ∀ H, connectivityError φ g H ≤ (1 / 10 : ℝ) := by
  classical
  refine ⟨14, fun v hv => ?_⟩
  have hvpos : 0 < v := by omega
  have hcard : Fintype.card {S : Finset (Fin (2 ^ v)) // S.card ≤ 3}
      ≤ Fintype.card (Vec (3 * v + 3)) := by
    have h1 := card_small (2 ^ v) (Nat.one_le_two_pow)
    have h2 : Fintype.card (Vec (3 * v + 3)) = 8 * (2 ^ v) ^ 3 := by
      have : Fintype.card (Vec (3 * v + 3)) = 2 ^ (3 * v + 3) := by
        simp [Vec, Fintype.card_fun, ZMod.card]
      rw [this, pow_add, pow_mul']
      ring
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let T := {S : Finset (Fin (2 ^ v)) // S.card ≤ 3}
  have : Nonempty T := ⟨⟨∅, by simp⟩⟩
  let pick : (Fin v × Fin (2 ^ v) → Bit) → T := fun z =>
    if h : (isoSet z).card ≤ 3 then ⟨isoSet z, h⟩ else ⟨∅, by simp⟩
  refine ⟨fun z => e (pick z),
    fun m H => decide ((decG (Function.invFun e m).1 ⊔ H).Connected), fun H => ?_⟩
  unfold connectivityError
  rw [prob_eq]
  have key : ∀ z : Fin v × Fin (2 ^ v) → Bit,
      (fun m H => decide ((decG (Function.invFun e m).1 ⊔ H).Connected)) (e (pick z)) H
        ≠ decide ((edgeGraph z ⊔ H).Connected) →
      4 ≤ (isoSet z).card ∨
        ∃ i i', i ≠ i' ∧ ∀ j, ¬ (z (i, j) = 1 ∧ z (i', j) = 1) := by
    intro z hz
    by_contra hcon
    push Not at hcon
    obtain ⟨h4, hp⟩ := hcon
    apply hz
    have hp' : ∀ i i', i ≠ i' → ∃ j, z (i, j) = 1 ∧ z (i', j) = 1 := hp
    have hpk : pick z = ⟨isoSet z, by omega⟩ := by
      simp only [pick]
      rw [dif_pos (by omega)]
    simp only [hpk, Function.leftInverse_invFun e.injective _]
    rw [decide_eq_decide]
    exact (good_correct hvpos z hp' H).symm
  have hb := prob_bound (v := v) (N := 2 ^ v) (by omega) rfl _ key
  have ht := small_tail v hv
  refine hb.trans ?_
  linarith

end BinarySketchTruncation.Dev.T3Upper
end

section
namespace BinarySketchTruncation.Dev.T3Prob

open BinarySketchTruncation.Opposite BinarySketchTruncation.Opposite.Supplement

/-- Columns of the edge vector. -/
def colEquiv (v N : ℕ) : (Fin v × Fin N → Bit) ≃ (Fin N → Fin v → Bit) where
  toFun z := fun j i => z (i, j)
  invFun c := fun p => c p.2 p.1
  left_inv z := rfl
  right_inv c := rfl

lemma count_cols {v N : ℕ} (S : Fin N → Finset (Fin v → Bit)) :
    (Finset.univ.filter (fun z : Fin v × Fin N → Bit => ∀ j, (fun i => z (i, j)) ∈ S j)).card
      = ∏ j, (S j).card := by
  rw [← Fintype.card_piFinset S]
  apply Finset.card_equiv (colEquiv v N)
  intro z
  simp [Fintype.mem_piFinset, colEquiv]

lemma card_total (v N : ℕ) : Fintype.card (Fin v × Fin N → Bit) = (2 ^ v) ^ N := by
  simp [Fintype.card_fun, ZMod.card, Fintype.card_prod, pow_mul]


lemma card_Q (v : ℕ) (i i' : Fin v) (hne : i ≠ i') :
    (Finset.univ.filter (fun d : Fin v → Bit => d i = 1 ∧ d i' = 1)).card * 4 = 2 ^ v := by
  classical
  have hv : 2 ≤ v := by
    have := Finset.card_le_univ ({i, i'} : Finset (Fin v))
    rw [Finset.card_pair hne] at this
    simpa using this
  have e : Finset.univ.filter (fun d : Fin v → Bit => d i = 1 ∧ d i' = 1)
      = Fintype.piFinset (fun k => if k = i ∨ k = i' then ({1} : Finset Bit) else Finset.univ) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ k
      by_cases hk : k = i ∨ k = i'
      · rcases hk with rfl | rfl <;> simp [h1, h2]
      · simp [hk]
    · intro h
      have a1 := h i
      have a2 := h i'
      simp at a1 a2
      exact ⟨a1, a2⟩
  have hc : ∀ k : Fin v, (if k = i ∨ k = i' then ({1} : Finset Bit) else Finset.univ).card
      = if k = i ∨ k = i' then 1 else 2 := by
    intro k
    by_cases hk : k = i ∨ k = i' <;> simp [hk, ZMod.card]
  rw [e, Fintype.card_piFinset]
  simp only [hc]
  rw [Finset.prod_ite]
  have e2 : Finset.univ.filter (fun k : Fin v => ¬ (k = i ∨ k = i')) = Finset.univ \ {i, i'} := by
    ext k; simp
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const, e2, Finset.card_univ_sdiff,
    Finset.card_pair hne, Fintype.card_fin]
  obtain ⟨m, rfl⟩ : ∃ m, v = m + 2 := ⟨v - 2, by omega⟩
  simp [pow_succ]
  ring

lemma card_S (v : ℕ) (i i' : Fin v) (hne : i ≠ i') :
    (Finset.univ.filter (fun d : Fin v → Bit => ¬ (d i = 1 ∧ d i' = 1))).card * 4 = 3 * 2 ^ v := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin v → Bit)))
    (fun d : Fin v → Bit => d i = 1 ∧ d i' = 1)
  have h2 := card_Q v i i' hne
  have h3 : (Finset.univ : Finset (Fin v → Bit)).card = 2 ^ v := by
    simp [Fintype.card_fun, ZMod.card]
  omega

lemma countB {v N : ℕ} (i i' : Fin v) (hne : i ≠ i') :
    (Finset.univ.filter (fun z : Fin v × Fin N → Bit => ∀ j, ¬ (z (i, j) = 1 ∧ z (i', j) = 1))).card
      = (Finset.univ.filter (fun d : Fin v → Bit => ¬ (d i = 1 ∧ d i' = 1))).card ^ N := by
  classical
  have h := count_cols (v := v) (N := N)
    (fun _ => Finset.univ.filter (fun d : Fin v → Bit => ¬ (d i = 1 ∧ d i' = 1)))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  congr 1
  ext z
  simp



lemma prob_eq {Ω : Type} [Fintype Ω] [Nonempty Ω] (E : Ω → Prop) [DecidablePred E] :
    uniformProbability E = ((Finset.univ.filter E).card : ℝ) / Fintype.card Ω := by
  classical
  unfold uniformProbability uniformMean
  simp only
  congr 2
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : E x <;> simp [h]


lemma bit_ne_zero {b : Bit} (h : b ≠ 0) : b = 1 := by
  revert b; decide


lemma pairfail_card {v N : ℕ} (s : ℕ)
    (hs : ∀ i i' : Fin v, i ≠ i' →
      (Finset.univ.filter (fun d : Fin v → Bit => ¬ (d i = 1 ∧ d i' = 1))).card = s) :
    (Finset.univ.filter (fun z : Fin v × Fin N → Bit =>
      ∃ i i', i ≠ i' ∧ ∀ j, ¬ (z (i, j) = 1 ∧ z (i', j) = 1))).card ≤ v * v * s ^ N := by
  classical
  let B : Finset (Fin v × Fin N → Bit) :=
    (Finset.univ.filter (fun p : Fin v × Fin v => p.1 ≠ p.2)).biUnion
      (fun p => Finset.univ.filter
        (fun z : Fin v × Fin N → Bit => ∀ j, ¬ (z (p.1, j) = 1 ∧ z (p.2, j) = 1)))
  have hsub : (Finset.univ.filter (fun z : Fin v × Fin N → Bit =>
      ∃ i i', i ≠ i' ∧ ∀ j, ¬ (z (i, j) = 1 ∧ z (i', j) = 1))) ⊆ B := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨i, i', hne, h⟩ := hz
    simp only [B, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(i, i'), hne, h⟩
  have hB : B.card ≤ v * v * s ^ N := by
    calc B.card ≤ ∑ p ∈ Finset.univ.filter (fun p : Fin v × Fin v => p.1 ≠ p.2),
          (Finset.univ.filter
            (fun z : Fin v × Fin N → Bit => ∀ j, ¬ (z (p.1, j) = 1 ∧ z (p.2, j) = 1))).card :=
          Finset.card_biUnion_le
      _ = ∑ p ∈ Finset.univ.filter (fun p : Fin v × Fin v => p.1 ≠ p.2), s ^ N := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          rw [countB p.1 p.2 hp, hs p.1 p.2 hp]
      _ ≤ v * v * s ^ N := by
          rw [Finset.sum_const, smul_eq_mul]
          apply Nat.mul_le_mul_right
          calc _ ≤ (Finset.univ : Finset (Fin v × Fin v)).card := Finset.card_filter_le _ _
            _ = v * v := by simp
  exact (Finset.card_le_card hsub).trans hB

lemma countNoIso (v N : ℕ) :
    (Finset.univ.filter (fun z : Fin v × Fin N → Bit => ∀ j, ∃ i, z (i, j) ≠ 0)).card
      = (2 ^ v - 1) ^ N := by
  classical
  have h := count_cols (v := v) (N := N) (fun _ => Finset.univ.erase 0)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.card_erase_of_mem (Finset.mem_univ _)] at h
  have e : (Finset.univ.filter (fun z : Fin v × Fin N → Bit => ∀ j, ∃ i, z (i, j) ≠ 0))
      = Finset.univ.filter (fun z : Fin v × Fin N → Bit =>
          ∀ j, (fun i => z (i, j)) ∈ (Finset.univ.erase (0 : Fin v → Bit))) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, and_true]
    constructor
    · intro hz j hj
      obtain ⟨i, hi⟩ := hz j
      exact hi (congrFun hj i)
    · intro hz j
      by_contra hcon
      push Not at hcon
      exact hz j (funext hcon)
  rw [e, h]
  simp [Fintype.card_fun, ZMod.card]

lemma conn_noiso {v N : ℕ} (hv : 0 < v) (z : Fin v × Fin N → Bit)
    (hc : (edgeGraph z).Connected) : ∀ j, ∃ i, z (i, j) ≠ 0 := by
  intro j
  by_contra hcon
  push Not at hcon
  obtain ⟨w⟩ := hc.preconnected (Sum.inr j) (Sum.inl ⟨0, hv⟩)
  cases w with
  | cons h p =>
    rename_i u
    cases u with
    | inl i =>
      have : z (i, j) = 1 := h
      rw [hcon] at this
      exact absurd this (by decide)
    | inr j' => exact h

lemma noiso_conn {v N : ℕ} (hv : 0 < v) (z : Fin v × Fin N → Bit)
    (hno : ∀ j, ∃ i, z (i, j) ≠ 0)
    (hpair : ∀ i i', i ≠ i' → ∃ j, z (i, j) = 1 ∧ z (i', j) = 1) :
    (edgeGraph z).Connected := by
  have hadj : ∀ i j, (edgeGraph z).Adj (Sum.inl i) (Sum.inr j) ↔ z (i, j) = 1 :=
    fun _ _ => Iff.rfl
  have hl : ∀ i : Fin v, (edgeGraph z).Reachable (Sum.inl i) (Sum.inl ⟨0, hv⟩) := by
    intro i
    by_cases hi : i = ⟨0, hv⟩
    · rw [hi]
    · obtain ⟨j, hj1, hj2⟩ := hpair i ⟨0, hv⟩ hi
      have a1 : (edgeGraph z).Adj (Sum.inl i) (Sum.inr j) := (hadj _ _).mpr hj1
      have a2 : (edgeGraph z).Adj (Sum.inl ⟨0, hv⟩) (Sum.inr j) := (hadj _ _).mpr hj2
      exact a1.reachable.trans a2.symm.reachable
  have hbase : ∀ x, (edgeGraph z).Reachable x (Sum.inl ⟨0, hv⟩) := by
    intro x
    cases x with
    | inl i => exact hl i
    | inr j =>
      obtain ⟨i, hi⟩ := hno j
      have a1 : (edgeGraph z).Adj (Sum.inl i) (Sum.inr j) := (hadj _ _).mpr (bit_ne_zero hi)
      exact a1.symm.reachable.trans (hl i)
  rw [SimpleGraph.connected_iff]
  exact ⟨fun x y => (hbase x).trans (hbase y).symm, ⟨Sum.inl ⟨0, hv⟩⟩⟩

lemma connBool_iff {a b : ℕ} (z : Fin a × Fin b → Bit) :
    connectivityBool z = true ↔ (edgeGraph z).Connected := by
  unfold connectivityBool
  simp

lemma q_upper (N : ℕ) (hN : 1 ≤ N) : (1 - 1 / (N : ℝ)) ^ N ≤ 2 / 5 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h0 : (0 : ℝ) ≤ 1 - 1 / (N : ℝ) := by
    have : 1 / (N : ℝ) ≤ 1 := by
      rw [div_le_one hNpos]; exact_mod_cast hN
    linarith
  have h1 : 1 - 1 / (N : ℝ) ≤ Real.exp (-(1 / (N : ℝ))) := by
    have := Real.add_one_le_exp (-(1 / (N : ℝ)))
    linarith
  have h2 := pow_le_pow_left₀ h0 h1 N
  have h3 : Real.exp (-(1 / (N : ℝ))) ^ N = Real.exp (-1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [h3] at h2
  refine h2.trans ?_
  rw [Real.exp_neg]
  have := Real.exp_one_gt_d9
  rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
  norm_num at this ⊢
  linarith

lemma q_lower (n : ℕ) (hn : 10 ≤ n) : 1 / 3 ≤ (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
  have hn' : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set y : ℝ := 1 + 1 / (n : ℝ) with hy
  have hy1 : y ≤ 11 / 10 := by
    rw [hy]
    have : 1 / (n : ℝ) ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hn'
    linarith
  have hy0 : 0 < y := by rw [hy]; positivity
  have hx : (1 - 1 / ((n + 1 : ℕ) : ℝ)) * y = 1 := by
    rw [hy]; push_cast; field_simp; ring
  have hexp : y ^ n ≤ Real.exp 1 := by
    have h1 : y ≤ Real.exp (1 / (n : ℝ)) := by
      have := Real.add_one_le_exp (1 / (n : ℝ))
      rw [hy]; linarith
    have := pow_le_pow_left₀ hy0.le h1 n
    refine this.trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hmain : y ^ (n + 1) ≤ 3 := by
    rw [pow_succ]
    have := Real.exp_one_lt_d9
    have e1 : Real.exp 1 < 2.72 := by norm_num at this ⊢; linarith
    calc y ^ n * y ≤ Real.exp 1 * (11 / 10) :=
          mul_le_mul hexp hy1 hy0.le (Real.exp_pos 1).le
      _ ≤ 3 := by nlinarith
  have hxy : (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^ (n + 1) * y ^ (n + 1) = 1 := by
    rw [← mul_pow, hx, one_pow]
  have hpos : 0 < y ^ (n + 1) := by positivity
  have hxpos : 0 ≤ (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
    have : 0 ≤ 1 - 1 / ((n + 1 : ℕ) : ℝ) := by
      have : 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]; push_cast; linarith
      linarith
    positivity
  nlinarith

lemma pow_ge (v : ℕ) (hv : 16 ≤ v) : 150 * (v * v) ≤ 2 ^ v := by
  induction v, hv using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    nlinarith

lemma small_tail (v : ℕ) (hv : 16 ≤ v) :
    (v : ℝ) * v * (3 / 4 : ℝ) ^ (2 ^ v) ≤ 1 / 50 := by
  have h1 : 1 + ((2 ^ v : ℕ) : ℝ) * (1 / 3) ≤ (4 / 3 : ℝ) ^ (2 ^ v) := by
    have := one_add_mul_le_pow (R := ℝ) (a := 1 / 3) (by norm_num) (2 ^ v)
    norm_num at this ⊢
    linarith
  have h2 : (3 / 4 : ℝ) ^ (2 ^ v) = 1 / (4 / 3 : ℝ) ^ (2 ^ v) := by
    rw [one_div, ← inv_pow]; norm_num
  have hpos : (0 : ℝ) < (4 / 3 : ℝ) ^ (2 ^ v) := by positivity
  have h3 : (150 : ℝ) * (v * v) ≤ 2 ^ v := by exact_mod_cast pow_ge v hv
  rw [h2, mul_one_div, div_le_iff₀ hpos]
  push_cast at h1
  nlinarith

/-- The variance of the connectivity indicator is `p - p²`. -/
theorem variance_eq (a b : ℕ) :
    uniformVariance (connectivityIndicator (a := a) (b := b))
      = uniformProbability (fun z : Fin a × Fin b → Bit => connectivityBool z = true)
        - uniformProbability (fun z : Fin a × Fin b → Bit => connectivityBool z = true) ^ 2 := by
  classical
  have hm : uniformMean (connectivityIndicator (a := a) (b := b))
      = uniformProbability (fun z : Fin a × Fin b → Bit => connectivityBool z = true) := by
    unfold uniformProbability
    congr 1
    funext z
    unfold connectivityIndicator
    by_cases h : connectivityBool z = true <;> simp [h]
  rw [uniformVariance, hm]
  set p := uniformProbability (fun z : Fin a × Fin b → Bit => connectivityBool z = true) with hp
  have hcard : (Fintype.card (Fin a × Fin b → Bit) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (Fin a × Fin b → Bit) := Fintype.card_pos
    exact_mod_cast this.ne'
  have hsq : ∀ z, (connectivityIndicator (a := a) (b := b) z - p) ^ 2
      = connectivityIndicator z * (1 - 2 * p) + p ^ 2 := by
    intro z
    unfold connectivityIndicator
    by_cases h : connectivityBool z = true <;> simp [h] <;> ring
  unfold uniformMean
  simp only [hsq]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hm2 : (∑ z, connectivityIndicator (a := a) (b := b) z)
      / Fintype.card (Fin a × Fin b → Bit) = p := by
    rw [← hm]; rfl
  field_simp
  have : (∑ z, connectivityIndicator (a := a) (b := b) z) = p * Fintype.card (Fin a × Fin b → Bit) := by
    field_simp at hm2; linarith
  rw [this]
  ring

theorem prob : ∃ v₀ : ℕ, ∀ v ≥ v₀,
    (1 / 5 : ℝ) ≤ uniformProbability (fun z : Fin v × Fin (2 ^ v) → Bit => connectivityBool z = true)
      * (1 - uniformProbability (fun z : Fin v × Fin (2 ^ v) → Bit => connectivityBool z = true)) := by
  classical
  refine ⟨16, fun v hv => ?_⟩
  have hv0 : 0 < v := by omega
  have hv2 : 2 ≤ v := by omega
  have hN11 : 11 ≤ 2 ^ v :=
    calc 11 ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq1 : 1 / 3 ≤ (1 - 1 / ((2 ^ v : ℕ) : ℝ)) ^ (2 ^ v) := by
    obtain ⟨n, hn⟩ : ∃ n, 2 ^ v = n + 1 := ⟨2 ^ v - 1, by omega⟩
    rw [hn]
    exact q_lower n (by omega)
  have hq2 := q_upper (2 ^ v) (by omega)
  have ht := small_tail v hv
  rw [prob_eq]
  rw [card_total]
  -- counts
  have hNI := countNoIso v (2 ^ v)
  have hCsub : (Finset.univ.filter (fun z : Fin v × Fin (2 ^ v) → Bit => connectivityBool z = true))
      ⊆ Finset.univ.filter (fun z : Fin v × Fin (2 ^ v) → Bit => ∀ j, ∃ i, z (i, j) ≠ 0) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact conn_noiso hv0 z ((connBool_iff z).mp hz)
  have hup := Finset.card_le_card hCsub
  rw [hNI] at hup
  obtain ⟨s, hs4, hs⟩ : ∃ s : ℕ, s * 4 = 3 * 2 ^ v ∧ ∀ i i' : Fin v, i ≠ i' →
      (Finset.univ.filter (fun d : Fin v → Bit => ¬ (d i = 1 ∧ d i' = 1))).card = s := by
    refine ⟨(Finset.univ.filter (fun d : Fin v → Bit =>
      ¬ (d ⟨0, by omega⟩ = 1 ∧ d ⟨1, by omega⟩ = 1))).card, ?_, ?_⟩
    · exact card_S v ⟨0, by omega⟩ ⟨1, by omega⟩ (by
        intro h; have := congrArg Fin.val h; simp at this)
    · intro i i' hne
      have h1 := card_S v i i' hne
      have h2 := card_S v ⟨0, by omega⟩ ⟨1, by omega⟩ (by
        intro h; have := congrArg Fin.val h; simp at this)
      omega
  have hPF := pairfail_card (v := v) (N := 2 ^ v) s hs
  have hlow : (2 ^ v - 1) ^ (2 ^ v) ≤
      (Finset.univ.filter (fun z : Fin v × Fin (2 ^ v) → Bit => connectivityBool z = true)).card
      + v * v * s ^ (2 ^ v) := by
    rw [← hNI]
    refine le_trans ?_ (Nat.add_le_add_left hPF _)
    have hsub : (Finset.univ.filter (fun z : Fin v × Fin (2 ^ v) → Bit => ∀ j, ∃ i, z (i, j) ≠ 0))
        ⊆ (Finset.univ.filter (fun z : Fin v × Fin (2 ^ v) → Bit => connectivityBool z = true))
          ∪ (Finset.univ.filter (fun z : Fin v × Fin (2 ^ v) → Bit =>
            ∃ i i', i ≠ i' ∧ ∀ j, ¬ (z (i, j) = 1 ∧ z (i', j) = 1))) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hz ⊢
      by_cases hp : ∀ i i', i ≠ i' → ∃ j, z (i, j) = 1 ∧ z (i', j) = 1
      · left
        exact (connBool_iff z).mpr (noiso_conn hv0 z hz hp)
      · right
        push Not at hp
        obtain ⟨i, i', hne, h⟩ := hp
        exact ⟨i, i', hne, fun j hj => h j hj.1 hj.2⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  -- reals
  have hNr : ((2 ^ v : ℕ) : ℝ) = (2 : ℝ) ^ v := by push_cast; rfl
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ v) ^ (2 ^ v) := by positivity
  have hq : (((2 ^ v - 1 : ℕ) : ℝ)) ^ (2 ^ v)
      = (1 - 1 / ((2 ^ v : ℕ) : ℝ)) ^ (2 ^ v) * ((2 : ℝ) ^ v) ^ (2 ^ v) := by
    rw [← mul_pow]
    congr 1
    rw [Nat.cast_sub Nat.one_le_two_pow, hNr]
    have : (2 : ℝ) ^ v ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  have hsR : (s : ℝ) = 3 / 4 * 2 ^ v := by
    have : (s : ℝ) * 4 = 3 * 2 ^ v := by exact_mod_cast hs4
    linarith
  have ht2 : (s : ℝ) ^ (2 ^ v) = (3 / 4 : ℝ) ^ (2 ^ v) * ((2 : ℝ) ^ v) ^ (2 ^ v) := by
    rw [hsR, mul_pow]
  set q : ℝ := (1 - 1 / ((2 ^ v : ℕ) : ℝ)) ^ (2 ^ v) with hqdef
  set T : ℝ := ((2 : ℝ) ^ v) ^ (2 ^ v) with hT
  set c : ℝ := ((Finset.univ.filter
    (fun z : Fin v × Fin (2 ^ v) → Bit => connectivityBool z = true)).card : ℝ) with hc
  have hupR : c ≤ q * T := by
    have h := (Nat.cast_le (α := ℝ)).mpr hup
    rw [Nat.cast_pow] at h
    rw [← hq]; exact h
  have hlowR : q * T ≤ c + v * v * ((3 / 4 : ℝ) ^ (2 ^ v) * T) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hlow
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow] at h
    rw [← ht2, ← hq]; exact h
  have hp1 : c / T ≤ q := by rw [div_le_iff₀ hpos]; exact hupR
  have hp2 : q - v * v * (3 / 4 : ℝ) ^ (2 ^ v) ≤ c / T := by
    rw [le_div_iff₀ hpos]; nlinarith
  have hpl : (3 : ℝ) / 10 ≤ c / T := by
    have : (v : ℝ) * v * (3 / 4 : ℝ) ^ (2 ^ v) ≤ 1 / 50 := ht
    linarith
  have hph : c / T ≤ 2 / 5 := by linarith
  have hTc : (((2 ^ v) ^ (2 ^ v) : ℕ) : ℝ) = T := by rw [hT]; push_cast; rfl
  rw [hTc]
  nlinarith [mul_nonneg (sub_nonneg.mpr hpl) (sub_nonneg.mpr hph)]

end BinarySketchTruncation.Dev.T3Prob
end

section
namespace BinarySketchTruncation.Dev.Thm3
open BinarySketchTruncation.Opposite BinarySketchTruncation.Opposite.Supplement
open Matrix

noncomputable def Bm {n k : ℕ} (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n) :
    Matrix (Fin k) (Fin k) Bit := fun i j => A i (e j)
lemma fjm_gen {n : ℕ} (f : Vec n → Bool) : ∀ {T : Type} [DecidableEq T] (s : Vec n → T) (h : Bool) (t : T),
      functionJointMass f s h t = (∑ z, if f z = h ∧ s z = t then (1 : ℝ) else 0) /
        Fintype.card (Vec n) := by
  classical
  intro T _ s h t
  unfold functionJointMass uniformProbability uniformMean
  congr
  funext x
  by_cases c : f x = h ∧ s x = t <;> simp [c]

noncomputable def err {n : ℕ} {T : Type} (f : Vec n → Bool) (s : Vec n → T) (g : T → Bool) : ℝ :=
  uniformProbability (fun z => g (s z) ≠ f z)

lemma err_eq {n : ℕ} {T : Type} [Fintype T] [DecidableEq T] (f : Vec n → Bool) (s : Vec n → T)
    (g : T → Bool) :
    err f s g = ∑ x, ∑ h, (if g x ≠ h then (1 : ℝ) else 0) * functionJointMass f s h x := by
  classical
  have hz : ∀ z, ∑ x, ∑ h, (if g x ≠ h then (1 : ℝ) else 0) *
      (if f z = h ∧ s z = x then (1 : ℝ) else 0) = if g (s z) ≠ f z then 1 else 0 := by
    intro z
    rw [Finset.sum_eq_single (s z)]
    · rw [Finset.sum_eq_single (f z)]
      · simp
      · intro h _ hne; simp [Ne.symm hne]
      · simp
    · intro x _ hx
      apply Finset.sum_eq_zero
      intro h _
      simp [Ne.symm hx]
    · simp
  have hnum : (∑ z, if g (s z) ≠ f z then (1 : ℝ) else 0) =
      ∑ x, ∑ h, (if g x ≠ h then (1 : ℝ) else 0) *
        (∑ z, if f z = h ∧ s z = x then (1 : ℝ) else 0) := by
    simp_rw [Finset.mul_sum]
    calc (∑ z, if g (s z) ≠ f z then (1 : ℝ) else 0)
        = ∑ z, ∑ x, ∑ h, (if g x ≠ h then (1 : ℝ) else 0) *
            (if f z = h ∧ s z = x then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl fun z _ => (hz z).symm
      _ = ∑ x, ∑ z, ∑ h, (if g x ≠ h then (1 : ℝ) else 0) *
            (if f z = h ∧ s z = x then (1 : ℝ) else 0) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun x _ => by
          rw [Finset.sum_comm]
  unfold err uniformProbability uniformMean
  refine (?_ : _ = (∑ z, if g (s z) ≠ f z then (1 : ℝ) else 0) /
      Fintype.card (Vec n)).trans ?_
  · congr 1
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases c : g (s z) ≠ f z <;> simp [c]
  rw [hnum, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [fjm_gen, mul_div_assoc]

lemma minErr_le {n : ℕ} {T : Type} [Fintype T] (f : Vec n → Bool) (s : Vec n → T) (g : T → Bool) :
    minimumError f s ≤ err f s g := by
  classical
  unfold minimumError
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ g))

lemma minErr_attained {n : ℕ} {T : Type} [Fintype T] (f : Vec n → Bool) (s : Vec n → T) :
    ∃ g : T → Bool, minimumError f s = err f s g := by
  classical
  obtain ⟨g, -, hg⟩ := Finset.exists_min_image Finset.univ (fun g : T → Bool => err f s g)
    Finset.univ_nonempty
  refine ⟨g, le_antisymm (minErr_le f s g) ?_⟩
  unfold minimumError
  apply Finset.le_min'
  intro y hy
  obtain ⟨g', -, rfl⟩ := Finset.mem_image.1 hy
  exact hg g' (Finset.mem_univ _)

lemma dpi {n : ℕ} {S T : Type} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (f : Vec n → Bool) (s : Vec n → S) (t : Vec n → T) (hd : FunctionDominates f s t) :
    minimumError f s ≤ minimumError f t := by
  classical
  obtain ⟨K, ⟨hK0, hK1⟩, hKJ⟩ := hd
  obtain ⟨g, hg⟩ := minErr_attained f t
  set w : S → Bool → ℝ := fun x b =>
    ∑ h, (if b ≠ h then (1 : ℝ) else 0) * functionJointMass f s h x with hw
  have step1 : err f t g = ∑ x, ∑ y, K x y * w x (g y) := by
    rw [err_eq]
    simp_rw [hKJ]
    simp only [hw, Finset.mul_sum]
    refine (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun h _ => ?_
    ring
  let g' : S → Bool := fun x => if w x true ≤ w x false then true else false
  have hmin : ∀ x b, w x (g' x) ≤ w x b := by
    intro x b
    simp only [g']
    split_ifs with hc
    · cases b
      · exact hc
      · exact le_rfl
    · cases b
      · exact le_rfl
      · exact (not_le.1 hc).le
  have step2 : err f s g' = ∑ x, w x (g' x) := err_eq f s g'
  have step3 : ∑ x, w x (g' x) ≤ ∑ x, ∑ y, K x y * w x (g y) := by
    refine Finset.sum_le_sum fun x _ => ?_
    calc w x (g' x) = ∑ y, K x y * w x (g' x) := by rw [← Finset.sum_mul, hK1 x, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hmin x _) (hK0 x y)
  calc minimumError f s ≤ err f s g' := minErr_le f s g'
    _ ≤ err f t g := by rw [step2, step1]; exact step3
    _ = minimumError f t := hg.symm


lemma exists_info {n k : ℕ} (A : Matrix (Fin k) (Fin n) Bit) (hA : FullRowRank A) :
    ∃ e : Fin k ↪ Fin n, IsUnit (Bm A e).det := by
  classical
  have hrank : A.rank = k := by
    rw [Matrix.rank_eq_finrank_span_row]
    have := finrank_span_eq_card hA
    simp only [Fintype.card_fin] at this
    exact this
  obtain ⟨κ, f, hf, hspan, hli⟩ := exists_linearIndependent' Bit A.col
  have : Fintype κ := Fintype.ofInjective f hf
  have hcard : Fintype.card κ = k := by
    rw [← hrank, Matrix.rank_eq_finrank_span_cols, ← hspan, finrank_span_eq_card hli]
  let σ : Fin k ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let e : Fin k ↪ Fin n := ⟨fun i => f (σ i), fun x y hxy => σ.injective (hf hxy)⟩
  refine ⟨e, ?_⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
  exact hli.comp σ σ.injective


/-! ### Rank reduction -/

lemma reduce {n k : ℕ} (A : Matrix (Fin k) (Fin n) Bit) :
    ∃ (r : ℕ) (B : Matrix (Fin r) (Fin n) Bit) (C : Matrix (Fin k) (Fin r) Bit),
      r ≤ k ∧ FullRowRank B ∧ ∀ z, A *ᵥ z = C *ᵥ (B *ᵥ z) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' Bit A
  have : Fintype κ := Fintype.ofInjective a ha
  let σ : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  have hmem : ∀ i, ∃ c : κ → Bit, ∑ x, c x • A (a x) = A i := fun i => by
    have h1 : A i ∈ Submodule.span Bit (Set.range A) := Submodule.subset_span (Set.mem_range_self i)
    rw [← hspan] at h1
    exact (Submodule.mem_span_range_iff_exists_fun Bit).1 h1
  choose c hc using hmem
  refine ⟨Fintype.card κ, fun i => A (a (σ i)), fun i j => c i (σ j), ?_, ?_, ?_⟩
  · simpa using Fintype.card_le_of_injective a ha
  · exact hli.comp σ σ.injective
  · intro z
    funext i
    have h1 : (A *ᵥ z) i = A i ⬝ᵥ z := rfl
    rw [h1, ← hc i]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine (Equiv.sum_comp σ (fun x => ∑ j, c i x * A (a x) j * z j)).symm.trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_assoc]


lemma dom_bound {n k : ℕ} (f : Vec n → Bool) (hf : IsUnate f)
    (A : Matrix (Fin k) (Fin n) Bit) (g0 : Vec k → Bool) :
    ∃ (r : ℕ) (e : Fin r ↪ Fin n), r ≤ k ∧
      minimumError f (fun z => z ∘ e) ≤ err f (fun z => A *ᵥ z) g0 := by
  classical
  obtain ⟨r, B, C, hr, hB, hA⟩ := reduce A
  obtain ⟨e, he⟩ := exists_info B hB
  refine ⟨r, e, hr, ?_⟩
  have hd : FunctionDominates f (fun z => z ∘ e) (fun z => B.mulVec z) :=
    (theorem_2 f hf).1 r B e he
  have h1 := dpi f _ _ hd
  have h2 := minErr_le f (fun z => B.mulVec z) (fun u => g0 (C *ᵥ u))
  have h3 : err f (fun z => B.mulVec z) (fun u => g0 (C *ᵥ u)) = err f (fun z => A *ᵥ z) g0 := by
    unfold err
    simp only [hA]
  exact h1.trans (h3 ▸ h2)

/-! ### Fiber computations -/

section fiber
variable {Ω U : Type} [Fintype Ω] [Fintype U] [DecidableEq U] [DecidableEq Ω]

noncomputable def Qf (κ : Ω → U) (Fh : Ω → ℝ) (z : Ω) : ℝ :=
  (∑ w ∈ Finset.univ.filter (fun w => κ w = κ z), Fh w) /
    ((Finset.univ.filter (fun w => κ w = κ z)).card : ℝ)

lemma Qf_on (κ : Ω → U) (Fh : Ω → ℝ) (u : U) (z : Ω) (hz : κ z = u) :
    Qf κ Fh z = (∑ w ∈ Finset.univ.filter (fun w => κ w = u), Fh w) /
      ((Finset.univ.filter (fun w => κ w = u)).card : ℝ) := by
  simp only [Qf, hz]

lemma sumQ (κ : Ω → U) (Fh : Ω → ℝ) : ∑ z, Qf κ Fh z = ∑ z, Fh z := by
  rw [← Finset.sum_fiberwise Finset.univ κ (fun z => Qf κ Fh z),
    ← Finset.sum_fiberwise Finset.univ κ Fh]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_congr rfl (fun z hz => Qf_on κ Fh u z (Finset.mem_filter.1 hz).2),
    Finset.sum_const, nsmul_eq_mul]
  by_cases h : (Finset.univ.filter (fun w => κ w = u)).card = 0
  · rw [Finset.card_eq_zero] at h
    rw [h]; simp
  · have h' : ((Finset.univ.filter (fun w => κ w = u)).card : ℝ) ≠ 0 := by exact_mod_cast h
    field_simp

lemma sumQ2 (κ : Ω → U) (Fh : Ω → ℝ) (u : U) :
    ∑ z ∈ Finset.univ.filter (fun w => κ w = u), (Qf κ Fh z) ^ 2 =
      (∑ w ∈ Finset.univ.filter (fun w => κ w = u), Fh w) ^ 2 /
        ((Finset.univ.filter (fun w => κ w = u)).card : ℝ) := by
  rw [Finset.sum_congr rfl (fun z hz => by rw [Qf_on κ Fh u z (Finset.mem_filter.1 hz).2]),
    Finset.sum_const, nsmul_eq_mul]
  by_cases h : (Finset.univ.filter (fun w => κ w = u)).card = 0
  · rw [h]; simp
  · have h' : ((Finset.univ.filter (fun w => κ w = u)).card : ℝ) ≠ 0 := by exact_mod_cast h
    field_simp

lemma err_ge (κ : Ω → U) (F : Ω → Bool) (d : U → Bool) :
    ∑ z, (if F z then (1 : ℝ) else 0) -
      ∑ z, (Qf κ (fun z => if F z then (1 : ℝ) else 0) z) ^ 2 ≤
    ∑ z, (if d (κ z) ≠ F z then (1 : ℝ) else 0) := by
  set Fh : Ω → ℝ := fun z => if F z then (1 : ℝ) else 0 with hFh
  rw [← Finset.sum_fiberwise Finset.univ κ (fun z => if F z then (1 : ℝ) else 0),
    ← Finset.sum_fiberwise Finset.univ κ (fun z => (Qf κ Fh z) ^ 2),
    ← Finset.sum_fiberwise Finset.univ κ (fun z => if d (κ z) ≠ F z then (1 : ℝ) else 0),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [sumQ2]
  set fib := Finset.univ.filter (fun w => κ w = u) with hfib
  set S := ∑ w ∈ fib, Fh w with hS
  set N : ℝ := (fib.card : ℝ) with hN
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun w _ => by simp only [hFh]; split_ifs <;> norm_num
  have hSN : S ≤ N := by
    have : S ≤ ∑ w ∈ fib, (1 : ℝ) := Finset.sum_le_sum fun w _ => by
      simp only [hFh]; split_ifs <;> norm_num
    simpa [hN] using this
  have hN0 : 0 ≤ N := by positivity
  have hind : ∑ z ∈ fib, (if d (κ z) ≠ F z then (1 : ℝ) else 0) =
      if d u = true then N - S else S := by
    have : ∀ z ∈ fib, (if d (κ z) ≠ F z then (1 : ℝ) else 0) =
        if d u = true then 1 - Fh z else Fh z := by
      intro z hz
      have hz' : κ z = u := (Finset.mem_filter.1 hz).2
      rw [hz']
      simp only [hFh]
      cases d u <;> cases F z <;> simp
    rw [Finset.sum_congr rfl this]
    by_cases hd : d u = true
    · simp [hd, Finset.sum_sub_distrib, hS, hN]
    · simp [hd, hS]
  rw [hind]
  by_cases hN' : N = 0
  · have : S = 0 := le_antisymm (hN' ▸ hSN) hS0
    simp [hN', this]
  · have hNp : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hN')
    have hq : 0 ≤ S ^ 2 / N := by positivity
    split_ifs
    · have : (N - S) ^ 2 / N = N - 2 * S + S ^ 2 / N := by field_simp; ring
      have : 0 ≤ (N - S) ^ 2 / N := by positivity
      linarith
    · linarith
end fiber


lemma var_eq {Ω : Type} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    uniformVariance f = (∑ z, f z ^ 2) / (Fintype.card Ω : ℝ) - uniformMean f ^ 2 := by
  have hM : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold uniformVariance
  set m := uniformMean f with hm
  have hsum : ∑ z, f z = (Fintype.card Ω : ℝ) * m := by
    rw [hm]; unfold uniformMean; field_simp
  unfold uniformMean
  have : ∑ z, (f z - m) ^ 2 = ∑ z, f z ^ 2 - (Fintype.card Ω : ℝ) * m ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, hsum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    ring
  rw [this]
  field_simp

lemma up_equiv {Ω Ω' : Type} [Fintype Ω] [Fintype Ω'] [Nonempty Ω] [Nonempty Ω']
    (τ : Ω ≃ Ω') (E : Ω' → Prop) :
    uniformProbability (fun x => E (τ x)) = uniformProbability E := by
  classical
  unfold uniformProbability uniformMean
  rw [Fintype.card_congr τ]
  congr 1
  exact Equiv.sum_comp τ (fun y => if E y then (1 : ℝ) else 0)

theorem core {a b r : ℕ} (hab : 0 < a * b) (e' : Fin r ↪ Fin a × Fin b)
    (d : (Fin r → Bit) → Bool) :
    (1 - (r : ℝ) / ((a * b : ℕ) : ℝ)) * uniformVariance (connectivityIndicator (a := a) (b := b))
      ≤ uniformProbability (fun z : Fin a × Fin b → Bit => d (z ∘ e') ≠ connectivityBool z) := by
  classical
  set κ : (Fin a × Fin b → Bit) → (Fin r → Bit) := fun z => z ∘ e' with hκ
  set Fh : (Fin a × Fin b → Bit) → ℝ := connectivityIndicator with hFh
  set I : Finset (Fin a × Fin b) := Finset.univ.image e' with hI
  have hQ : coordinateConditionalMean Fh I = Qf κ Fh := by
    funext z
    unfold coordinateConditionalMean Qf coordinateFiber
    have key : ∀ p q : Finset (Fin a × Fin b → Bit), p = q →
        (∑ w ∈ p, Fh w) / (p.card : ℝ) = (∑ w ∈ q, Fh w) / (q.card : ℝ) := fun p q h => by rw [h]
    refine key _ _ ?_
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hI, Finset.mem_image,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff, hκ]
    constructor
    · intro h; funext i; exact h i
    · intro h i; exact congrFun h i
  have hcard : I.card = r := by
    rw [hI, Finset.card_image_of_injective _ e'.injective]; simp
  have h3 := lemma_3 a b I
  rw [hcard, hQ] at h3
  set M : ℝ := (Fintype.card (Fin a × Fin b → Bit) : ℝ) with hMdef
  have hM : 0 < M := by
    rw [hMdef]; exact_mod_cast Fintype.card_pos
  have hFF : ∀ z, Fh z = if connectivityBool z then (1 : ℝ) else 0 := fun z => rfl
  set μ := uniformMean Fh with hμ
  have hQmean : uniformMean (Qf κ Fh) = μ := by
    unfold uniformMean; rw [sumQ]; rfl
  have hVQ := var_eq (Qf κ Fh)
  rw [hQmean] at hVQ
  have hVF : uniformVariance Fh = μ - μ ^ 2 := by
    rw [var_eq]
    have : ∑ z, Fh z ^ 2 = ∑ z, Fh z := Finset.sum_congr rfl fun z _ => by
      rw [hFF]; split_ifs <;> norm_num
    rw [this]
    rfl
  have herr := err_ge κ connectivityBool d
  have hup : uniformProbability (fun z : Fin a × Fin b → Bit => d (z ∘ e') ≠ connectivityBool z)
      = (∑ z, (if d (κ z) ≠ connectivityBool z then (1 : ℝ) else 0)) / M := by
    unfold uniformProbability uniformMean
    congr 1
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases h : d (κ z) ≠ connectivityBool z <;> simp [h, hκ]
  rw [hup, le_div_iff₀ hM]
  have hX : (∑ z, Qf κ Fh z ^ 2) = (uniformVariance (Qf κ Fh) + μ ^ 2) * M := by
    rw [hVQ, ← hMdef]; field_simp; ring
  have hsumF : ∑ z, Fh z = μ * M := by
    rw [hμ]; unfold uniformMean; rw [← hMdef]; field_simp
  have herr' : ∑ z, Fh z - ∑ z, Qf κ Fh z ^ 2 ≤ ∑ z, (if d (κ z) ≠ connectivityBool z then (1 : ℝ) else 0) := by
    exact herr
  have hm : (0 : ℝ) < ((a * b : ℕ) : ℝ) := by exact_mod_cast hab
  have hVQle : uniformVariance (Qf κ Fh) ≤ (r : ℝ) / ((a * b : ℕ) : ℝ) * uniformVariance Fh := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]; linarith [h3]
  calc (1 - (r : ℝ) / ((a * b : ℕ) : ℝ)) * uniformVariance connectivityIndicator * M
      ≤ (uniformVariance Fh - uniformVariance (Qf κ Fh)) * M := by
        apply mul_le_mul_of_nonneg_right _ hM.le
        have : (1 - (r : ℝ) / ((a * b : ℕ) : ℝ)) * uniformVariance Fh
            = uniformVariance Fh - (r : ℝ) / ((a * b : ℕ) : ℝ) * uniformVariance Fh := by ring
        show (1 - (r : ℝ) / ((a * b : ℕ) : ℝ)) * uniformVariance Fh ≤ _
        linarith
    _ = μ * M - (uniformVariance (Qf κ Fh) + μ ^ 2) * M := by rw [hVF]; ring
    _ ≤ _ := by rw [← hsumF, ← hX]; exact herr'

/-! ### Transport to `Vec n` -/

noncomputable def fF (a b : ℕ) : Vec (a * b) → Bool :=
  fun w => connectivityBool (fun c : Fin a × Fin b => w (finProdFinEquiv c))

def tau (a b : ℕ) : (Fin a × Fin b → Bit) ≃ Vec (a * b) :=
  Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bit)

lemma tau_apply {a b : ℕ} (z : Fin a × Fin b → Bit) (i : Fin (a * b)) :
    tau a b z i = z (finProdFinEquiv.symm i) := rfl

lemma fF_tau {a b : ℕ} (z : Fin a × Fin b → Bit) : fF a b (tau a b z) = connectivityBool z := by
  unfold fF
  congr 1
  funext c
  simp [tau_apply]

lemma unate_fF (a b : ℕ) : IsUnate (fF a b) := by
  refine ⟨0, fun z i => ?_⟩
  simp only [add_zero]
  rw [Bool.le_iff_imp]
  unfold fF
  rw [T3Prob.connBool_iff, T3Prob.connBool_iff]
  intro h
  refine h.mono ?_
  intro x y hxy
  have key : ∀ c : Fin a × Fin b,
      (Function.update z i 0) (finProdFinEquiv c) = 1 → (Function.update z i 1) (finProdFinEquiv c) = 1 := by
    intro c hc
    by_cases hci : finProdFinEquiv c = i
    · rw [hci] at hc; simp at hc
    · rw [Function.update_of_ne hci] at hc ⊢; exact hc
  cases x <;> cases y <;> simp_all [edgeGraph]

lemma lower_bound {a b r : ℕ} (hab : 0 < a * b) (e : Fin r ↪ Fin (a * b)) :
    (1 - (r : ℝ) / ((a * b : ℕ) : ℝ)) * uniformVariance (connectivityIndicator (a := a) (b := b))
      ≤ minimumError (fF a b) (fun w => w ∘ e) := by
  classical
  obtain ⟨d, hd⟩ := minErr_attained (fF a b) (fun w => w ∘ e)
  rw [hd]
  unfold err
  rw [← up_equiv (tau a b)]
  have := core hab (e.trans finProdFinEquiv.symm.toEmbedding) d
  refine this.trans (le_of_eq ?_)
  congr 1
  funext z
  show (d (z ∘ _) ≠ connectivityBool z) = (d ((tau a b z) ∘ e) ≠ fF a b (tau a b z))
  rw [fF_tau]
  congr 3


lemma clause2 (v : ℕ) (hv : 0 < v)
    (hp : (1 / 5 : ℝ) ≤ uniformProbability (fun z : Fin v × Fin (2 ^ v) → Bit => connectivityBool z = true)
      * (1 - uniformProbability (fun z : Fin v × Fin (2 ^ v) → Bit => connectivityBool z = true)))
    (k : ℕ) (A : Matrix (Fin k) (Fin v × Fin (2 ^ v)) Bit)
    (g : Vec k → SimpleGraph (Fin v ⊕ Fin (2 ^ v)) → Bool)
    (h : ∀ H : SimpleGraph (Fin v ⊕ Fin (2 ^ v)),
      connectivityError (fun z => A.mulVec z) g H ≤ (1 / 10 : ℝ)) :
    v * 2 ^ v ≤ 2 * k := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hn : 0 < v * 2 ^ v := Nat.mul_pos hv (by positivity)
  have h0 := h ⊥
  set A' : Matrix (Fin k) (Fin (v * 2 ^ v)) Bit := A.submatrix id finProdFinEquiv.symm with hA'
  have hAA : ∀ z : Fin v × Fin (2 ^ v) → Bit, A' *ᵥ tau v (2 ^ v) z = A *ᵥ z := by
    intro z
    funext i
    simp only [hA', Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, tau_apply]
    exact Equiv.sum_comp finProdFinEquiv.symm (fun c => A i c * z c)
  have hconn : connectivityError (fun z => A.mulVec z) g ⊥ =
      err (fF v (2 ^ v)) (fun w => A' *ᵥ w) (fun m => g m ⊥) := by
    unfold err
    rw [← up_equiv (tau v (2 ^ v))]
    unfold connectivityError
    congr 1
    funext z
    simp only []
    rw [fF_tau, hAA]
    simp only [sup_bot_eq, connectivityBool]
  rw [hconn] at h0
  obtain ⟨r, e, hr, hle⟩ := dom_bound (fF v (2 ^ v)) (unate_fF v (2 ^ v)) A' (fun m => g m ⊥)
  have hlb := lower_bound hn e
  rw [T3Prob.variance_eq] at hlb
  set p := uniformProbability (fun z : Fin v × Fin (2 ^ v) → Bit => connectivityBool z = true)
  have hnR : (0 : ℝ) < ((v * 2 ^ v : ℕ) : ℝ) := by exact_mod_cast hn
  have h2r : 2 * (r : ℝ) < ((v * 2 ^ v : ℕ) : ℝ) := by
    have : 2 * r < v * 2 ^ v := by omega
    exact_mod_cast this
  have hfrac : (r : ℝ) / ((v * 2 ^ v : ℕ) : ℝ) < 1 / 2 := by
    rw [div_lt_iff₀ hnR]; linarith
  have hVar : (1 / 5 : ℝ) ≤ p - p ^ 2 := by nlinarith
  have : (1 / 10 : ℝ) < (1 - (r : ℝ) / ((v * 2 ^ v : ℕ) : ℝ)) * (p - p ^ 2) := by
    nlinarith
  linarith

end BinarySketchTruncation.Dev.Thm3

namespace BinarySketchTruncation.Opposite.Supplement
open BinarySketchTruncation.Dev.Thm3

theorem chk_theorem_3 :
    ∃ v₀ : ℕ, ∀ v : ℕ, v₀ ≤ v →
      (∃ (φ : ((Fin v × Fin (2 ^ v)) → Bit) → Vec (3 * v + 3))
          (g : Vec (3 * v + 3) → SimpleGraph (Fin v ⊕ Fin (2 ^ v)) → Bool),
        ∀ H : SimpleGraph (Fin v ⊕ Fin (2 ^ v)),
          connectivityError φ g H ≤ (1 / 10 : ℝ)) ∧
      (∀ (k : ℕ) (A : Matrix (Fin k) (Fin v × Fin (2 ^ v)) Bit)
          (g : Vec k → SimpleGraph (Fin v ⊕ Fin (2 ^ v)) → Bool),
        (∀ H : SimpleGraph (Fin v ⊕ Fin (2 ^ v)),
          connectivityError (fun z => A.mulVec z) g H ≤ (1 / 10 : ℝ)) →
        v * 2 ^ v ≤ 2 * k) := by
  obtain ⟨v1, h1⟩ := BinarySketchTruncation.Dev.T3Upper.upper
  obtain ⟨v2, h2⟩ := BinarySketchTruncation.Dev.T3Prob.prob
  refine ⟨max (max v1 v2) 1, fun v hv => ⟨h1 v (by omega), ?_⟩⟩
  intro k A g h
  exact clause2 v (by omega) (h2 v (by omega)) k A g h

end BinarySketchTruncation.Opposite.Supplement
end

theorem solution : type_of% @BinarySketchTruncation.Opposite.Supplement.chk_theorem_3 := @BinarySketchTruncation.Opposite.Supplement.chk_theorem_3
