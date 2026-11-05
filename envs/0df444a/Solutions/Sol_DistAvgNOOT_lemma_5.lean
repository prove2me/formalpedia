-- Prove2me | solution 1 for DistAvgNOOT.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:46:49.888718+00:00
-- url     : https://prove2.me/submissions/d3e0a588-5cf9-4a43-a0b4-dd58416d7f0d

import Mathlib

namespace DistAvgNOOT.Aux

open Finset

/-- sample variance -/
noncomputable def V {n : ℕ} (y : Fin n → ℝ) : ℝ := ∑ i, (y i - (∑ j, y j) / n) ^ 2

/-- entries of `AᵀA` -/
def wgt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℝ := ∑ k, A k i * A k j

lemma sum_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hcol : ∀ j, ∑ i, A i j = 1)
    (y : Fin n → ℝ) : ∑ i, (A.mulVec y) i = ∑ j, y j := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_mul, hcol j, one_mul]

lemma V_expand {n : ℕ} (y : Fin n → ℝ) :
    V y = ∑ i, y i ^ 2 - 2 * ((∑ j, y j) / n) * (∑ j, y j) + n * ((∑ j, y j) / n) ^ 2 := by
  unfold V
  set m := (∑ j, y j) / n
  have : ∀ i, (y i - m) ^ 2 = y i ^ 2 - 2 * m * y i + m ^ 2 := fun i => by ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma V_decrease {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hrow : ∀ i, ∑ j, A i j = 1) (hcol : ∀ j, ∑ i, A i j = 1) (y : Fin n → ℝ) :
    V y - V (A.mulVec y) = (1 / 2) * ∑ i, ∑ j, wgt A i j * (y i - y j) ^ 2 := by
  rw [V_expand, V_expand, sum_mulVec A hcol y]
  have hw1 : ∀ i, ∑ j, wgt A i j = 1 := by
    intro i
    simp only [wgt]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hrow, mul_one, hcol]
  have hw2 : ∀ j, ∑ i, wgt A i j = 1 := by
    intro j
    simp only [wgt]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hrow, one_mul, hcol]
  have hsq : ∑ k, (A.mulVec y k) ^ 2 = ∑ i, ∑ j, wgt A i j * (y i * y j) := by
    simp only [Matrix.mulVec, dotProduct, sq, Finset.sum_mul, Finset.mul_sum, wgt]
    rw [Finset.sum_comm (f := fun k a => ∑ b, A k b * y b * (A k a * y a))]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm (f := fun k b => A k b * y b * (A k a * y a))]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [hsq]
  have e : ∀ i j, wgt A i j * (y i - y j) ^ 2 =
      wgt A i j * y i ^ 2 + wgt A i j * y j ^ 2 - 2 * (wgt A i j * (y i * y j)) := by
    intro i j; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, hw1, hw2, one_mul]
  rw [Finset.sum_comm (f := fun i j => wgt A i j * y j ^ 2)]
  simp only [← Finset.sum_mul, hw2, one_mul]
  ring

lemma wgt_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hnn : ∀ i j, 0 ≤ A i j) (i j : Fin n) :
    0 ≤ wgt A i j := Finset.sum_nonneg (fun k _ => mul_nonneg (hnn k i) (hnn k j))

lemma wgt_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    wgt A i j = wgt A j i := by
  simp only [wgt]; exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

lemma wgt_ge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hnn : ∀ i j, 0 ≤ A i j)
    (k i j : Fin n) : A k i * A k j ≤ wgt A i j :=
  Finset.single_le_sum (f := fun k => A k i * A k j)
    (fun k _ => mul_nonneg (hnn k i) (hnn k j)) (Finset.mem_univ k)

/-- Lemma 2 of the source: a crossing edge forces cut weight at least `η / 2`. -/
lemma cut_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (η : ℝ)
    (hnn : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j = 1)
    (hdiag : ∀ i, 0 < A i i) (hη : ∀ i j, 0 < A i j → η ≤ A i j)
    (S : Finset (Fin n)) (hcross : ∃ i ∈ S, ∃ j ∉ S, 0 < A i j ∨ 0 < A j i) :
    η / 2 ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, wgt A i j := by
  have hpos : ∀ i ∈ S, ∀ j ∈ Sᶜ, 0 ≤ wgt A i j := fun i _ j _ => wgt_nonneg A hnn i j
  have hsplit : ∀ p, ∑ i ∈ S, A p i + ∑ i ∈ Sᶜ, A p i = 1 := by
    intro p; rw [Finset.sum_add_sum_compl, hrow]
  -- single-row and single-column lower bounds
  have hrowS : ∀ p ∈ S, ∑ j ∈ Sᶜ, wgt A p j ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, wgt A i j := fun p hp =>
    Finset.single_le_sum (f := fun i => ∑ j ∈ Sᶜ, wgt A i j)
      (fun i hi => Finset.sum_nonneg (fun j hj => hpos i hi j hj)) hp
  have hcolS : ∀ q ∈ Sᶜ, ∑ i ∈ S, wgt A i q ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, wgt A i j := fun q hq =>
    Finset.sum_le_sum (fun i hi => Finset.single_le_sum (f := fun j => wgt A i j)
      (fun j hj => hpos i hi j hj) hq)
  have hηA : ∀ i, η ≤ A i i := fun i => hη i i (hdiag i)
  -- the crossing entry `A p q > 0` with `p`, `q` on opposite sides
  obtain ⟨p, q, hpq, hside⟩ : ∃ p q, 0 < A p q ∧ ((p ∈ S ∧ q ∈ Sᶜ) ∨ (p ∈ Sᶜ ∧ q ∈ S)) := by
    obtain ⟨i, hi, j, hj, h | h⟩ := hcross
    · exact ⟨i, j, h, Or.inl ⟨hi, Finset.mem_compl.2 hj⟩⟩
    · exact ⟨j, i, h, Or.inr ⟨Finset.mem_compl.2 hj, hi⟩⟩
  have hηpq : η ≤ A p q := hη p q hpq
  have hC := hsplit p
  -- bound `η * C` where `C` is a row-`p` mass
  have bnd1 : ∀ T : Finset (Fin n), ∀ r : Fin n, (∀ j ∈ T, A p r * A p j ≤ wgt A r j) →
      η ≤ A p r → η * ∑ j ∈ T, A p j ≤ ∑ j ∈ T, wgt A r j := by
    intro T r h hr
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hj => le_trans ?_ (h j hj))
    exact mul_le_mul_of_nonneg_right hr (hnn p j)
  have bnd2 : ∀ T : Finset (Fin n), ∀ r : Fin n, (∀ i ∈ T, A p i * A p r ≤ wgt A i r) →
      η ≤ A p r → η * ∑ i ∈ T, A p i ≤ ∑ i ∈ T, wgt A i r := by
    intro T r h hr
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => le_trans ?_ (h i hi))
    rw [mul_comm (A p i)]
    exact mul_le_mul_of_nonneg_right hr (hnn p i)
  have hη0 : 0 ≤ η ∨ η < 0 := le_or_gt 0 η
  rcases hη0 with hη0 | hη0
  swap
  · have : 0 ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, wgt A i j :=
      Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => hpos i hi j hj))
    linarith
  rcases hside with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · by_cases hc : 1 / 2 ≤ ∑ i ∈ Sᶜ, A p i
    · -- pairs (p, j), j ∉ S
      have := bnd1 Sᶜ p (fun j _ => wgt_ge A hnn p p j) (hηA p)
      have := hrowS p hp
      nlinarith
    · -- pairs (i, q), i ∈ S
      have := bnd2 S q (fun i _ => wgt_ge A hnn p i q) hηpq
      have := hcolS q hq
      nlinarith
  · by_cases hc : 1 / 2 ≤ ∑ i ∈ S, A p i
    · -- pairs (i, p), i ∈ S
      have := bnd2 S p (fun i _ => wgt_ge A hnn p i p) (hηA p)
      have := hcolS p hp
      nlinarith
    · -- pairs (q, j), j ∉ S
      have := bnd1 Sᶜ q (fun j _ => wgt_ge A hnn p q j) hηpq
      have := hrowS q hq
      nlinarith

lemma telescope (u : ℕ → ℝ) (a : ℕ) :
    ∀ m, ∑ d ∈ Finset.Ico a (a + m), (u (d + 1) - u d) = u (a + m) - u a := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega), ih]
    ring

lemma sum_cut {n : ℕ} (S : Finset (Fin n)) (h : Fin n → Fin n → ℝ) :
    ∑ i ∈ S, ∑ j ∈ Sᶜ, h i j = ∑ i, ∑ j, if i ∈ S ∧ j ∉ S then h i j else 0 := by
  classical
  have e : ∀ i, (∑ j, if i ∈ S ∧ j ∉ S then h i j else 0) =
      if i ∈ S then ∑ j ∈ Sᶜ, h i j else 0 := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hi, true_and, if_true]
      rw [← Finset.sum_filter]
      congr 1
      ext j; simp
    · simp [hi]
  simp only [e]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

end DistAvgNOOT.Aux

open DistAvgNOOT.Aux

theorem solution {n : ℕ} (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (η : ℝ)
    (hnn : ∀ t i j, 0 ≤ A t i j)
    (hrow : ∀ t i, ∑ j, A t i j = 1) (hcol : ∀ t j, ∑ i, A t i j = 1)
    (hdiag : ∀ t i, 0 < A t i i)
    (hη : ∀ t i j, 0 < A t i j → η ≤ A t i j)
    (t0 B : ℕ)
    (hconn : (⨆ t ∈ Finset.Ico t0 (t0 + B),
      SimpleGraph.fromRel (fun i j : Fin n => 0 < A t i j)).Connected)
    (x : ℕ → Fin n → ℝ) (hx : ∀ t, x (t + 1) = (A t).mulVec (x t)) :
    ∑ i, (x (t0 + B) i - (∑ j, x (t0 + B) j) / n) ^ 2 ≤
      (1 - η / (2 * (n : ℝ) ^ 2)) * ∑ i, (x t0 i - (∑ j, x t0 j) / n) ^ 2 := by
  classical
  change V (x (t0 + B)) ≤ (1 - η / (2 * (n : ℝ) ^ 2)) * V (x t0)
  have hV0 : ∀ y : Fin n → ℝ, 0 ≤ V y := fun y => Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hn : 0 < n := by
    obtain ⟨v⟩ := hconn.nonempty
    exact Fin.pos_iff_nonempty.2 ⟨v⟩
  have hdec : ∀ t, V (x t) - V (x (t + 1)) =
      (1 / 2) * ∑ i, ∑ j, wgt (A t) i j * (x t i - x t j) ^ 2 := fun t => by
    rw [hx t]; exact V_decrease (A t) (hrow t) (hcol t) (x t)
  have hmonoV : ∀ t, V (x (t + 1)) ≤ V (x t) := by
    intro t
    have := hdec t
    have : 0 ≤ ∑ i, ∑ j, wgt (A t) i j * (x t i - x t j) ^ 2 :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
        mul_nonneg (wgt_nonneg _ (hnn t) i j) (sq_nonneg _)))
    linarith
  -- sorting the initial values
  set y := x t0 with hy
  set σ := Tuple.sort y with hσ
  have hsort : Monotone (y ∘ σ) := Tuple.monotone_sort y
  set r : Fin n → ℕ := fun i => ((σ.symm i : Fin n) : ℕ) with hr
  have hrlt : ∀ i, r i < n := fun i => (σ.symm i).2
  set u : ℕ → ℝ := fun k => if h : k < n then y (σ ⟨k, h⟩) else 0 with hu
  have hu_y : ∀ i, u (r i) = y i := by
    intro i
    simp only [hu, hr, dif_pos (σ.symm i).2]
    simp
  have hu_mono : ∀ a b, a ≤ b → b < n → u a ≤ u b := by
    intro a b hab hb
    simp only [hu, dif_pos hb, dif_pos (lt_of_le_of_lt hab hb)]
    exact hsort (show (⟨a, lt_of_le_of_lt hab hb⟩ : Fin n) ≤ ⟨b, hb⟩ from hab)
  set Low : ℕ → Finset (Fin n) := fun d => Finset.univ.filter (fun i => r i ≤ d) with hLow
  have hmemLow : ∀ d i, i ∈ Low d ↔ r i ≤ d := by
    intro d i; simp [hLow]
  set cuts := Finset.range (n - 1) with hcuts
  set g : ℕ → ℝ := fun d => u (d + 1) - u d with hg
  have hg0 : ∀ d ∈ cuts, 0 ≤ g d := by
    intro d hd
    have := Finset.mem_range.1 hd
    simp only [hg]
    linarith [hu_mono d (d + 1) (by omega) (by omega)]
  -- crossing predicate
  set P : ℕ → ℕ → Prop := fun d s =>
    ∃ i ∈ Low d, ∃ j ∉ Low d, 0 < A (t0 + s) i j ∨ 0 < A (t0 + s) j i with hP
  have hcross : ∀ d ∈ cuts, ∃ s, s < B ∧ P d s := by
    intro d hd
    have hd' := Finset.mem_range.1 hd
    set a : Fin n := σ ⟨0, hn⟩
    set b : Fin n := σ ⟨d + 1, by omega⟩
    have ha : a ∈ Low d := by
      rw [hmemLow]; simp [hr, a]
    have hb : b ∉ Low d := by
      rw [hmemLow]; simp [hr, b]
    obtain ⟨p⟩ := hconn.preconnected a b
    obtain ⟨dt, _, h1, h2⟩ := p.exists_boundary_dart (↑(Low d) : Set (Fin n)) ha hb
    have hadj := dt.adj
    simp only [SimpleGraph.iSup_adj, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨t, ht, -, hA⟩ := hadj
    have ht' := Finset.mem_Ico.1 ht
    refine ⟨t - t0, by omega, dt.fst, h1, dt.snd, h2, ?_⟩
    rw [show t0 + (t - t0) = t by omega]
    exact hA
  set sd : ℕ → ℕ := fun d => if h : ∃ s, s < B ∧ P d s then Nat.find h else 0 with hsd
  have hsd_spec : ∀ d ∈ cuts, sd d < B ∧ P d (sd d) ∧ ∀ s < sd d, ¬ P d s := by
    intro d hd
    have h := hcross d hd
    simp only [hsd, dif_pos h]
    refine ⟨(Nat.find_spec h).1, (Nat.find_spec h).2, fun s hs hPs => ?_⟩
    exact Nat.find_min h hs ⟨lt_trans hs (Nat.find_spec h).1, hPs⟩
  -- invariant before the first crossing
  have hinv : ∀ d ∈ cuts, ∀ s, s ≤ sd d →
      (∀ i ∈ Low d, x (t0 + s) i ≤ u d) ∧ (∀ j ∉ Low d, u (d + 1) ≤ x (t0 + s) j) := by
    intro d hd s
    have hd' := Finset.mem_range.1 hd
    induction s with
    | zero =>
      intro _
      constructor
      · intro i hi
        rw [hmemLow] at hi
        show x t0 i ≤ u d
        rw [← hy, ← hu_y i]
        exact hu_mono _ _ hi (by omega)
      · intro j hj
        rw [hmemLow] at hj
        show u (d + 1) ≤ x t0 j
        rw [← hy, ← hu_y j]
        exact hu_mono _ _ (by omega) (hrlt j)
    | succ s ih =>
      intro hs
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hnP : ¬ P d s := (hsd_spec d hd).2.2 s (by omega)
      have hzero : ∀ i ∈ Low d, ∀ j ∉ Low d, A (t0 + s) i j = 0 ∧ A (t0 + s) j i = 0 := by
        intro i hi j hj
        by_contra hcon
        apply hnP
        refine ⟨i, hi, j, hj, ?_⟩
        rcases not_and_or.1 hcon with h | h
        · exact Or.inl (lt_of_le_of_ne (hnn _ i j) (Ne.symm h))
        · exact Or.inr (lt_of_le_of_ne (hnn _ j i) (Ne.symm h))
      have hxs : x (t0 + (s + 1)) = (A (t0 + s)).mulVec (x (t0 + s)) := hx (t0 + s)
      constructor
      · intro i hi
        rw [hxs]
        simp only [Matrix.mulVec, dotProduct]
        calc ∑ k, A (t0 + s) i k * x (t0 + s) k ≤ ∑ k, A (t0 + s) i k * u d := by
              refine Finset.sum_le_sum (fun k _ => ?_)
              by_cases hk : k ∈ Low d
              · exact mul_le_mul_of_nonneg_left (ih1 k hk) (hnn _ i k)
              · rw [(hzero i hi k hk).1]; simp
          _ = u d := by rw [← Finset.sum_mul, hrow, one_mul]
      · intro j hj
        rw [hxs]
        simp only [Matrix.mulVec, dotProduct]
        calc u (d + 1) = ∑ k, A (t0 + s) j k * u (d + 1) := by
              rw [← Finset.sum_mul, hrow, one_mul]
          _ ≤ ∑ k, A (t0 + s) j k * x (t0 + s) k := by
              refine Finset.sum_le_sum (fun k _ => ?_)
              by_cases hk : k ∈ Low d
              · rw [(hzero k hk j hj).2]; simp
              · exact mul_le_mul_of_nonneg_left (ih2 k hk) (hnn _ j k)
  -- pair inequality at time t0 + s
  set F : ℕ → Fin n → Fin n → Finset ℕ := fun s i j =>
    cuts.filter (fun d => sd d = s ∧ i ∈ Low d ∧ j ∉ Low d) with hF
  have hpair : ∀ s i j, ∑ d ∈ F s i j, g d ^ 2 ≤ (x (t0 + s) j - x (t0 + s) i) ^ 2 := by
    intro s i j
    by_cases hne : (F s i j).Nonempty
    · set d1 := (F s i j).min' hne
      set dk := (F s i j).max' hne
      have hd1 : d1 ∈ cuts ∧ (sd d1 = s ∧ i ∈ Low d1 ∧ j ∉ Low d1) :=
        Finset.mem_filter.1 (Finset.min'_mem _ hne)
      have hdk : dk ∈ cuts ∧ (sd dk = s ∧ i ∈ Low dk ∧ j ∉ Low dk) :=
        Finset.mem_filter.1 (Finset.max'_mem _ hne)
      have hxi : x (t0 + s) i ≤ u d1 := by
        have := (hinv d1 hd1.1 s (by rw [hd1.2.1])).1 i hd1.2.2.1
        exact this
      have hxj : u (dk + 1) ≤ x (t0 + s) j :=
        (hinv dk hdk.1 s (by rw [hdk.2.1])).2 j hdk.2.2.2
      have hle1 : d1 ≤ dk := Finset.min'_le _ _ (Finset.max'_mem _ hne)
      have hsub : F s i j ⊆ Finset.Ico d1 (d1 + (dk + 1 - d1)) := by
        intro d hd
        rw [Finset.mem_Ico]
        exact ⟨Finset.min'_le _ _ hd, by have := Finset.le_max' _ _ hd; omega⟩
      have hgF : ∀ d ∈ F s i j, 0 ≤ g d := fun d hd =>
        hg0 d (Finset.mem_filter.1 hd).1
      have hdkn : dk + 1 < n := by have := Finset.mem_range.1 hdk.1; omega
      have hgI : ∀ d ∈ Finset.Ico d1 (d1 + (dk + 1 - d1)), 0 ≤ g d := by
        intro d hd
        have := Finset.mem_Ico.1 hd
        exact hg0 d (Finset.mem_range.2 (by omega))
      have hsum_le : ∑ d ∈ F s i j, g d ≤ u (dk + 1) - u d1 := by
        calc ∑ d ∈ F s i j, g d ≤ ∑ d ∈ Finset.Ico d1 (d1 + (dk + 1 - d1)), g d :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d hd _ => hgI d hd)
          _ = u (dk + 1) - u d1 := by
              rw [telescope u d1]
              rw [show d1 + (dk + 1 - d1) = dk + 1 by omega]
      have h0 : 0 ≤ ∑ d ∈ F s i j, g d := Finset.sum_nonneg hgF
      calc ∑ d ∈ F s i j, g d ^ 2 ≤ (∑ d ∈ F s i j, g d) ^ 2 :=
            Finset.sum_sq_le_sq_sum_of_nonneg hgF
        _ ≤ (x (t0 + s) j - x (t0 + s) i) ^ 2 := by
            apply pow_le_pow_left₀ h0
            linarith
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]
      exact sq_nonneg _
  have hdisj : ∀ s i j, F s i j = ∅ ∨ F s j i = ∅ := by
    intro s i j
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    obtain ⟨d, hd⟩ := h1
    obtain ⟨d', hd'⟩ := h2
    obtain ⟨-, -, a1, a2⟩ := Finset.mem_filter.1 hd
    obtain ⟨-, -, b1, b2⟩ := Finset.mem_filter.1 hd'
    rw [hmemLow] at a1 a2 b1 b2
    omega
  -- per-time bound
  have hstep : ∀ s, s < B →
      (η / 2) * ∑ d ∈ cuts.filter (fun d => sd d = s), g d ^ 2 ≤
        V (x (t0 + s)) - V (x (t0 + s + 1)) := by
    intro s hs
    rw [hdec]
    set w := wgt (A (t0 + s)) with hw
    set z := x (t0 + s) with hz
    have hwnn : ∀ i j, 0 ≤ w i j := wgt_nonneg _ (hnn _)
    -- lower bound pairwise
    have h1 : ∑ i, ∑ j, w i j * (∑ d ∈ F s i j, g d ^ 2 + ∑ d ∈ F s j i, g d ^ 2) ≤
        ∑ i, ∑ j, w i j * (z i - z j) ^ 2 := by
      refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
      refine mul_le_mul_of_nonneg_left ?_ (hwnn i j)
      rcases hdisj s i j with h | h
      · rw [h, Finset.sum_empty, zero_add]
        have := hpair s j i
        rw [hz]; linarith
      · rw [h, Finset.sum_empty, add_zero]
        have := hpair s i j
        rw [hz]; nlinarith [sq_nonneg (x (t0 + s) j - x (t0 + s) i)]
    have h2 : ∑ i, ∑ j, w i j * (∑ d ∈ F s i j, g d ^ 2 + ∑ d ∈ F s j i, g d ^ 2) =
        2 * ∑ i, ∑ j, w i j * ∑ d ∈ F s i j, g d ^ 2 := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => w i j * ∑ d ∈ F s j i, g d ^ 2)]
      have : ∀ i j, w j i * ∑ d ∈ F s i j, g d ^ 2 = w i j * ∑ d ∈ F s i j, g d ^ 2 := by
        intro i j; rw [hw, wgt_symm]
      simp only [this]
      ring
    -- regroup by cuts
    have h3 : ∑ i, ∑ j, w i j * ∑ d ∈ F s i j, g d ^ 2 =
        ∑ d ∈ cuts.filter (fun d => sd d = s),
          g d ^ 2 * ∑ i, ∑ j, (if i ∈ Low d ∧ j ∉ Low d then w i j else 0) := by
      calc ∑ i, ∑ j, w i j * ∑ d ∈ F s i j, g d ^ 2
          = ∑ i, ∑ j, ∑ d ∈ cuts,
              (if sd d = s ∧ i ∈ Low d ∧ j ∉ Low d then w i j * g d ^ 2 else 0) := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            rw [show F s i j = cuts.filter (fun d => sd d = s ∧ i ∈ Low d ∧ j ∉ Low d) from rfl,
              Finset.sum_filter, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun d _ => ?_)
            split_ifs <;> simp
        _ = ∑ i, ∑ d ∈ cuts, ∑ j,
              (if sd d = s ∧ i ∈ Low d ∧ j ∉ Low d then w i j * g d ^ 2 else 0) :=
            Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
        _ = ∑ d ∈ cuts, ∑ i, ∑ j,
              (if sd d = s ∧ i ∈ Low d ∧ j ∉ Low d then w i j * g d ^ 2 else 0) :=
            Finset.sum_comm
        _ = _ := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl (fun d _ => ?_)
            by_cases hds : sd d = s
            · simp only [hds, true_and, if_true, Finset.mul_sum]
              refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
              split_ifs <;> ring
            · simp [hds]
    have h4 : (η / 2) * ∑ d ∈ cuts.filter (fun d => sd d = s), g d ^ 2 ≤
        ∑ d ∈ cuts.filter (fun d => sd d = s),
          g d ^ 2 * ∑ i, ∑ j, (if i ∈ Low d ∧ j ∉ Low d then w i j else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun d hd => ?_)
      obtain ⟨hdc, hds⟩ := Finset.mem_filter.1 hd
      have hc : η / 2 ≤ ∑ i, ∑ j, (if i ∈ Low d ∧ j ∉ Low d then w i j else 0) := by
        rw [← sum_cut (Low d) w]
        apply cut_bound (A (t0 + s)) η (hnn _) (hrow _) (hdiag _) (hη _) (Low d)
        have := (hsd_spec d hdc).2.1
        rw [hds] at this
        exact this
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    linarith
  -- summing over the window
  have htel : V (x t0) - V (x (t0 + B)) =
      ∑ s ∈ Finset.range B, (V (x (t0 + s)) - V (x (t0 + s + 1))) := by
    have := Finset.sum_range_sub' (fun s => V (x (t0 + s))) B
    simp only [Nat.add_zero] at this
    exact this.symm
  have hmaps : ∀ d ∈ cuts, sd d ∈ Finset.range B := fun d hd =>
    Finset.mem_range.2 (hsd_spec d hd).1
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun d => g d ^ 2)
  have hbig : (η / 2) * ∑ d ∈ cuts, g d ^ 2 ≤ V (x t0) - V (x (t0 + B)) := by
    rw [htel, ← hfib, Finset.mul_sum]
    exact Finset.sum_le_sum (fun s hs => hstep s (Finset.mem_range.1 hs))
  have hmon : V (x (t0 + B)) ≤ V (x t0) := by
    have : 0 ≤ ∑ s ∈ Finset.range B, (V (x (t0 + s)) - V (x (t0 + s + 1))) :=
      Finset.sum_nonneg (fun s _ => by linarith [hmonoV (t0 + s)])
    linarith
  -- the sorted-gap bound
  have hR : ∑ d ∈ cuts, g d = u (n - 1) - u 0 := by
    have := telescope u 0 (n - 1)
    rw [zero_add, ← Finset.range_eq_Ico] at this
    exact this
  have hyb : ∀ i, u 0 ≤ y i ∧ y i ≤ u (n - 1) := by
    intro i
    rw [← hu_y i]
    exact ⟨hu_mono _ _ (Nat.zero_le _) (hrlt i), hu_mono _ _ (by have := hrlt i; omega)
      (by omega)⟩
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hmean : u 0 ≤ (∑ j, y j) / n ∧ (∑ j, y j) / n ≤ u (n - 1) := by
    have h1 : (n : ℝ) * u 0 ≤ ∑ j, y j := by
      have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (hyb j).1)
      simpa using this
    have h2 : ∑ j, y j ≤ (n : ℝ) * u (n - 1) := by
      have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (hyb j).2)
      simpa using this
    constructor
    · rw [le_div_iff₀ hnr]; linarith
    · rw [div_le_iff₀ hnr]; linarith
  have hVy : V y ≤ (n : ℝ) ^ 2 * ∑ d ∈ cuts, g d ^ 2 := by
    set R := u (n - 1) - u 0
    have hterm : ∀ i, (y i - (∑ j, y j) / n) ^ 2 ≤ R ^ 2 := by
      intro i
      have := hyb i
      apply sq_le_sq'
      · simp only [R]; linarith [hmean.1, hmean.2]
      · simp only [R]; linarith [hmean.1, hmean.2]
    have h1 : V y ≤ n * R ^ 2 := by
      unfold V
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
      simpa using this
    have h2 : R ^ 2 ≤ (n - 1 : ℕ) * ∑ d ∈ cuts, g d ^ 2 := by
      rw [← hR]
      have := sq_sum_le_card_mul_sum_sq (s := cuts) (f := g)
      simpa [hcuts] using this
    have h3 : ((n - 1 : ℕ) : ℝ) ≤ n := by
      have : n - 1 ≤ n := Nat.sub_le n 1
      exact_mod_cast this
    have hS : 0 ≤ ∑ d ∈ cuts, g d ^ 2 := Finset.sum_nonneg (fun d _ => sq_nonneg _)
    have h4 : ((n - 1 : ℕ) : ℝ) * ∑ d ∈ cuts, g d ^ 2 ≤ n * ∑ d ∈ cuts, g d ^ 2 :=
      mul_le_mul_of_nonneg_right h3 hS
    have h5 := mul_le_mul_of_nonneg_left (h2.trans h4) hnr.le
    nlinarith
  -- conclusion
  rcases le_or_gt 0 η with hη0 | hη0
  · have hfin : η / (2 * (n : ℝ) ^ 2) * V (x t0) ≤ (η / 2) * ∑ d ∈ cuts, g d ^ 2 := by
      have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      have : V (x t0) / (n : ℝ) ^ 2 ≤ ∑ d ∈ cuts, g d ^ 2 := by
        rw [div_le_iff₀ hn2]; linarith [hVy]
      calc η / (2 * (n : ℝ) ^ 2) * V (x t0) = (η / 2) * (V (x t0) / (n : ℝ) ^ 2) := by
            field_simp
        _ ≤ (η / 2) * ∑ d ∈ cuts, g d ^ 2 :=
            mul_le_mul_of_nonneg_left this (by linarith)
    nlinarith
  · have hneg : η / (2 * (n : ℝ) ^ 2) < 0 := div_neg_of_neg_of_pos hη0 (by positivity)
    have : 0 ≤ -(η / (2 * (n : ℝ) ^ 2)) * V (x t0) :=
      mul_nonneg (by linarith) (hV0 _)
    nlinarith
