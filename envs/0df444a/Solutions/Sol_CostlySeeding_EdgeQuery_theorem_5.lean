-- Prove2me | solution 1 for CostlySeeding.EdgeQuery.theorem_5
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:42:39.372195+00:00
-- url     : https://prove2.me/submissions/5559d9a1-932c-4934-877c-0b2bef339d54

import Definitions.Def_CostlySeeding_EdgeQuery_Algorithm

open CostlySeeding.EdgeQuery

namespace Theorem5Disproof

/-! ### Part 1: Probability weights and expectation reduction -/

private lemma bitW_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ bitW p b := by
  cases b <;> simp [bitW] <;> linarith

private lemma sum_bitW (p : ℝ) : ∑ b : Bool, bitW p b = 1 := by
  simp [bitW]

private noncomputable def permW (n : ℕ) : ℝ :=
  1 / (Fintype.card (Equiv.Perm (Fin n)) : ℝ)

private noncomputable def pickW (n : ℕ) : ℝ :=
  ∏ _ : Fin (n + 1), permW n

private noncomputable def orderW (n : ℕ) : ℝ :=
  ∏ _ : Fin n, permW n

private noncomputable def coinW {n : ℕ} (p : ℝ) (c : Fin n → Fin n → Bool) : ℝ :=
  ∏ v : Fin n, ∏ w : Fin n, bitW p (c v w)

private def seedEquiv (n : ℕ) : ProbeSeed n ≃
    (Fin (n + 1) → Equiv.Perm (Fin n)) ×
      (Fin n → Equiv.Perm (Fin n)) ×
      (Fin n → Fin n → Bool) × (Fin n → Fin n → Bool) where
  toFun s := (s.pick, s.order, s.coin, s.redo)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv s := by cases s; rfl
  right_inv t := by rcases t with ⟨a, b, c, d⟩; rfl

private lemma seedW_eq {n : ℕ} (p : ℝ) (s : ProbeSeed n) :
    seedW p s = pickW n * orderW n * coinW p s.coin * coinW p s.redo := rfl

private lemma permW_pos (n : ℕ) : 0 < permW n := by
  unfold permW
  exact div_pos one_pos (Nat.cast_pos.mpr Fintype.card_pos)

private lemma pickW_pos (n : ℕ) : 0 < pickW n :=
  Finset.prod_pos fun _ _ => permW_pos n

private lemma orderW_pos (n : ℕ) : 0 < orderW n :=
  Finset.prod_pos fun _ _ => permW_pos n

private lemma coinW_nonneg {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (c : Fin n → Fin n → Bool) : 0 ≤ coinW p c :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => bitW_nonneg hp0 hp1 _

private lemma seedW_nonneg {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : ProbeSeed n) :
    0 ≤ seedW p s := by
  rw [seedW_eq]
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (pickW_pos n).le (orderW_pos n).le) (coinW_nonneg hp0 hp1 _))
    (coinW_nonneg hp0 hp1 _)

private lemma sum_permW_const (n : ℕ) :
    ∑ _ : Equiv.Perm (Fin n), permW n = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, permW]
  have hpos : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  field_simp [hpos]

private lemma sum_pickW (n : ℕ) :
    ∑ _ : Fin (n + 1) → Equiv.Perm (Fin n), pickW n = 1 := by
  unfold pickW
  rw [← Fintype.prod_sum (fun (_ : Fin (n + 1)) (_ : Equiv.Perm (Fin n)) => permW n)]
  simp_rw [sum_permW_const]
  simp

private lemma sum_orderW (n : ℕ) :
    ∑ _ : Fin n → Equiv.Perm (Fin n), orderW n = 1 := by
  unfold orderW
  rw [← Fintype.prod_sum (fun (_ : Fin n) (_ : Equiv.Perm (Fin n)) => permW n)]
  simp_rw [sum_permW_const]
  simp

private lemma sum_coinW_row {n : ℕ} (p : ℝ) :
    ∑ r : Fin n → Bool, ∏ w : Fin n, bitW p (r w) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Bool) => bitW p b)]
  simp_rw [sum_bitW]
  simp

private lemma sum_coinW {n : ℕ} (p : ℝ) :
    ∑ c : Fin n → Fin n → Bool, coinW p c = 1 := by
  unfold coinW
  rw [← Fintype.prod_sum (fun (_ : Fin n) (r : Fin n → Bool) => ∏ w : Fin n, bitW p (r w))]
  simp_rw [sum_coinW_row]
  simp

private lemma sum_seedW_fn {n : ℕ} (p : ℝ) (f : ProbeSeed n → ℝ) :
    ∑ s : ProbeSeed n, seedW p s * f s =
      ∑ pick : Fin (n + 1) → Equiv.Perm (Fin n), pickW n *
        ∑ coin : Fin n → Fin n → Bool, coinW p coin *
          ∑ redo : Fin n → Fin n → Bool, coinW p redo *
            ∑ ord : Fin n → Equiv.Perm (Fin n), orderW n *
              f ⟨pick, ord, coin, redo⟩ := by
  rw [← (seedEquiv n).symm.sum_comp]
  simp only [seedEquiv, Equiv.coe_fn_symm_mk, seedW_eq]
  simp only [Fintype.sum_prod_type]
  calc ∑ pick, ∑ ord, ∑ coin, ∑ redo,
        pickW n * orderW n * coinW p coin * coinW p redo * f ⟨pick, ord, coin, redo⟩
      = ∑ pick, ∑ coin, ∑ redo, ∑ ord,
          pickW n * (coinW p coin * (coinW p redo * (orderW n * f ⟨pick, ord, coin, redo⟩))) := by
        apply Finset.sum_congr rfl; intro pick _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro coin _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro redo _
        apply Finset.sum_congr rfl; intro ord _
        ring
    _ = _ := by
        simp only [← Finset.mul_sum]

private lemma sum_seedW {n : ℕ} (p : ℝ) : ∑ s : ProbeSeed n, seedW p s = 1 := by
  have h := sum_seedW_fn (n := n) p (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  rw [h]
  simp only [sum_orderW, sum_coinW, sum_pickW, mul_one]

private lemma sum_prod_seedW {n : ℕ} (T : ℕ) (p : ℝ) :
    ∑ ss : Fin T → ProbeSeed n, (∏ i : Fin T, seedW p (ss i)) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin T) (s : ProbeSeed n) => seedW p s)]
  simp [sum_seedW]

private lemma sum_prod_single_coord {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (w : α → ℝ) (hw : ∑ a : α, w a = 1) (i : ι) (f : α → ℝ) :
    ∑ x : ι → α, (∏ j : ι, w (x j)) * f (x i) = ∑ a : α, w a * f a := by
  let g : ι → α → ℝ := fun j a => if j = i then w a * f a else w a
  have hprod : ∀ x : ι → α, (∏ j : ι, w (x j)) * f (x i) = ∏ j : ι, g j (x j) := by
    intro x
    rw [← Finset.mul_prod_erase Finset.univ (fun j => w (x j)) (Finset.mem_univ i)]
    rw [← Finset.mul_prod_erase Finset.univ (fun j => g j (x j)) (Finset.mem_univ i)]
    have hrest : ∏ j ∈ Finset.univ.erase i, g j (x j) =
        ∏ j ∈ Finset.univ.erase i, w (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [g, Finset.ne_of_mem_erase hj]
    rw [hrest]
    simp only [g, ↓reduceIte]
    ring
  simp_rw [hprod]
  rw [← Fintype.prod_sum g]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => ∑ a, g j a) (Finset.mem_univ i)]
  have hones : ∏ j ∈ Finset.univ.erase i, ∑ a : α, g j a = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    have hne : j ≠ i := Finset.ne_of_mem_erase hj
    simp [g, hne, hw]
  rw [hones, mul_one]
  simp [g]

private lemma expect_queries_eq_T_mul {n T : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (Vrho : Finset (Fin n)) (tau : ℕ) :
    ∑ ss : Fin T → ProbeSeed n, (∏ i : Fin T, seedW p (ss i)) * (queries G Vrho tau ss : ℝ) =
      (T : ℝ) * ∑ s : ProbeSeed n, seedW p s * ((probeCopy G Vrho tau s).2 : ℝ) := by
  have hterm : ∀ i : Fin T,
      ∑ ss : Fin T → ProbeSeed n, (∏ j : Fin T, seedW p (ss j)) *
          ((probeCopy G Vrho tau (ss i)).2 : ℝ) =
        ∑ s : ProbeSeed n, seedW p s * ((probeCopy G Vrho tau s).2 : ℝ) :=
    fun i => sum_prod_single_coord (seedW p) (sum_seedW p) i
      (fun s => ((probeCopy G Vrho tau s).2 : ℝ))
  calc ∑ ss : Fin T → ProbeSeed n, (∏ i : Fin T, seedW p (ss i)) * (queries G Vrho tau ss : ℝ)
      = ∑ ss : Fin T → ProbeSeed n, ∑ i : Fin T,
          (∏ j : Fin T, seedW p (ss j)) * ((probeCopy G Vrho tau (ss i)).2 : ℝ) := by
        apply Finset.sum_congr rfl; intro ss _
        simp only [queries, Nat.cast_sum, Finset.mul_sum]
    _ = ∑ i : Fin T, ∑ ss : Fin T → ProbeSeed n,
          (∏ j : Fin T, seedW p (ss j)) * ((probeCopy G Vrho tau (ss i)).2 : ℝ) :=
        Finset.sum_comm
    _ = ∑ _ : Fin T, ∑ s : ProbeSeed n, seedW p s * ((probeCopy G Vrho tau s).2 : ℝ) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = (T : ℝ) * ∑ s : ProbeSeed n, seedW p s * ((probeCopy G Vrho tau s).2 : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### Part 2: Deterministic worst-case query bound (`≤ n^2` per copy) -/

private lemma probeNeighbors_queries_le {n : ℕ} (v : Fin n) (tau : ℕ) (X : Finset (Fin n)) :
    ∀ (ws : List (Fin n)) (st : ProbeState n),
      (probeNeighbors v tau X ws st).queries ≤ st.queries + ws.length
  | [], st => by simp [probeNeighbors]
  | w :: ws, st => by
    simp only [probeNeighbors, List.length_cons]
    split_ifs with h1 h2
    · have ih := probeNeighbors_queries_le v tau X ws { st with queries := st.queries + 1 }
      dsimp at ih; omega
    · have ih := probeNeighbors_queries_le v tau X ws
        { st with vertices := insert w st.vertices, edges := insert s(v, w) st.edges,
                  queries := st.queries + 1 }
      dsimp at ih; omega
    · omega

private lemma orderedNeighbors_length_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : ProbeSeed n) (X : Finset (Fin n)) (v : Fin n) :
    (orderedNeighbors G s X v).length ≤ n := by
  unfold orderedNeighbors
  rw [List.length_mergeSort, Finset.length_toList]
  exact (Finset.card_le_univ _).trans (by simp)

private lemma probeLoop_queries_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tau : ℕ) (s : ProbeSeed n) :
    ∀ (fuel : ℕ) (st : ProbeState n),
      (probeLoop G tau s fuel st).queries ≤ st.queries + fuel * n
  | 0, st => by simp [probeLoop]
  | fuel + 1, st => by
    simp only [probeLoop]
    split_ifs with h
    · set v := chooseRank (s.pick (Fin.ofNat (n + 1) (n - (fuel + 1)))) (st.vertices \ st.explored) h
      set X := insert v st.explored
      set st' := probeNeighbors v tau X (orderedNeighbors G s X v) { st with explored := X }
      have h1 := probeLoop_queries_le G tau s fuel st'
      have h2 : st'.queries ≤ st.queries + (orderedNeighbors G s X v).length :=
        probeNeighbors_queries_le v tau X (orderedNeighbors G s X v) { st with explored := X }
      have h3 := orderedNeighbors_length_le G s X v
      have hmul : (fuel + 1) * n = fuel * n + n := by ring
      omega
    · omega

private lemma probeCopy_queries_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Vrho : Finset (Fin n)) (tau : ℕ) (s : ProbeSeed n) :
    (probeCopy G Vrho tau s).2 ≤ n ^ 2 := by
  unfold probeCopy
  have h := probeLoop_queries_le G tau s n
    { vertices := Vrho, edges := ∅, explored := ∅, queries := 0 }
  simpa [sq] using h

private lemma queries_le_T_mul_sq {n T : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Vrho : Finset (Fin n)) (tau : ℕ) (ss : Fin T → ProbeSeed n) :
    queries G Vrho tau ss ≤ T * n ^ 2 := by
  unfold queries
  calc ∑ i : Fin T, (probeCopy G Vrho tau (ss i)).2
      ≤ ∑ _ : Fin T, n ^ 2 := Finset.sum_le_sum fun i _ => probeCopy_queries_le G Vrho tau (ss i)
    _ = T * n ^ 2 := by simp

private lemma powersetCard_univ_self (n : ℕ) :
    (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
  ext A
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => Finset.eq_univ_of_card A (by simpa using h), fun h => by simp [h]⟩

private lemma expect_single_le_of_prob_ge {n T tau : ℕ} (hn : 0 < n) (hT : 0 < T)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p delta Q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hQ : 0 ≤ Q)
    (hdelta : 2 * Real.log n ≤ delta)
    (hprob : 1 - 3 * Real.exp (-delta) ≤
      probeEventProb (T := T) p n (fun Vrho ss => (queries G Vrho tau ss : ℝ) ≤ Q)) :
    ∑ s : ProbeSeed n, seedW p s * ((probeCopy G Finset.univ tau s).2 : ℝ) ≤ Q / (T : ℝ) + 3 := by
  unfold probeEventProb at hprob
  rw [powersetCard_univ_self] at hprob
  simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, div_one, one_mul] at hprob
  have hpw : ∀ ss : Fin T → ProbeSeed n,
      (queries G Finset.univ tau ss : ℝ) ≤
        Q + (T : ℝ) * (n : ℝ) ^ 2 * (1 - if (queries G Finset.univ tau ss : ℝ) ≤ Q then (1 : ℝ) else 0) := by
    intro ss
    split_ifs with h
    · linarith
    · have hle : (queries G Finset.univ tau ss : ℝ) ≤ (T : ℝ) * (n : ℝ) ^ 2 := by
        exact_mod_cast queries_le_T_mul_sq G Finset.univ tau ss
      linarith
  have hw0 : ∀ ss : Fin T → ProbeSeed n, 0 ≤ ∏ i : Fin T, seedW p (ss i) :=
    fun ss => Finset.prod_nonneg fun i _ => seedW_nonneg hp0 hp1 (ss i)
  have hsum_le :
      ∑ ss : Fin T → ProbeSeed n, (∏ i : Fin T, seedW p (ss i)) * (queries G Finset.univ tau ss : ℝ) ≤
        ∑ ss : Fin T → ProbeSeed n, (∏ i : Fin T, seedW p (ss i)) *
          (Q + (T : ℝ) * (n : ℝ) ^ 2 *
            (1 - if (queries G Finset.univ tau ss : ℝ) ≤ Q then (1 : ℝ) else 0)) :=
    Finset.sum_le_sum fun ss _ => mul_le_mul_of_nonneg_left (hpw ss) (hw0 ss)
  have hsum_rhs :
      ∑ ss : Fin T → ProbeSeed n, (∏ i : Fin T, seedW p (ss i)) *
          (Q + (T : ℝ) * (n : ℝ) ^ 2 *
            (1 - if (queries G Finset.univ tau ss : ℝ) ≤ Q then (1 : ℝ) else 0)) =
        Q + (T : ℝ) * (n : ℝ) ^ 2 * (1 - ∑ ss : Fin T → ProbeSeed n,
          (∏ i : Fin T, seedW p (ss i)) *
            if (queries G Finset.univ tau ss : ℝ) ≤ Q then (1 : ℝ) else 0) := by
    have hexp : ∀ ss : Fin T → ProbeSeed n,
        (∏ i : Fin T, seedW p (ss i)) *
          (Q + (T : ℝ) * (n : ℝ) ^ 2 *
            (1 - if (queries G Finset.univ tau ss : ℝ) ≤ Q then (1 : ℝ) else 0)) =
        (∏ i : Fin T, seedW p (ss i)) * (Q + (T : ℝ) * (n : ℝ) ^ 2) -
          (T : ℝ) * (n : ℝ) ^ 2 * ((∏ i : Fin T, seedW p (ss i)) *
            if (queries G Finset.univ tau ss : ℝ) ≤ Q then (1 : ℝ) else 0) := by
      intro ss; ring
    simp_rw [hexp]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, sum_prod_seedW]
    ring
  rw [expect_queries_eq_T_mul, hsum_rhs] at hsum_le
  have hexp_le : (n : ℝ) ^ 2 * Real.exp (-delta) ≤ 1 := by
    have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have h1 : Real.exp (-delta) ≤ Real.exp (-(2 * Real.log (n : ℝ))) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-(2 * Real.log (n : ℝ))) = ((n : ℝ) ^ 2)⁻¹ := by
      rw [Real.exp_neg, show 2 * Real.log (n : ℝ) = Real.log (n : ℝ) + Real.log (n : ℝ) by ring,
          Real.exp_add, Real.exp_log hnR, sq]
    calc (n : ℝ) ^ 2 * Real.exp (-delta)
        ≤ (n : ℝ) ^ 2 * ((n : ℝ) ^ 2)⁻¹ := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt hnR))
  have hTpos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
  have hstep : (T : ℝ) * ∑ s : ProbeSeed n, seedW p s * ((probeCopy G Finset.univ tau s).2 : ℝ) ≤
      Q + (T : ℝ) * 3 := by
    have h1 : 1 - ∑ ss : Fin T → ProbeSeed n, (∏ i : Fin T, seedW p (ss i)) *
        (if (queries G Finset.univ tau ss : ℝ) ≤ Q then (1 : ℝ) else 0) ≤ 3 * Real.exp (-delta) := by
      linarith
    have h2 : (T : ℝ) * (n : ℝ) ^ 2 *
        (1 - ∑ ss : Fin T → ProbeSeed n, (∏ i : Fin T, seedW p (ss i)) *
          (if (queries G Finset.univ tau ss : ℝ) ≤ Q then (1 : ℝ) else 0)) ≤
        (T : ℝ) * (n : ℝ) ^ 2 * (3 * Real.exp (-delta)) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hTpos.le (sq_nonneg _))
    have h3 : (T : ℝ) * (n : ℝ) ^ 2 * (3 * Real.exp (-delta)) ≤ (T : ℝ) * 3 := by
      have : (T : ℝ) * (n : ℝ) ^ 2 * (3 * Real.exp (-delta)) =
          (T : ℝ) * 3 * ((n : ℝ) ^ 2 * Real.exp (-delta)) := by ring
      rw [this]
      nlinarith
    linarith
  have hdiv : ∑ s : ProbeSeed n, seedW p s * ((probeCopy G Finset.univ tau s).2 : ℝ) ≤
      (Q + (T : ℝ) * 3) / (T : ℝ) :=
    (le_div_iff₀' hTpos).mpr hstep
  have hrewrite : (Q + (T : ℝ) * 3) / (T : ℝ) = Q / (T : ℝ) + 3 := by
    rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt hTpos)]
  linarith

/-! ### Part 3: Complete bipartite graph `K_{a, b}` and pure pick trajectory -/

private def bipGraph (n a : ℕ) : SimpleGraph (Fin n) where
  Adj u v := (u.val < a ∧ a ≤ v.val) ∨ (a ≤ u.val ∧ v.val < a)
  symm := ⟨fun _ _ h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩⟩
  loopless := ⟨fun _ h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega⟩

private instance bipGraphDec (n a : ℕ) : DecidableRel (bipGraph n a).Adj := by
  intro u v; unfold bipGraph; infer_instance

private def setA (n a : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u : Fin n => u.val < a

private def setB (n a : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u : Fin n => a ≤ u.val

private lemma mem_setA {n a : ℕ} {u : Fin n} : u ∈ setA n a ↔ u.val < a := by
  simp [setA]

private lemma mem_setB {n a : ℕ} {u : Fin n} : u ∈ setB n a ↔ a ≤ u.val := by
  simp [setB]

private lemma card_setA {n a : ℕ} (ha : a ≤ n) : (setA n a).card = a := by
  have heq : setA n a = Finset.univ.image (Fin.castLE ha) := by
    ext u
    simp only [mem_setA, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hu; exact ⟨⟨u.val, hu⟩, by ext; rfl⟩
    · rintro ⟨x, rfl⟩; exact x.isLt
  rw [heq, Finset.card_image_of_injective _ (Fin.castLE_injective ha)]
  simp

private lemma card_setB {n a : ℕ} (ha : a ≤ n) : (setB n a).card = n - a := by
  have hdisj : Disjoint (setA n a) (setB n a) := by
    rw [Finset.disjoint_left]
    intro u huA huB
    rw [mem_setA] at huA; rw [mem_setB] at huB; omega
  have hunion : setA n a ∪ setB n a = Finset.univ := by
    ext u; simp only [Finset.mem_union, mem_setA, mem_setB, Finset.mem_univ, iff_true]; omega
  have hcard : (setA n a).card + (setB n a).card = n := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  rw [card_setA ha] at hcard
  omega

private lemma chooseRank_mem {n : ℕ} (e : Equiv.Perm (Fin n)) (U : Finset (Fin n))
    (hU : U.Nonempty) : chooseRank e U hU ∈ U := by
  unfold chooseRank
  obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp (Finset.min'_mem (U.image e) (hU.image e))
  rw [← heq]; simpa using hu

private lemma chooseRank_eq_iff {n : ℕ} (e : Equiv.Perm (Fin n)) (U : Finset (Fin n))
    (hU : U.Nonempty) (w : Fin n) (hw : w ∈ U) :
    chooseRank e U hU = w ↔ ∀ u ∈ U, e w ≤ e u := by
  unfold chooseRank
  constructor
  · intro h u hu
    have hmin := Finset.min'_le (U.image e) (e u) (Finset.mem_image_of_mem e hu)
    have hew : e w = (U.image e).min' (hU.image e) := by
      have := congrArg e h
      simpa using this.symm
    rw [hew]; exact hmin
  · intro h
    have hle : (U.image e).min' (hU.image e) ≤ e w :=
      Finset.min'_le (U.image e) (e w) (Finset.mem_image_of_mem e hw)
    have hge : e w ≤ (U.image e).min' (hU.image e) := by
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp (Finset.min'_mem (U.image e) (hU.image e))
      rw [← heq]; exact h u hu
    have heq : (U.image e).min' (hU.image e) = e w := le_antisymm hle hge
    rw [heq]; simp

private lemma chooseRank_equivariant {n : ℕ} (e σ : Equiv.Perm (Fin n))
    (U : Finset (Fin n)) (hU : U.Nonempty) :
    chooseRank (e * σ.symm) (U.image σ) (hU.image σ) = σ (chooseRank e U hU) := by
  unfold chooseRank
  have himg : (U.image σ).image (e * σ.symm) = U.image e := by
    ext y
    simp only [Finset.mem_image, Equiv.Perm.mul_apply]
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, by simp⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨σ z, ⟨z, hz, rfl⟩, by simp⟩
  have hmin : ((U.image σ).image (e * σ.symm)).min' ((hU.image σ).image _) =
      (U.image e).min' (hU.image e) := by
    congr 1
  rw [hmin]
  apply (e * σ.symm).injective
  simp [Equiv.Perm.mul_apply]

private noncomputable def pickPrefix {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n)) :
    ℕ → Finset (Fin n)
  | 0 => ∅
  | t + 1 =>
    let U := Finset.univ \ pickPrefix pick t
    if h : U.Nonempty then
      insert (chooseRank (pick (Fin.ofNat (n + 1) t)) U h) (pickPrefix pick t)
    else pickPrefix pick t

private lemma card_pickPrefix {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n)) :
    ∀ t ≤ n, (pickPrefix pick t).card = t
  | 0, _ => by simp [pickPrefix]
  | t + 1, ht => by
    have ih := card_pickPrefix pick t (by omega)
    have hUcard : (Finset.univ \ pickPrefix pick t).card = n - t := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, ih]
    have hU : (Finset.univ \ pickPrefix pick t).Nonempty :=
      Finset.card_pos.mp (by omega)
    simp only [pickPrefix, dif_pos hU]
    have hmem := chooseRank_mem (pick (Fin.ofNat (n + 1) t)) _ hU
    rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hmem).2, ih]

private lemma pickPrefix_univ {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n)) :
    pickPrefix pick n = Finset.univ :=
  Finset.eq_univ_of_card _ (by rw [card_pickPrefix pick n le_rfl, Fintype.card_fin])

private lemma pickPrefix_nonempty_sdiff {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n))
    {t : ℕ} (ht : t < n) : (Finset.univ \ pickPrefix pick t).Nonempty := by
  apply Finset.card_pos.mp
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      card_pickPrefix pick t ht.le]
  omega

private noncomputable def pickStepVertex {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n))
    (t : Fin n) : Fin n :=
  chooseRank (pick (Fin.ofNat (n + 1) t.val)) (Finset.univ \ pickPrefix pick t.val)
    (pickPrefix_nonempty_sdiff pick t.isLt)

private lemma pickPrefix_succ {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n)) (t : Fin n) :
    pickPrefix pick (t.val + 1) = insert (pickStepVertex pick t) (pickPrefix pick t.val) := by
  simp only [pickPrefix, dif_pos (pickPrefix_nonempty_sdiff pick t.isLt), pickStepVertex]

private lemma pickStepVertex_not_mem {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n)) (t : Fin n) :
    pickStepVertex pick t ∉ pickPrefix pick t.val := by
  have h := chooseRank_mem (pick (Fin.ofNat (n + 1) t.val))
    (Finset.univ \ pickPrefix pick t.val) (pickPrefix_nonempty_sdiff pick t.isLt)
  exact (Finset.mem_sdiff.mp h).2

private lemma pickPrefix_mono {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n))
    {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) : pickPrefix pick t₁ ⊆ pickPrefix pick t₂ := by
  induction h with
  | refl => exact Finset.Subset.rfl
  | @step m _ ih =>
    refine ih.trans ?_
    simp only [pickPrefix]
    split_ifs
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.rfl

private lemma pickStepVertex_bijective {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n)) :
    Function.Bijective (pickStepVertex pick) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  intro t₁ t₂ heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmem : pickStepVertex pick t₁ ∈ pickPrefix pick t₂.val := by
      have h1 : pickStepVertex pick t₁ ∈ pickPrefix pick (t₁.val + 1) := by
        rw [pickPrefix_succ]; exact Finset.mem_insert_self _ _
      exact pickPrefix_mono pick hlt h1
    rw [heq] at hmem
    exact pickStepVertex_not_mem pick t₂ hmem
  · have hmem : pickStepVertex pick t₂ ∈ pickPrefix pick t₁.val := by
      have h1 : pickStepVertex pick t₂ ∈ pickPrefix pick (t₂.val + 1) := by
        rw [pickPrefix_succ]; exact Finset.mem_insert_self _ _
      exact pickPrefix_mono pick hgt h1
    rw [← heq] at hmem
    exact pickStepVertex_not_mem pick t₁ hmem

private noncomputable def pickTime {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n)) :
    Fin n ≃ Fin n :=
  (Equiv.ofBijective (pickStepVertex pick) (pickStepVertex_bijective pick)).symm

private lemma pickStepVertex_pickTime {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n)) (v : Fin n) :
    pickStepVertex pick (pickTime pick v) = v :=
  (Equiv.ofBijective (pickStepVertex pick) (pickStepVertex_bijective pick)).apply_symm_apply v

private lemma pickTime_pickStepVertex {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n)) (t : Fin n) :
    pickTime pick (pickStepVertex pick t) = t :=
  (Equiv.ofBijective (pickStepVertex pick) (pickStepVertex_bijective pick)).symm_apply_apply t

private noncomputable def Xat {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n)) (v : Fin n) :
    Finset (Fin n) :=
  pickPrefix pick ((pickTime pick v).val + 1)

private lemma mem_pickPrefix_iff {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n))
    (t : ℕ) (_ht : t ≤ n) (w : Fin n) :
    w ∈ pickPrefix pick t ↔ (pickTime pick w).val < t := by
  constructor
  · intro hw
    by_contra hge
    have hge' : t ≤ (pickTime pick w).val := Nat.le_of_not_lt hge
    have hsub : pickPrefix pick t ⊆ pickPrefix pick (pickTime pick w).val :=
      pickPrefix_mono pick hge'
    have hmem : w ∈ pickPrefix pick (pickTime pick w).val := hsub hw
    have hnot := pickStepVertex_not_mem pick (pickTime pick w)
    rw [pickStepVertex_pickTime] at hnot
    exact hnot hmem
  · intro hlt
    have h1 : w ∈ pickPrefix pick ((pickTime pick w).val + 1) := by
      rw [pickPrefix_succ, pickStepVertex_pickTime]
      exact Finset.mem_insert_self _ _
    exact pickPrefix_mono pick hlt h1

private lemma mem_Xat_iff {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n)) (v w : Fin n) :
    w ∈ Xat pick v ↔ (pickTime pick w).val ≤ (pickTime pick v).val := by
  unfold Xat
  rw [mem_pickPrefix_iff pick _ (pickTime pick v).isLt]
  omega

private lemma pickPrefix_act {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n))
    (σ : Equiv.Perm (Fin n)) :
    ∀ t : ℕ, pickPrefix (fun i => pick i * σ.symm) t = (pickPrefix pick t).image σ
  | 0 => by simp [pickPrefix]
  | t + 1 => by
    have ih := pickPrefix_act pick σ t
    have hsdiff : Finset.univ \ (pickPrefix pick t).image σ =
        (Finset.univ \ pickPrefix pick t).image σ := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hy
        refine ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
        intro hmem
        exact hy ⟨σ.symm y, hmem, σ.apply_symm_apply y⟩
      · rintro ⟨x, hx, rfl⟩ ⟨z, hz, heq⟩
        exact hx (σ.injective heq ▸ hz)
    simp only [pickPrefix, ih, hsdiff]
    by_cases h : (Finset.univ \ pickPrefix pick t).Nonempty
    · rw [dif_pos (h.image σ), dif_pos h, chooseRank_equivariant, Finset.image_insert]
    · have h' : ¬ ((Finset.univ \ pickPrefix pick t).image σ).Nonempty := by
        intro ⟨y, hy⟩
        obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hy
        exact h ⟨x, hx⟩
      rw [dif_neg h', dif_neg h]

private lemma pickStepVertex_act {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n))
    (σ : Equiv.Perm (Fin n)) (t : Fin n) :
    pickStepVertex (fun i => pick i * σ.symm) t = σ (pickStepVertex pick t) := by
  have h1 := pickPrefix_act pick σ (t.val + 1)
  rw [pickPrefix_succ, pickPrefix_succ, pickPrefix_act pick σ t.val, Finset.image_insert] at h1
  have hmem : pickStepVertex (fun i => pick i * σ.symm) t ∈
      insert (σ (pickStepVertex pick t)) ((pickPrefix pick t.val).image σ) := by
    rw [← h1]; exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp hmem with heq | hmem'
  · exact heq
  · exfalso
    rw [← pickPrefix_act pick σ t.val] at hmem'
    exact pickStepVertex_not_mem _ t hmem'

private lemma pickTime_act {n : ℕ} (pick : Fin (n + 1) → Equiv.Perm (Fin n))
    (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    pickTime (fun i => pick i * σ.symm) (σ v) = pickTime pick v := by
  have h := pickStepVertex_act pick σ (pickTime pick v)
  rw [pickStepVertex_pickTime] at h
  rw [← h, pickTime_pickStepVertex]

/-! ### Part 4: Deterministic lower bound on `probeCopy` queries for `K_{a, b}` -/

private noncomputable def Zset {n : ℕ} (a : ℕ) (s : ProbeSeed n) (X : Finset (Fin n)) (v : Fin n) :
    Finset (Fin n) :=
  (setA n a).filter fun w =>
    w ∈ X ∧ s.redo v w = true ∧
    ∀ w' ∈ setA n a, w' ∉ X → edgeCoin s v w' = true → s.order v w < s.order v w'

private noncomputable def Zval {n : ℕ} (a : ℕ) (s : ProbeSeed n) (v : Fin n) : ℕ :=
  (Zset a s (Xat s.pick v) v).card

private lemma Zval_le_a {n a : ℕ} (ha : a ≤ n) (s : ProbeSeed n) (v : Fin n) :
    Zval a s v ≤ a := by
  unfold Zval Zset
  exact (Finset.card_filter_le _ _).trans (card_setA ha).le

private lemma probeNeighbors_vertices_univ {n : ℕ} (v : Fin n) (tau : ℕ) (X : Finset (Fin n)) :
    ∀ (ws : List (Fin n)) (st : ProbeState n),
      st.vertices = Finset.univ → (probeNeighbors v tau X ws st).vertices = Finset.univ
  | [], st, h => h
  | w :: ws, st, h => by
    simp only [probeNeighbors]
    split_ifs
    · exact probeNeighbors_vertices_univ v tau X ws _ h
    · apply probeNeighbors_vertices_univ v tau X ws
      simp [h]
    · exact h

private lemma probeNeighbors_explored {n : ℕ} (v : Fin n) (tau : ℕ) (X : Finset (Fin n)) :
    ∀ (ws : List (Fin n)) (st : ProbeState n),
      (probeNeighbors v tau X ws st).explored = st.explored
  | [], st => rfl
  | w :: ws, st => by
    simp only [probeNeighbors]
    split_ifs
    · exact probeNeighbors_explored v tau X ws _
    · exact probeNeighbors_explored v tau X ws _
    · rfl

private lemma probeNeighbors_queries_mono {n : ℕ} (v : Fin n) (tau : ℕ) (X : Finset (Fin n)) :
    ∀ (ws : List (Fin n)) (st : ProbeState n),
      st.queries ≤ (probeNeighbors v tau X ws st).queries
  | [], st => le_rfl
  | w :: ws, st => by
    simp only [probeNeighbors]
    split_ifs
    · have ih := probeNeighbors_queries_mono v tau X ws { st with queries := st.queries + 1 }
      dsimp at ih; omega
    · have ih := probeNeighbors_queries_mono v tau X ws
        { st with vertices := insert w st.vertices, edges := insert s(v, w) st.edges,
                  queries := st.queries + 1 }
      dsimp at ih; omega
    · exact le_rfl

private lemma componentSize_ge_two_of_edge {n : ℕ} (st : ProbeState n) (v w : Fin n)
    (hvert : st.vertices = Finset.univ) (hne : w ≠ v) (he : s(v, w) ∈ st.edges) :
    2 ≤ componentSize st v := by
  unfold componentSize
  have hsub : ({v, w} : Finset (Fin n)) ⊆
      (Finset.univ : Finset (Fin n)).filter (fun u =>
        u ∈ st.vertices ∧
          (SimpleGraph.fromEdgeSet (st.edges : Set (Sym2 (Fin n)))).Reachable v u) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hvert]
    rcases Finset.mem_insert.mp hu with rfl | hu'
    · exact SimpleGraph.Reachable.refl _
    · rw [Finset.mem_singleton.mp hu']
      exact SimpleGraph.Adj.reachable ⟨he, hne.symm⟩
  calc 2 = ({v, w} : Finset (Fin n)).card := by rw [Finset.card_pair hne.symm]
    _ ≤ _ := Finset.card_le_card hsub

private lemma probeNeighbors_of_ge {n : ℕ} (v : Fin n) (tau : ℕ) (X : Finset (Fin n))
    (ws : List (Fin n)) (st : ProbeState n) (hge : tau ≤ componentSize st v) :
    probeNeighbors v tau X ws st = st := by
  cases ws with
  | nil => rfl
  | cons w ws =>
    simp only [probeNeighbors, if_neg (not_lt.mpr hge)]

private lemma probeNeighbors_edges_two {n : ℕ} (v : Fin n) (X : Finset (Fin n)) :
    ∀ (ws : List (Fin n)) (st : ProbeState n),
      st.vertices = Finset.univ → (∀ w ∈ ws, w ≠ v) →
      (probeNeighbors v 2 X ws st).edges = st.edges ∨
        ∃ w ∈ ws, (probeNeighbors v 2 X ws st).edges = insert s(v, w) st.edges
  | [], st, _, _ => Or.inl rfl
  | w :: ws, st, hv, hne => by
    simp only [probeNeighbors]
    by_cases hlt : componentSize st v < 2
    · rw [if_pos hlt]
      by_cases hw : w ∈ X
      · rw [if_pos hw]
        rcases probeNeighbors_edges_two v X ws { st with queries := st.queries + 1 } hv
            (fun u hu => hne u (List.mem_cons_of_mem w hu)) with h1 | ⟨w', hw', h2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨w', List.mem_cons_of_mem w hw', h2⟩
      · rw [if_neg hw]
        set st' : ProbeState n :=
          { st with vertices := insert w st.vertices, edges := insert s(v, w) st.edges,
                    queries := st.queries + 1 }
        have hv' : st'.vertices = Finset.univ := by simp [st', hv]
        have hge : 2 ≤ componentSize st' v :=
          componentSize_ge_two_of_edge st' v w hv' (hne w List.mem_cons_self)
            (Finset.mem_insert_self _ _)
        rw [probeNeighbors_of_ge v 2 X ws st' hge]
        exact Or.inr ⟨w, List.mem_cons_self, rfl⟩
    · rw [if_neg hlt]
      exact Or.inl rfl

private lemma componentSize_eq_one_of_no_edge {n : ℕ} (st : ProbeState n) (v : Fin n)
    (hv : st.vertices = Finset.univ) (hno : ∀ u, s(u, v) ∉ st.edges) :
    componentSize st v = 1 := by
  unfold componentSize
  have hfilt : (Finset.univ : Finset (Fin n)).filter (fun u =>
      u ∈ st.vertices ∧
        (SimpleGraph.fromEdgeSet (st.edges : Set (Sym2 (Fin n)))).Reachable v u) = {v} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hv, Finset.mem_singleton]
    constructor
    · rintro ⟨p⟩
      cases p with
      | nil => rfl
      | @cons _ x _ hadj _ =>
        exfalso
        have he : s(v, x) ∈ st.edges := hadj.1
        rw [Sym2.eq_swap] at he
        exact hno x he
    · rintro rfl
      exact SimpleGraph.Reachable.refl _
  rw [hfilt, Finset.card_singleton]

private lemma probeNeighbors_queries_ge_card {n : ℕ} (v : Fin n) (X : Finset (Fin n))
    (r : Fin n → Fin n) :
    ∀ (ws : List (Fin n)) (st : ProbeState n) (S : Finset (Fin n)),
      st.vertices = Finset.univ →
      (∀ u, s(u, v) ∉ st.edges) →
      ws.Nodup →
      ws.Pairwise (fun x y => r x ≤ r y) →
      (∀ w ∈ S, w ∈ ws ∧ w ∈ X) →
      (∀ w ∈ S, ∀ w' ∈ ws, w' ∉ X → r w < r w') →
      st.queries + S.card ≤ (probeNeighbors v 2 X ws st).queries
  | [], st, S, _, _, _, _, hS, _ => by
    have hSe : S = ∅ := by
      ext w; simp only [Finset.notMem_empty, iff_false]
      intro hw; exact List.not_mem_nil (hS w hw).1
    simp [probeNeighbors, hSe]
  | w :: ws, st, S, hv, hno, hnd, hpw, hS, hltS => by
    have hcs : componentSize st v < 2 := by
      rw [componentSize_eq_one_of_no_edge st v hv hno]; omega
    simp only [probeNeighbors, if_pos hcs]
    rw [List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hpw
    by_cases hw : w ∈ X
    · rw [if_pos hw]
      by_cases hwS : w ∈ S
      · have ih := probeNeighbors_queries_ge_card v X r ws { st with queries := st.queries + 1 }
          (S.erase w) hv hno hnd.2 hpw.2
          (fun u hu => by
            have hu' := Finset.mem_erase.mp hu
            have ⟨hmem, hX⟩ := hS u hu'.2
            exact ⟨(List.mem_cons.mp hmem).resolve_left hu'.1, hX⟩)
          (fun u hu w' hw' hw'X =>
            hltS u (Finset.mem_erase.mp hu).2 w' (List.mem_cons_of_mem w hw') hw'X)
        dsimp at ih
        have hcard : (S.erase w).card + 1 = S.card := Finset.card_erase_add_one hwS
        omega
      · have ih := probeNeighbors_queries_ge_card v X r ws { st with queries := st.queries + 1 }
          S hv hno hnd.2 hpw.2
          (fun u hu => by
            have ⟨hmem, hX⟩ := hS u hu
            have hne : u ≠ w := fun h => hwS (h ▸ hu)
            exact ⟨(List.mem_cons.mp hmem).resolve_left hne, hX⟩)
          (fun u hu w' hw' hw'X =>
            hltS u hu w' (List.mem_cons_of_mem w hw') hw'X)
        dsimp at ih
        omega
    · rw [if_neg hw]
      have hSe : S = ∅ := by
        ext u; simp only [Finset.notMem_empty, iff_false]
        intro hu
        have ⟨hmem, hX⟩ := hS u hu
        have hne : u ≠ w := fun h => hw (h ▸ hX)
        have huws : u ∈ ws := (List.mem_cons.mp hmem).resolve_left hne
        have hle : r w ≤ r u := hpw.1 u huws
        have hlt : r u < r w := hltS u hu w List.mem_cons_self hw
        exact not_lt_of_ge hle hlt
      rw [hSe, Finset.card_empty, add_zero]
      have hm := probeNeighbors_queries_mono v 2 X ws
        { st with vertices := insert w st.vertices, edges := insert s(v, w) st.edges,
                  queries := st.queries + 1 }
      dsimp at hm; omega

private lemma mem_orderedNeighbors_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : ProbeSeed n) (X : Finset (Fin n)) (v w : Fin n) :
    w ∈ orderedNeighbors G s X v ↔
      G.Adj v w ∧ (if w ∈ X then s.redo v w = true else edgeCoin s v w = true) := by
  unfold orderedNeighbors
  rw [List.mem_mergeSort, Finset.mem_toList, Finset.mem_filter]
  simp

private lemma nodup_orderedNeighbors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : ProbeSeed n) (X : Finset (Fin n)) (v : Fin n) :
    (orderedNeighbors G s X v).Nodup := by
  unfold orderedNeighbors
  rw [List.nodup_mergeSort]
  exact Finset.nodup_toList _

private lemma pairwise_orderedNeighbors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : ProbeSeed n) (X : Finset (Fin n)) (v : Fin n) :
    (orderedNeighbors G s X v).Pairwise (fun x y => s.order v x ≤ s.order v y) := by
  unfold orderedNeighbors
  have h := List.pairwise_mergeSort
    (le := fun a b => decide (s.order v a ≤ s.order v b))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact le_trans hab hbc)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total _ _)
    (((Finset.univ : Finset (Fin n)).filter fun w =>
      G.Adj v w ∧ if w ∈ X then s.redo v w else edgeCoin s v w).toList)
  simpa only [decide_eq_true_eq] using h

private noncomputable def unexpHitB (n a : ℕ) (st : ProbeState n) : Finset (Fin n) :=
  (setB n a \ st.explored).filter fun b => ∃ u, s(u, b) ∈ st.edges

private lemma probeLoop_lower_bound {n a : ℕ} (ha : a ≤ n) (s : ProbeSeed n) :
    ∀ (fuel : ℕ) (_hfuel : fuel ≤ n) (st : ProbeState n),
      st.vertices = Finset.univ →
      st.explored = pickPrefix s.pick (n - fuel) →
      st.queries + ∑ v ∈ setB n a \ st.explored, Zval a s v ≤
        (probeLoop (bipGraph n a) 2 s fuel st).queries +
          a * (unexpHitB n a st).card + a * (setA n a \ st.explored).card
  | 0, _, st, _, hexp => by
    rw [Nat.sub_zero, pickPrefix_univ] at hexp
    have hBe : setB n a \ Finset.univ = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ _)
    simp only [probeLoop, hexp, hBe, Finset.sum_empty, add_zero]
    omega
  | fuel + 1, hfuel, st, hv, hexp => by
    set t : ℕ := n - (fuel + 1)
    have ht : t < n := by omega
    let tFin : Fin n := ⟨t, ht⟩
    have hU : (st.vertices \ st.explored).Nonempty := by
      rw [hv, hexp]; exact pickPrefix_nonempty_sdiff s.pick ht
    simp only [probeLoop, dif_pos hU]
    have hv_eq : chooseRank (s.pick (Fin.ofNat (n + 1) (n - (fuel + 1))))
        (st.vertices \ st.explored) hU = pickStepVertex s.pick tFin := by
      simp only [pickStepVertex, tFin, t]
      congr 1; rw [hv, hexp]
    set v := chooseRank (s.pick (Fin.ofNat (n + 1) (n - (fuel + 1))))
        (st.vertices \ st.explored) hU
    set X := insert v st.explored
    set ws := orderedNeighbors (bipGraph n a) s X v
    set st' := probeNeighbors v 2 X ws { st with explored := X }
    have hv' : st'.vertices = Finset.univ :=
      probeNeighbors_vertices_univ v 2 X ws { st with explored := X } hv
    have hexp' : st'.explored = pickPrefix s.pick (n - fuel) := by
      rw [probeNeighbors_explored]
      show insert v st.explored = pickPrefix s.pick (n - fuel)
      have hnf : n - fuel = t + 1 := by omega
      rw [hnf, pickPrefix_succ s.pick tFin, ← hv_eq, hexp]
    have hX_eq : X = Xat s.pick v := by
      have hpt : pickTime s.pick v = tFin := by
        rw [hv_eq, pickTime_pickStepVertex]
      show insert v st.explored = Xat s.pick v
      unfold Xat
      rw [hpt, pickPrefix_succ s.pick tFin, ← hv_eq, hexp]
    have hv_not_exp : v ∉ st.explored := (Finset.mem_sdiff.mp (chooseRank_mem _ _ hU)).2
    have hih := probeLoop_lower_bound ha s fuel (by omega) st' hv' hexp'
    have hst'_exp : st'.explored = X := probeNeighbors_explored v 2 X ws { st with explored := X }
    have hws_ne : ∀ w ∈ ws, w ≠ v := by
      intro w hw
      have hadj := (mem_orderedNeighbors_iff (bipGraph n a) s X v w).mp hw |>.1
      exact hadj.ne.symm
    have hedges := probeNeighbors_edges_two v X ws { st with explored := X } hv hws_ne
    have hq_mono : st.queries ≤ st'.queries :=
      probeNeighbors_queries_mono v 2 X ws { st with explored := X }
    by_cases hvA : v.val < a
    · -- Case 1: v ∈ setA
      have hA_erase : setA n a \ st'.explored = (setA n a \ st.explored).erase v := by
        rw [hst'_exp]; ext u; simp only [Finset.mem_sdiff, Finset.mem_erase, X, Finset.mem_insert,
          not_or]; tauto
      have hv_in_A : v ∈ setA n a \ st.explored :=
        Finset.mem_sdiff.mpr ⟨mem_setA.mpr hvA, hv_not_exp⟩
      have hA_card : (setA n a \ st'.explored).card + 1 = (setA n a \ st.explored).card := by
        rw [hA_erase]; exact Finset.card_erase_add_one hv_in_A
      have hB_same : setB n a \ st'.explored = setB n a \ st.explored := by
        rw [hst'_exp]; ext u
        simp only [Finset.mem_sdiff, mem_setB, X, Finset.mem_insert, not_or]
        constructor
        · rintro ⟨hu, _, hne⟩; exact ⟨hu, hne⟩
        · rintro ⟨hu, hne⟩; exact ⟨hu, fun h => by subst h; omega, hne⟩
      have hHit_le : (unexpHitB n a st').card ≤ (unexpHitB n a st).card + 1 := by
        rcases hedges with heq | ⟨w, _, heq⟩
        · have hsub : unexpHitB n a st' = unexpHitB n a st := by
            unfold unexpHitB; rw [hB_same, heq]
          rw [hsub]; omega
        · have hsub : unexpHitB n a st' ⊆ insert w (unexpHitB n a st) := by
            intro b hb
            unfold unexpHitB at hb ⊢
            rw [hB_same, heq, Finset.mem_filter] at hb
            obtain ⟨hbB, u, hu⟩ := hb
            rcases Finset.mem_insert.mp hu with hsym | hold
            · have hb_ne_v : b ≠ v := by
                have := (Finset.mem_sdiff.mp hbB).1
                rw [mem_setB] at this; intro h; subst h; omega
              have hb_eq_w : b = w := by
                have hmem : b ∈ s(v, w) := by rw [← hsym]; exact Sym2.mem_mk_right u b
                rcases Sym2.mem_iff.mp hmem with rfl | rfl
                · exact absurd rfl hb_ne_v
                · rfl
              rw [hb_eq_w]; exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hbB, u, hold⟩)
          exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      rw [hB_same] at hih
      have hpot : a * (unexpHitB n a st').card + a * (setA n a \ st'.explored).card ≤
          a * (unexpHitB n a st).card + a * (setA n a \ st.explored).card := by
        have : a * (setA n a \ st.explored).card =
            a * (setA n a \ st'.explored).card + a := by rw [← hA_card]; ring
        have : a * (unexpHitB n a st').card ≤ a * (unexpHitB n a st).card + a := by
          calc a * (unexpHitB n a st').card
              ≤ a * ((unexpHitB n a st).card + 1) := Nat.mul_le_mul_left a hHit_le
            _ = a * (unexpHitB n a st).card + a := by ring
        omega
      omega
    · -- Case 2 & 3: v ∈ setB
      have hvB : a ≤ v.val := by omega
      have hA_same : setA n a \ st'.explored = setA n a \ st.explored := by
        rw [hst'_exp]; ext u
        simp only [Finset.mem_sdiff, mem_setA, X, Finset.mem_insert, not_or]
        constructor
        · rintro ⟨hu, _, hne⟩; exact ⟨hu, hne⟩
        · rintro ⟨hu, hne⟩; exact ⟨hu, fun h => by subst h; omega, hne⟩
      have hB_erase : setB n a \ st'.explored = (setB n a \ st.explored).erase v := by
        rw [hst'_exp]; ext u; simp only [Finset.mem_sdiff, Finset.mem_erase, X, Finset.mem_insert,
          not_or]; tauto
      have hv_in_B : v ∈ setB n a \ st.explored :=
        Finset.mem_sdiff.mpr ⟨mem_setB.mpr hvB, hv_not_exp⟩
      have hsum_split : ∑ u ∈ setB n a \ st.explored, Zval a s u =
          Zval a s v + ∑ u ∈ setB n a \ st'.explored, Zval a s u := by
        rw [hB_erase, ← Finset.add_sum_erase _ _ hv_in_B]
      have hHit_eq : unexpHitB n a st' = (unexpHitB n a st).erase v := by
        ext b
        unfold unexpHitB
        rw [hB_erase]
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨hbv, hbB⟩, u, hu⟩
          refine ⟨hbv, hbB, ?_⟩
          rcases hedges with heq | ⟨w, hw, heq⟩
          · rw [heq] at hu; exact ⟨u, hu⟩
          · rw [heq] at hu
            rcases Finset.mem_insert.mp hu with hsym | hold
            · exfalso
              have hadj := (mem_orderedNeighbors_iff (bipGraph n a) s X v w).mp hw |>.1
              have hwA : w.val < a := by
                rcases hadj with ⟨h1, _⟩ | ⟨_, h2⟩
                · omega
                · exact h2
              have hb_ge : a ≤ b.val := mem_setB.mp (Finset.mem_sdiff.mp hbB).1
              have hmem : b ∈ s(v, w) := by rw [← hsym]; exact Sym2.mem_mk_right u b
              rcases Sym2.mem_iff.mp hmem with rfl | rfl
              · exact hbv rfl
              · omega
            · exact ⟨u, hold⟩
        · rintro ⟨hbv, hbB, u, hu⟩
          refine ⟨⟨hbv, hbB⟩, u, ?_⟩
          rcases hedges with heq | ⟨w, _, heq⟩
          · rw [heq]; exact hu
          · rw [heq]; exact Finset.mem_insert_of_mem hu
      by_cases hvHit : v ∈ unexpHitB n a st
      · -- Case 2: v is already hit
        have hHit_card : (unexpHitB n a st').card + 1 = (unexpHitB n a st).card := by
          rw [hHit_eq]; exact Finset.card_erase_add_one hvHit
        have hZle : Zval a s v ≤ a := Zval_le_a ha s v
        rw [hA_same] at hih
        have hmul : a * (unexpHitB n a st).card = a * (unexpHitB n a st').card + a := by
          rw [← hHit_card]; ring
        omega
      · -- Case 3: v is isolated
        have hno : ∀ u, s(u, v) ∉ st.edges := by
          intro u hu
          exact hvHit (Finset.mem_filter.mpr ⟨hv_in_B, u, hu⟩)
        have hHit_card : (unexpHitB n a st').card = (unexpHitB n a st).card := by
          rw [hHit_eq, Finset.erase_eq_of_notMem hvHit]
        have hq_ge : st.queries + Zval a s v ≤ st'.queries := by
          unfold Zval
          rw [← hX_eq]
          apply probeNeighbors_queries_ge_card v X (s.order v) ws { st with explored := X }
            (Zset a s X v) hv hno (nodup_orderedNeighbors _ _ _ _)
            (pairwise_orderedNeighbors _ _ _ _)
          · intro w hw
            simp only [Zset, Finset.mem_filter, mem_setA] at hw
            refine ⟨?_, hw.2.1⟩
            rw [mem_orderedNeighbors_iff]
            exact ⟨Or.inr ⟨hvB, hw.1⟩, by simp [hw.2.1, hw.2.2.1]⟩
          · intro w hw w' hw' hw'X
            simp only [Zset, Finset.mem_filter, mem_setA] at hw
            rw [mem_orderedNeighbors_iff] at hw'
            have hw'A : w' ∈ setA n a := by
              rw [mem_setA]
              rcases hw'.1 with ⟨h1, _⟩ | ⟨_, h2⟩
              · omega
              · exact h2
            have hcoin : edgeCoin s v w' = true := by simpa [hw'X] using hw'.2
            exact hw.2.2.2 w' (mem_setA.mp hw'A) hw'X hcoin
        rw [hA_same, hHit_card] at hih
        omega

private lemma probeCopy_lower_bound {n a : ℕ} (ha : a ≤ n) (s : ProbeSeed n) :
    ∑ v ∈ setB n a, Zval a s v ≤ (probeCopy (bipGraph n a) Finset.univ 2 s).2 + a * a := by
  unfold probeCopy
  have h := probeLoop_lower_bound ha s n le_rfl
    { vertices := Finset.univ, edges := ∅, explored := ∅, queries := 0 } rfl (by simp [pickPrefix])
  have hhit : unexpHitB n a { vertices := Finset.univ, edges := ∅, explored := ∅, queries := 0 } = ∅ := by
    ext u; simp [unexpHitB]
  rw [hhit, Finset.card_empty, mul_zero, add_zero, Finset.sdiff_empty, Finset.sdiff_empty,
      card_setA ha, zero_add] at h
  exact h

/-! ### Part 5: Exact expectation of `Zval a s v` for fixed `v ∈ setB n a` -/

private lemma sum_perm_min_eq {n : ℕ} (S1 : Finset (Fin n)) (w : Fin n) (hw : w ∉ S1) :
    (∑ e : Equiv.Perm (Fin n), if (∀ w' ∈ S1, e w < e w') then (1 : ℝ) else 0) *
        ((S1.card : ℝ) + 1) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
  let M : Finset (Fin n) := insert w S1
  have hM : M.Nonempty := ⟨w, Finset.mem_insert_self _ _⟩
  have hMcard : (M.card : ℝ) = (S1.card : ℝ) + 1 := by
    rw [Finset.card_insert_of_notMem hw, Nat.cast_add, Nat.cast_one]
  have hiff : ∀ e : Equiv.Perm (Fin n),
      (∀ w' ∈ S1, e w < e w') ↔ chooseRank e M hM = w := by
    intro e
    rw [chooseRank_eq_iff e M hM w (Finset.mem_insert_self _ _)]
    constructor
    · intro h u hu
      rcases Finset.mem_insert.mp hu with rfl | hu'
      · exact le_rfl
      · exact (h u hu').le
    · intro h w' hw'
      have hle := h w' (Finset.mem_insert_of_mem hw')
      have hne : w ≠ w' := fun heq => hw (heq ▸ hw')
      exact lt_of_le_of_ne hle (fun heq => hne (e.injective heq))
  have heq_u : ∀ u ∈ M,
      (∑ e : Equiv.Perm (Fin n), if chooseRank e M hM = u then (1 : ℝ) else 0) =
      (∑ e : Equiv.Perm (Fin n), if chooseRank e M hM = w then (1 : ℝ) else 0) := by
    intro u hu
    let σ : Equiv.Perm (Fin n) := Equiv.swap w u
    let φ : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) := Equiv.mulRight σ.symm
    rw [← φ.sum_comp]
    apply Finset.sum_congr rfl
    intro e _
    have hMimg : M.image σ = M := by
      ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        by_cases hyw : y = w
        · subst hyw; simp [σ, hu]
        · by_cases hyu : y = u
          · subst hyu; simp [σ, M]
          · simp [σ, Equiv.swap_apply_of_ne_of_ne hyw hyu, hy]
      · intro hx
        refine ⟨σ x, ?_, by simp [σ]⟩
        by_cases hxw : x = w
        · subst hxw; simp [σ, hu]
        · by_cases hxu : x = u
          · subst hxu; simp [σ, M]
          · simp [σ, Equiv.swap_apply_of_ne_of_ne hxw hxu, hx]
    have hcr : chooseRank (e * σ.symm) M hM = σ (chooseRank e M hM) := by
      have h := chooseRank_equivariant e σ M hM
      simpa [hMimg] using h
    change (if chooseRank (e * σ.symm) M hM = u then (1 : ℝ) else 0) = _
    rw [hcr]
    have hswap : σ (chooseRank e M hM) = u ↔ chooseRank e M hM = w := by
      constructor
      · intro h
        have := congrArg σ h
        simpa [σ] using this
      · intro h; rw [h]; simp [σ]
    simp [hswap]
  have htot : (∑ u ∈ M, ∑ e : Equiv.Perm (Fin n), if chooseRank e M hM = u then (1 : ℝ) else 0) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    rw [Finset.sum_comm]
    have h1 : ∀ e : Equiv.Perm (Fin n),
        (∑ u ∈ M, if chooseRank e M hM = u then (1 : ℝ) else 0) = 1 := by
      intro e
      rw [Finset.sum_ite_eq M (chooseRank e M hM)]
      rw [if_pos (chooseRank_mem e M hM)]
    simp_rw [h1]
    simp
  have hsumM : (∑ u ∈ M, ∑ e : Equiv.Perm (Fin n), if chooseRank e M hM = u then (1 : ℝ) else 0) =
      (M.card : ℝ) * ∑ e : Equiv.Perm (Fin n), if chooseRank e M hM = w then (1 : ℝ) else 0 := by
    rw [Finset.sum_congr rfl heq_u, Finset.sum_const, nsmul_eq_mul]
  rw [hsumM, hMcard] at htot
  have hcongr :
      (∑ e : Equiv.Perm (Fin n), if (∀ w' ∈ S1, e w < e w') then (1 : ℝ) else 0) =
      (∑ e : Equiv.Perm (Fin n), if chooseRank e M hM = w then (1 : ℝ) else 0) :=
    Finset.sum_congr rfl fun e _ => by simp [hiff e]
  rw [hcongr, mul_comm]
  exact htot

private lemma expect_order_Zset {n a : ℕ} (v : Fin n) (X : Finset (Fin n))
    (coin redo : Fin n → Fin n → Bool) :
    let S2 := (setA n a ∩ X).filter (fun w => redo v w = true)
    let S1 := (setA n a \ X).filter (fun w' => coin w' v = true)
    ∑ ord : Fin n → Equiv.Perm (Fin n), orderW n *
      (((setA n a).filter fun w =>
        w ∈ X ∧ redo v w = true ∧
        ∀ w' ∈ setA n a, w' ∉ X → coin w' v = true → ord v w < ord v w').card : ℝ) =
      (S2.card : ℝ) / ((S1.card : ℝ) + 1) := by
  intro S2 S1
  have hcard_eq : ∀ ord : Fin n → Equiv.Perm (Fin n),
      (((setA n a).filter fun w =>
        w ∈ X ∧ redo v w = true ∧
        ∀ w' ∈ setA n a, w' ∉ X → coin w' v = true → ord v w < ord v w').card : ℝ) =
      ∑ w ∈ S2, if (∀ w' ∈ S1, ord v w < ord v w') then (1 : ℝ) else 0 := by
    intro ord
    have hfilt : ((setA n a).filter fun w =>
        w ∈ X ∧ redo v w = true ∧
        ∀ w' ∈ setA n a, w' ∉ X → coin w' v = true → ord v w < ord v w') =
        S2.filter (fun w => ∀ w' ∈ S1, ord v w < ord v w') := by
      ext w
      simp only [S2, S1, Finset.mem_filter, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro ⟨hwA, hwX, hredo, hlt⟩
        refine ⟨⟨⟨hwA, hwX⟩, hredo⟩, fun w' hw' => ?_⟩
        exact hlt w' hw'.1.1 hw'.1.2 hw'.2
      · rintro ⟨⟨⟨hwA, hwX⟩, hredo⟩, hlt⟩
        exact ⟨hwA, hwX, hredo, fun w' hw'A hw'X hc => hlt w' ⟨⟨hw'A, hw'X⟩, hc⟩⟩
    rw [hfilt, Finset.card_filter]
    simp
  simp_rw [hcard_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hsingle : ∀ w ∈ S2,
      ∑ ord : Fin n → Equiv.Perm (Fin n), orderW n *
        (if (∀ w' ∈ S1, ord v w < ord v w') then (1 : ℝ) else 0) =
      1 / ((S1.card : ℝ) + 1) := by
    intro w hw
    have hw_not_S1 : w ∉ S1 := by
      intro hw1
      have h1 := (Finset.mem_inter.mp (Finset.mem_filter.mp hw).1).2
      have h2 := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw1).1).2
      exact h2 h1
    have hprod := sum_prod_single_coord (fun _ : Equiv.Perm (Fin n) => permW n)
      (sum_permW_const n) v (fun e => if (∀ w' ∈ S1, e w < e w') then (1 : ℝ) else 0)
    change ∑ ord : Fin n → Equiv.Perm (Fin n), (∏ _ : Fin n, permW n) * _ = _
    rw [hprod, ← Finset.mul_sum]
    have hmin := sum_perm_min_eq S1 w hw_not_S1
    have hpos1 : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin n)) : ℝ) :=
      Nat.cast_pos.mpr Fintype.card_pos
    have hpos2 : (0 : ℝ) < (S1.card : ℝ) + 1 := by positivity
    unfold permW
    rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀ (ne_of_gt hpos1)]
    have hmin' : (∑ e : Equiv.Perm (Fin n), if (∀ w' ∈ S1, e w < e w') then (1 : ℝ) else 0) =
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * ((S1.card : ℝ) + 1)⁻¹ :=
      (eq_mul_inv_iff_mul_eq₀ (ne_of_gt hpos2)).mpr hmin
    rw [hmin']
  rw [Finset.sum_congr rfl hsingle, Finset.sum_const, nsmul_eq_mul]
  ring

private lemma expect_redo_card {n : ℕ} (p : ℝ) (v : Fin n) (A0 : Finset (Fin n)) :
    ∑ redo : Fin n → Fin n → Bool, coinW p redo *
      ((A0.filter fun w => redo v w = true).card : ℝ) = (A0.card : ℝ) * p := by
  have hcard : ∀ redo : Fin n → Fin n → Bool,
      ((A0.filter fun w => redo v w = true).card : ℝ) =
        ∑ w ∈ A0, if redo v w = true then (1 : ℝ) else 0 := by
    intro redo; rw [Finset.card_filter]; simp
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hsingle : ∀ w ∈ A0,
      ∑ redo : Fin n → Fin n → Bool, coinW p redo * (if redo v w = true then (1 : ℝ) else 0) = p := by
    intro w _
    unfold coinW
    have h1 := sum_prod_single_coord (fun r : Fin n → Bool => ∏ u : Fin n, bitW p (r u))
      (sum_coinW_row p) v (fun r => if r w = true then (1 : ℝ) else 0)
    rw [h1]
    have h2 := sum_prod_single_coord (fun b : Bool => bitW p b) (sum_bitW p) w
      (fun b => if b = true then (1 : ℝ) else 0)
    rw [h2]
    simp [bitW]
  rw [Finset.sum_congr rfl hsingle, Finset.sum_const, nsmul_eq_mul]

private lemma sum_row_filter_powerset {n : ℕ} (p : ℝ) (I : Finset (Fin n)) (g : Finset (Fin n) → ℝ) :
    ∑ r : Fin n → Bool, (∏ u : Fin n, bitW p (r u)) * g (I.filter fun u => r u = true) =
      ∑ S ∈ I.powerset, p ^ S.card * (1 - p) ^ (I.card - S.card) * g S := by
  induction I using Finset.induction_on generalizing g with
  | empty =>
    simp only [Finset.filter_empty, Finset.powerset_empty, Finset.sum_singleton,
      Finset.card_empty, Nat.sub_zero, pow_zero, mul_one, one_mul]
    rw [← Finset.sum_mul, sum_coinW_row, one_mul]
  | @insert x I hx ih =>
    -- Split by value of r x
    have hsplit : ∀ r : Fin n → Bool,
        (∏ u : Fin n, bitW p (r u)) * g ((insert x I).filter fun u => r u = true) =
          (∏ u : Fin n, bitW p (r u)) *
            (if r x = true then g (insert x (I.filter fun u => r u = true))
             else g (I.filter fun u => r u = true)) := by
      intro r
      congr 1
      by_cases hrx : r x = true
      · simp [Finset.filter_insert, hrx]
      · simp [Finset.filter_insert, hrx]
    simp_rw [hsplit]
    -- Factor out coordinate x using Function.update
    let eqv : (Fin n → Bool) ≃ Bool × ({u : Fin n // u ≠ x} → Bool) :=
      { toFun := fun r => (r x, fun u => r u.1)
        invFun := fun ⟨b, r'⟩ u => if h : u = x then b else r' ⟨u, h⟩
        left_inv := fun r => by funext u; by_cases h : u = x <;> simp [h]
        right_inv := fun ⟨b, r'⟩ => by
          ext
          · simp
          · rename_i u; simp [u.2] }
    have hprod_eq : ∀ b (r' : {u : Fin n // u ≠ x} → Bool),
        ∏ u : Fin n, bitW p (eqv.symm (b, r') u) =
          bitW p b * ∏ u : {u : Fin n // u ≠ x}, bitW p (r' u) := by
      intro b r'
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
      congr 1
      · simp [eqv]
      · refine Finset.prod_bij (fun u hu => ⟨u, Finset.ne_of_mem_erase hu⟩) ?_ ?_ ?_ ?_
        · intro u _; exact Finset.mem_univ _
        · intro u₁ _ u₂ _ h; simpa using congrArg Subtype.val h
        · intro u _; exact ⟨u.1, Finset.mem_erase.mpr ⟨u.2, Finset.mem_univ _⟩, by ext; rfl⟩
        · intro u hu; simp [eqv, Finset.ne_of_mem_erase hu]
    have hfilt_eq : ∀ b (r' : {u : Fin n // u ≠ x} → Bool),
        I.filter (fun u => eqv.symm (b, r') u = true) =
        I.filter (fun u => eqv.symm (false, r') u = true) := by
      intro b r'
      apply Finset.filter_congr
      intro u hu
      have hne : u ≠ x := fun h => hx (h ▸ hu)
      simp [eqv, hne]
    -- Even simpler: compute directly using eqv on BOTH sides!
    have hsub : ∀ h : Finset (Fin n) → ℝ,
        ∑ r : Fin n → Bool, (∏ u : Fin n, bitW p (r u)) *
          (if r x = true then h (I.filter fun u => r u = true) else 0) =
        p * ∑ r : Fin n → Bool, (∏ u : Fin n, bitW p (r u)) * h (I.filter fun u => r u = true) := by
      intro h
      rw [← eqv.symm.sum_comp, ← eqv.symm.sum_comp]
      simp only [Fintype.sum_prod_type]
      simp_rw [hprod_eq, hfilt_eq]
      simp only [eqv, Equiv.coe_fn_symm_mk, ↓reduceDIte]
      simp only [Fintype.sum_bool, bitW, ↓reduceIte, Bool.false_eq_true, mul_zero,
        Finset.sum_const_zero, add_zero]
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r' _; ring
    have hsubF : ∀ h : Finset (Fin n) → ℝ,
        ∑ r : Fin n → Bool, (∏ u : Fin n, bitW p (r u)) *
          (if r x = true then 0 else h (I.filter fun u => r u = true)) =
        (1 - p) * ∑ r : Fin n → Bool, (∏ u : Fin n, bitW p (r u)) * h (I.filter fun u => r u = true) := by
      intro h
      rw [← eqv.symm.sum_comp, ← eqv.symm.sum_comp]
      simp only [Fintype.sum_prod_type]
      simp_rw [hprod_eq, hfilt_eq]
      simp only [eqv, Equiv.coe_fn_symm_mk, ↓reduceDIte]
      simp only [Fintype.sum_bool, bitW, ↓reduceIte, Bool.false_eq_true, mul_zero,
        Finset.sum_const_zero, zero_add]
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r' _; ring
    have hite_split : ∀ r : Fin n → Bool,
        (∏ u : Fin n, bitW p (r u)) *
          (if r x = true then g (insert x (I.filter fun u => r u = true))
           else g (I.filter fun u => r u = true)) =
        (∏ u : Fin n, bitW p (r u)) *
          (if r x = true then g (insert x (I.filter fun u => r u = true)) else 0) +
        (∏ u : Fin n, bitW p (r u)) *
          (if r x = true then 0 else g (I.filter fun u => r u = true)) := by
      intro r; split_ifs <;> ring
    simp_rw [hite_split]
    rw [Finset.sum_add_distrib, hsub (fun S => g (insert x S)), hsubF g]
    rw [ih (fun S => g (insert x S)), ih g]
    rw [Finset.powerset_insert, Finset.sum_union]
    · rw [Finset.sum_image]
      · rw [add_comm, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl; intro S hS
          have hSsub := Finset.mem_powerset.mp hS
          have hcard : (insert x I).card - S.card = (I.card - S.card) + 1 := by
            rw [Finset.card_insert_of_notMem hx]
            have hle : S.card ≤ I.card := Finset.card_le_card hSsub
            omega
          rw [hcard, pow_succ]; ring
        · apply Finset.sum_congr rfl; intro S hS
          have hSsub := Finset.mem_powerset.mp hS
          have hxS : x ∉ S := fun h => hx (hSsub h)
          rw [Finset.card_insert_of_notMem hx, Finset.card_insert_of_notMem hxS,
              Nat.add_sub_add_right, pow_succ]
          ring
      · intro S₁ hS₁ S₂ hS₂ heq
        have hx₁ : x ∉ S₁ := fun h => hx (Finset.mem_powerset.mp hS₁ h)
        have hx₂ : x ∉ S₂ := fun h => hx (Finset.mem_powerset.mp hS₂ h)
        have := congrArg (fun T => T.erase x) heq
        simpa [Finset.erase_insert hx₁, Finset.erase_insert hx₂] using this
    · rw [Finset.disjoint_left]
      intro T hT hTimg
      obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hTimg
      exact hx (Finset.mem_powerset.mp hT (Finset.mem_insert_self x S))

private lemma sum_powerset_inv_card_add_one {n : ℕ} {p : ℝ} (hp : 0 < p) (I : Finset (Fin n)) :
    ∑ S ∈ I.powerset, p ^ S.card * (1 - p) ^ (I.card - S.card) * (1 / ((S.card : ℝ) + 1)) =
      (1 - (1 - p) ^ (I.card + 1)) / (((I.card : ℝ) + 1) * p) := by
  have hdenom : ((I.card : ℝ) + 1) * p ≠ 0 := by positivity
  rw [eq_div_iff hdenom, Finset.sum_mul]
  -- Group by card m ∈ range (I.card + 1)
  have hgroup :
      ∑ S ∈ I.powerset, p ^ S.card * (1 - p) ^ (I.card - S.card) * (1 / ((S.card : ℝ) + 1)) *
          (((I.card : ℝ) + 1) * p) =
      ∑ m ∈ Finset.range (I.card + 1),
        ((I.card.choose m : ℝ) * (p ^ m * (1 - p) ^ (I.card - m) * (1 / ((m : ℝ) + 1)) *
          (((I.card : ℝ) + 1) * p))) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := Finset.range (I.card + 1))
      (fun S hS => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_card (Finset.mem_powerset.mp hS))))]
    apply Finset.sum_congr rfl
    intro m hm
    have hfilt : I.powerset.filter (fun S => S.card = m) = I.powersetCard m := by
      ext S; simp [Finset.mem_powersetCard]
    have hcongr : ∀ S ∈ I.powerset.filter (fun S => S.card = m),
        p ^ S.card * (1 - p) ^ (I.card - S.card) * (1 / ((S.card : ℝ) + 1)) *
          (((I.card : ℝ) + 1) * p) =
        p ^ m * (1 - p) ^ (I.card - m) * (1 / ((m : ℝ) + 1)) * (((I.card : ℝ) + 1) * p) := by
      intro S hS
      rw [(Finset.mem_filter.mp hS).2]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, hfilt, Finset.card_powersetCard, nsmul_eq_mul]
  rw [hgroup]
  have hterm : ∀ m ∈ Finset.range (I.card + 1),
      (I.card.choose m : ℝ) * (p ^ m * (1 - p) ^ (I.card - m) * (1 / ((m : ℝ) + 1)) *
        (((I.card : ℝ) + 1) * p)) =
      ((I.card + 1).choose (m + 1) : ℝ) * p ^ (m + 1) * (1 - p) ^ ((I.card + 1) - (m + 1)) := by
    intro m _
    have hch : ((I.card : ℝ) + 1) * (I.card.choose m : ℝ) =
        ((I.card + 1).choose (m + 1) : ℝ) * ((m : ℝ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq I.card m
    have hmpos : (m : ℝ) + 1 ≠ 0 := by positivity
    rw [Nat.add_sub_add_right, pow_succ]
    calc (I.card.choose m : ℝ) * (p ^ m * (1 - p) ^ (I.card - m) * (1 / ((m : ℝ) + 1)) *
            (((I.card : ℝ) + 1) * p))
        = (((I.card : ℝ) + 1) * (I.card.choose m : ℝ)) / ((m : ℝ) + 1) *
            (p ^ m * p * (1 - p) ^ (I.card - m)) := by ring
      _ = (((I.card + 1).choose (m + 1) : ℝ) * ((m : ℝ) + 1)) / ((m : ℝ) + 1) *
            (p ^ m * p * (1 - p) ^ (I.card - m)) := by rw [hch]
      _ = ((I.card + 1).choose (m + 1) : ℝ) * (p ^ m * p) * (1 - p) ^ (I.card - m) := by
            rw [mul_div_cancel_right₀ _ hmpos]; ring
  rw [Finset.sum_congr rfl hterm]
  have hbinom := add_pow p (1 - p) (I.card + 1)
  rw [add_sub_cancel, one_pow] at hbinom
  rw [Finset.sum_range_succ'] at hbinom
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, Nat.sub_zero, one_mul] at hbinom
  have hsum_eq :
      ∑ m ∈ Finset.range (I.card + 1),
        ((I.card + 1).choose (m + 1) : ℝ) * p ^ (m + 1) * (1 - p) ^ ((I.card + 1) - (m + 1)) =
      ∑ m ∈ Finset.range (I.card + 1),
        p ^ (m + 1) * (1 - p) ^ ((I.card + 1) - (m + 1)) * ((I.card + 1).choose (m + 1) : ℝ) := by
    apply Finset.sum_congr rfl; intro m _; ring
  rw [hsum_eq]
  linarith

private lemma expect_coin_inv_card {n : ℕ} {p : ℝ} (hp : 0 < p) (v : Fin n) (I : Finset (Fin n)) :
    ∑ coin : Fin n → Fin n → Bool, coinW p coin *
      (1 / (((I.filter fun w' => coin w' v = true).card : ℝ) + 1)) =
      (1 - (1 - p) ^ (I.card + 1)) / (((I.card : ℝ) + 1) * p) := by
  -- Transpose coin: c ↦ (fun w u => c u w) is a bijection preserving coinW!
  let trans : (Fin n → Fin n → Bool) ≃ (Fin n → Fin n → Bool) :=
    { toFun := fun c w u => c u w
      invFun := fun c w u => c u w
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← trans.sum_comp]
  have htrans_w : ∀ c : Fin n → Fin n → Bool, coinW p (trans c) = coinW p c := by
    intro c; unfold coinW; exact Finset.prod_comm
  simp_rw [htrans_w]
  have htrans_app : ∀ (c : Fin n → Fin n → Bool) (w' : Fin n), trans c w' v = c v w' :=
    fun _ _ => rfl
  simp_rw [htrans_app]
  unfold coinW
  rw [sum_prod_single_coord (fun r : Fin n → Bool => ∏ u : Fin n, bitW p (r u))
    (sum_coinW_row p) v (fun r => 1 / (((I.filter fun w' => r w' = true).card : ℝ) + 1))]
  rw [sum_row_filter_powerset p I (fun S => 1 / ((S.card : ℝ) + 1))]
  exact sum_powerset_inv_card_add_one hp I

private lemma expect_pick_rank {n a : ℕ} (ha : a < n) (v : Fin n) (hvB : a ≤ v.val)
    (f : ℕ → ℝ) :
    ∑ pick : Fin (n + 1) → Equiv.Perm (Fin n), pickW n * f ((setA n a ∩ Xat pick v).card) =
      (1 / ((a : ℝ) + 1)) * ∑ j ∈ Finset.range (a + 1), f j := by
  let A' : Finset (Fin n) := insert v (setA n a)
  have hv_not_A : v ∉ setA n a := by rw [mem_setA]; omega
  have hA'_card : A'.card = a + 1 := by
    rw [Finset.card_insert_of_notMem hv_not_A, card_setA ha.le]
  let rk : (Fin (n + 1) → Equiv.Perm (Fin n)) → Fin n → ℕ :=
    fun pick u => (A'.filter fun w => (pickTime pick w).val < (pickTime pick u).val).card
  have hrk_v : ∀ pick, (setA n a ∩ Xat pick v).card = rk pick v := by
    intro pick
    congr 1
    ext w
    simp only [A', Finset.mem_inter, mem_Xat_iff, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hwA, hle⟩
      refine ⟨Or.inr hwA, ?_⟩
      have hne : w ≠ v := fun h => hv_not_A (h ▸ hwA)
      exact lt_of_le_of_ne hle (fun heq => hne ((pickTime pick).injective (Fin.ext heq)))
    · rintro ⟨rfl | hwA, hlt⟩
      · exact absurd hlt (lt_irrefl _)
      · exact ⟨hwA, hlt.le⟩
  simp_rw [hrk_v]
  -- All u ∈ A' have the same pick-expectation of f (rk pick u)
  have hsym : ∀ u ∈ A',
      (∑ pick : Fin (n + 1) → Equiv.Perm (Fin n), pickW n * f (rk pick u)) =
      (∑ pick : Fin (n + 1) → Equiv.Perm (Fin n), pickW n * f (rk pick v)) := by
    intro u hu
    let σ : Equiv.Perm (Fin n) := Equiv.swap v u
    let φ : (Fin (n + 1) → Equiv.Perm (Fin n)) ≃ (Fin (n + 1) → Equiv.Perm (Fin n)) :=
      Equiv.piCongrRight fun _ => Equiv.mulRight σ.symm
    rw [← φ.sum_comp]
    apply Finset.sum_congr rfl
    intro pick _
    have hA'img : A'.image σ = A' := by
      ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        by_cases hyv : y = v
        · subst hyv; simp [σ, hu]
        · by_cases hyu : y = u
          · subst hyu; simp [σ, A']
          · simp [σ, Equiv.swap_apply_of_ne_of_ne hyv hyu, hy]
      · intro hx
        refine ⟨σ x, ?_, by simp [σ]⟩
        by_cases hxv : x = v
        · subst hxv; simp [σ, hu]
        · by_cases hxu : x = u
          · subst hxu; simp [σ, A']
          · simp [σ, Equiv.swap_apply_of_ne_of_ne hxv hxu, hx]
    have hrk_eq : rk (φ pick) u = rk pick v := by
      change (A'.filter fun w => (pickTime (fun i => pick i * σ.symm) w).val <
          (pickTime (fun i => pick i * σ.symm) u).val).card =
        (A'.filter fun w => (pickTime pick w).val < (pickTime pick v).val).card
      have hu_eq : u = σ v := by simp [σ]
      rw [hu_eq, pickTime_act]
      have hcard_img :
          ((A'.filter fun w => (pickTime pick w).val < (pickTime pick v).val).image σ).card =
          (A'.filter fun w => (pickTime pick w).val < (pickTime pick v).val).card :=
        Finset.card_image_of_injective _ σ.injective
      rw [← hcard_img]
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hy, hlt⟩
        have hy' : σ y ∈ A' := by
          have : y ∈ A'.image σ := hA'img.symm ▸ hy
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp this
          simpa [σ] using hz
        refine ⟨σ y, ⟨hy', ?_⟩, by simp [σ]⟩
        have hact := pickTime_act pick σ (σ y)
        simp only [σ, Equiv.swap_apply_self] at hact
        have hact' : pickTime (fun i => pick i * σ.symm) y = pickTime pick (σ y) := by
          have := pickTime_act pick σ (σ y)
          simpa [σ] using this
        rw [← hact']; exact hlt
      · rintro ⟨z, ⟨hz, hlt⟩, rfl⟩
        refine ⟨hA'img ▸ Finset.mem_image_of_mem σ hz, ?_⟩
        rw [pickTime_act]; exact hlt
    rw [hrk_eq]
  -- For any fixed pick, ∑ u ∈ A', f (rk pick u) = ∑ j ∈ range (a + 1), f j
  have hsum_fixed : ∀ pick : Fin (n + 1) → Equiv.Perm (Fin n),
      ∑ u ∈ A', f (rk pick u) = ∑ j ∈ Finset.range (a + 1), f j := by
    intro pick
    have hinj : Set.InjOn (rk pick) (A' : Set (Fin n)) := by
      intro u₁ hu₁ u₂ hu₂ heq
      by_contra hne
      have htne : (pickTime pick u₁).val ≠ (pickTime pick u₂).val :=
        fun h => hne ((pickTime pick).injective (Fin.ext h))
      rcases lt_or_gt_of_ne htne with hlt | hgt
      · have hss : (A'.filter fun w => (pickTime pick w).val < (pickTime pick u₁).val) ⊂
            (A'.filter fun w => (pickTime pick w).val < (pickTime pick u₂).val) := by
          rw [Finset.ssubset_iff_of_subset]
          · exact ⟨u₁, Finset.mem_filter.mpr ⟨hu₁, hlt⟩, by simp⟩
          · intro w hw
            simp only [Finset.mem_filter] at hw ⊢
            exact ⟨hw.1, lt_trans hw.2 hlt⟩
        exact ne_of_lt (Finset.card_lt_card hss) heq
      · have hss : (A'.filter fun w => (pickTime pick w).val < (pickTime pick u₂).val) ⊂
            (A'.filter fun w => (pickTime pick w).val < (pickTime pick u₁).val) := by
          rw [Finset.ssubset_iff_of_subset]
          · exact ⟨u₂, Finset.mem_filter.mpr ⟨hu₂, hgt⟩, by simp⟩
          · intro w hw
            simp only [Finset.mem_filter] at hw ⊢
            exact ⟨hw.1, lt_trans hw.2 hgt⟩
        exact ne_of_gt (Finset.card_lt_card hss) heq
    have himg_sub : A'.image (rk pick) ⊆ Finset.range (a + 1) := by
      intro j hj
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
      rw [Finset.mem_range, ← hA'_card]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
      exact ⟨u, hu, by simp⟩
    have himg_eq : A'.image (rk pick) = Finset.range (a + 1) :=
      Finset.eq_of_subset_of_card_le himg_sub
        (by rw [Finset.card_image_of_injOn hinj, hA'_card, Finset.card_range])
    rw [← himg_eq, Finset.sum_image hinj]
  have htot :
      ((a : ℝ) + 1) * ∑ pick : Fin (n + 1) → Equiv.Perm (Fin n), pickW n * f (rk pick v) =
        ∑ j ∈ Finset.range (a + 1), f j := by
    calc ((a : ℝ) + 1) * ∑ pick, pickW n * f (rk pick v)
        = (A'.card : ℝ) * ∑ pick, pickW n * f (rk pick v) := by rw [hA'_card]; push_cast; rfl
      _ = ∑ u ∈ A', ∑ pick, pickW n * f (rk pick u) := by
          rw [Finset.sum_congr rfl hsym, Finset.sum_const, nsmul_eq_mul]
      _ = ∑ pick, pickW n * ∑ u ∈ A', f (rk pick u) := by
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
      _ = ∑ pick, pickW n * ∑ j ∈ Finset.range (a + 1), f j :=
          Finset.sum_congr rfl fun pick _ => by rw [hsum_fixed]
      _ = (∑ pick : Fin (n + 1) → Equiv.Perm (Fin n), pickW n) *
            ∑ j ∈ Finset.range (a + 1), f j := by rw [← Finset.sum_mul]
      _ = ∑ j ∈ Finset.range (a + 1), f j := by rw [sum_pickW, one_mul]
  have ha1 : (a : ℝ) + 1 ≠ 0 := by positivity
  rw [← htot, one_div, inv_mul_cancel_left₀ ha1]

private lemma expect_Zval_exact {n a : ℕ} (ha : a < n) {p : ℝ} (hp : 0 < p)
    (v : Fin n) (hvB : a ≤ v.val) :
    ∑ s : ProbeSeed n, seedW p s * (Zval a s v : ℝ) =
      (1 / ((a : ℝ) + 1)) * ∑ j ∈ Finset.range (a + 1),
        ((j : ℝ) / (((a - j : ℕ) : ℝ) + 1)) * (1 - (1 - p) ^ (a - j + 1)) := by
  rw [sum_seedW_fn]
  have hinner : ∀ (pick : Fin (n + 1) → Equiv.Perm (Fin n)),
      ∑ coin : Fin n → Fin n → Bool, coinW p coin *
        ∑ redo : Fin n → Fin n → Bool, coinW p redo *
          ∑ ord : Fin n → Equiv.Perm (Fin n), orderW n *
            (Zval a ⟨pick, ord, coin, redo⟩ v : ℝ) =
      (((setA n a ∩ Xat pick v).card : ℝ) /
          (((a - (setA n a ∩ Xat pick v).card : ℕ) : ℝ) + 1)) *
        (1 - (1 - p) ^ (a - (setA n a ∩ Xat pick v).card + 1)) := by
    intro pick
    set X := Xat pick v
    have hZ_eq : ∀ (coin redo : Fin n → Fin n → Bool) (ord : Fin n → Equiv.Perm (Fin n)),
        (Zval a ⟨pick, ord, coin, redo⟩ v : ℝ) =
          (((setA n a).filter fun w =>
            w ∈ X ∧ redo v w = true ∧
            ∀ w' ∈ setA n a, w' ∉ X → coin w' v = true → ord v w < ord v w').card : ℝ) := by
      intro coin redo ord
      unfold Zval Zset
      congr 2
      apply Finset.filter_congr
      intro w _
      refine and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun w' hw' => ?_
      have hw'lt : w'.val < a := mem_setA.mp hw'
      have hnotle : ¬ (v ≤ w') := not_le.mpr (Fin.lt_def.mpr (lt_of_lt_of_le hw'lt hvB))
      simp [edgeCoin, hnotle, X]
    simp_rw [hZ_eq, expect_order_Zset v X _ _]
    have hfactor : ∀ (coin : Fin n → Fin n → Bool),
        ∑ redo : Fin n → Fin n → Bool, coinW p redo *
          ((((setA n a ∩ X).filter fun w => redo v w = true).card : ℝ) /
            ((((setA n a \ X).filter fun w' => coin w' v = true).card : ℝ) + 1)) =
        (((setA n a ∩ X).card : ℝ) * p) *
          (1 / ((((setA n a \ X).filter fun w' => coin w' v = true).card : ℝ) + 1)) := by
      intro coin
      have hrw : ∀ redo : Fin n → Fin n → Bool,
          coinW p redo *
            ((((setA n a ∩ X).filter fun w => redo v w = true).card : ℝ) /
              ((((setA n a \ X).filter fun w' => coin w' v = true).card : ℝ) + 1)) =
          (coinW p redo * (((setA n a ∩ X).filter fun w => redo v w = true).card : ℝ)) *
            (1 / ((((setA n a \ X).filter fun w' => coin w' v = true).card : ℝ) + 1)) := by
        intro redo; ring
      simp_rw [hrw]
      rw [← Finset.sum_mul, expect_redo_card]
    simp_rw [hfactor]
    have hrw2 : ∀ coin : Fin n → Fin n → Bool,
        coinW p coin * ((((setA n a ∩ X).card : ℝ) * p) *
          (1 / ((((setA n a \ X).filter fun w' => coin w' v = true).card : ℝ) + 1))) =
        (((setA n a ∩ X).card : ℝ) * p) *
          (coinW p coin * (1 / ((((setA n a \ X).filter fun w' => coin w' v = true).card : ℝ) + 1))) := by
      intro coin; ring
    simp_rw [hrw2]
    rw [← Finset.mul_sum, expect_coin_inv_card hp v (setA n a \ X)]
    have hcard_sdiff : (setA n a \ X).card = a - (setA n a ∩ X).card := by
      have h := Finset.card_sdiff_add_card_inter (setA n a) X
      rw [card_setA ha.le] at h
      omega
    rw [hcard_sdiff]
    have hpne : p ≠ 0 := ne_of_gt hp
    have hdne : ((a - (setA n a ∩ X).card : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hpne, hdne]
  simp_rw [hinner]
  exact expect_pick_rank ha v hvB
    (fun j => ((j : ℝ) / (((a - j : ℕ) : ℝ) + 1)) * (1 - (1 - p) ^ (a - j + 1)))

/-! ### Part 6: Harmonic / dyadic lower bound on `expect_Zval_exact` -/

private lemma dyadic_harmonic_block (j : ℕ) :
    (1 / 2 : ℝ) ≤ ∑ r ∈ Finset.Ico ((2 : ℕ) ^ j) ((2 : ℕ) ^ (j + 1)), (1 / (r : ℝ)) := by
  have hterm : ∀ r ∈ Finset.Ico ((2 : ℕ) ^ j) ((2 : ℕ) ^ (j + 1)),
      (1 / (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ)) ≤ 1 / (r : ℝ) := by
    intro r hr
    have h1 : 2 ^ j ≤ r := (Finset.mem_Ico.mp hr).1
    have h2 : r < 2 ^ (j + 1) := (Finset.mem_Ico.mp hr).2
    have hrpos : (0 : ℝ) < (r : ℝ) := by
      have hpow : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by omega)
      have hr1 : 0 < r := lt_of_lt_of_le Nat.zero_lt_one (le_trans hpow h1)
      exact Nat.cast_pos.mpr hr1
    exact one_div_le_one_div_of_le hrpos (Nat.cast_le.mpr h2.le)
  calc (1 / 2 : ℝ)
      = ((2 ^ (j + 1) - 2 ^ j : ℕ) : ℝ) * (1 / (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ)) := by
        have hsub : 2 ^ (j + 1) - 2 ^ j = 2 ^ j := by rw [pow_succ]; omega
        rw [hsub, pow_succ]
        push_cast
        have hpos : (2 : ℝ) ^ j ≠ 0 := by positivity
        field_simp [hpos]
    _ = ∑ _ ∈ Finset.Ico ((2 : ℕ) ^ j) ((2 : ℕ) ^ (j + 1)), (1 / (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ)) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ ∑ r ∈ Finset.Ico ((2 : ℕ) ^ j) ((2 : ℕ) ^ (j + 1)), (1 / (r : ℝ)) :=
        Finset.sum_le_sum hterm

private lemma dyadic_harmonic_sum (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) :
    ((k₂ - k₁ : ℕ) : ℝ) / 2 ≤ ∑ r ∈ Finset.Ico ((2 : ℕ) ^ k₁) ((2 : ℕ) ^ k₂), (1 / (r : ℝ)) := by
  induction hk with
  | refl => simp
  | @step m hm ih =>
    have hle1 : (2 : ℕ) ^ k₁ ≤ (2 : ℕ) ^ m := Nat.pow_le_pow_right (by omega) hm
    have hle2 : (2 : ℕ) ^ m ≤ (2 : ℕ) ^ (m + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ m)
    change ((m + 1 - k₁ : ℕ) : ℝ) / 2 ≤
      ∑ r ∈ Finset.Ico ((2 : ℕ) ^ k₁) ((2 : ℕ) ^ (m + 1)), (1 / (r : ℝ))
    rw [← Finset.sum_Ico_consecutive _ hle1 hle2]
    have hblock := dyadic_harmonic_block m
    have hm' : k₁ ≤ m := hm
    have hsub : m + 1 - k₁ = (m - k₁) + 1 := by omega
    rw [hsub]
    push_cast
    linarith

private lemma expect_Zval_ge_336 {n a : ℕ} (hn : a < n)
    (hdyad : (484 : ℝ) ≤ ∑ m ∈ Finset.Ico ((2 : ℕ) ^ 31) a, (1 / (m : ℝ)))
    (v : Fin n) (hvB : a ≤ v.val) :
    (336 : ℝ) ≤ ∑ s : ProbeSeed n, seedW (1 / (2 : ℝ) ^ 30) s * (Zval a s v : ℝ) := by
  set p : ℝ := 1 / (2 : ℝ) ^ 30
  have hp : 0 < p := by positivity
  have hp1 : p ≤ 1 := by norm_num [p]
  rw [expect_Zval_exact hn hp v hvB]
  have hrefl := Finset.sum_range_reflect
    (fun j => ((j : ℝ) / (((a - j : ℕ) : ℝ) + 1)) * (1 - (1 - p) ^ (a - j + 1))) (a + 1)
  rw [← hrefl]
  have hsimp : ∀ r ∈ Finset.range (a + 1),
      ((((a + 1 - 1 - r : ℕ) : ℝ) / (((a - (a + 1 - 1 - r) : ℕ) : ℝ) + 1)) *
        (1 - (1 - p) ^ (a - (a + 1 - 1 - r) + 1))) =
      ((a : ℝ) + 1) * ((1 - (1 - p) ^ (r + 1)) / ((r : ℝ) + 1)) - (1 - (1 - p) ^ (r + 1)) := by
    intro r hr
    have hrle : r ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have h1 : a + 1 - 1 - r = a - r := by omega
    have h2 : a - (a - r) = r := by omega
    rw [h1, h2, Nat.cast_sub hrle]
    have hd : (r : ℝ) + 1 ≠ 0 := by linarith [Nat.cast_nonneg (α := ℝ) r]
    field_simp [hd]
    ring
  rw [Finset.sum_congr rfl hsimp, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have ha1 : (a : ℝ) + 1 ≠ 0 := by linarith [Nat.cast_nonneg (α := ℝ) a]
  have ha1_pos : (0 : ℝ) < (a : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) a]
  have hsplit : (1 / ((a : ℝ) + 1)) *
      (((a : ℝ) + 1) * (∑ r ∈ Finset.range (a + 1), (1 - (1 - p) ^ (r + 1)) / ((r : ℝ) + 1)) -
        ∑ r ∈ Finset.range (a + 1), (1 - (1 - p) ^ (r + 1))) =
      (∑ r ∈ Finset.range (a + 1), (1 - (1 - p) ^ (r + 1)) / ((r : ℝ) + 1)) -
        (1 / ((a : ℝ) + 1)) * ∑ r ∈ Finset.range (a + 1), (1 - (1 - p) ^ (r + 1)) := by
    field_simp [ha1]
  rw [hsplit]
  have hsecond : (1 / ((a : ℝ) + 1)) * ∑ r ∈ Finset.range (a + 1), (1 - (1 - p) ^ (r + 1)) ≤ 1 := by
    have hle1 : ∀ r ∈ Finset.range (a + 1), 1 - (1 - p) ^ (r + 1) ≤ 1 := by
      intro r _
      have : 0 ≤ (1 - p) ^ (r + 1) := pow_nonneg (by linarith) _
      linarith
    calc (1 / ((a : ℝ) + 1)) * ∑ r ∈ Finset.range (a + 1), (1 - (1 - p) ^ (r + 1))
        ≤ (1 / ((a : ℝ) + 1)) * ∑ _ ∈ Finset.range (a + 1), (1 : ℝ) := by
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hle1) (div_nonneg zero_le_one ha1_pos.le)
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          push_cast; field_simp [ha1]
  have hshift : ∑ r ∈ Finset.range (a + 1), (1 - (1 - p) ^ (r + 1)) / ((r : ℝ) + 1) =
      ∑ m ∈ Finset.Ico (1 : ℕ) (a + 2), (1 - (1 - p) ^ m) / (m : ℝ) := by
    refine Finset.sum_bij (fun r _ => r + 1) ?_ ?_ ?_ ?_
    · intro r hr
      rw [Finset.mem_range] at hr
      rw [Finset.mem_Ico]; omega
    · intro r₁ _ r₂ _ h; omega
    · intro m hm
      rw [Finset.mem_Ico] at hm
      exact ⟨m - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro r _; push_cast; rfl
  rw [hshift]
  have hsubIco : Finset.Ico ((2 : ℕ) ^ 31) a ⊆ Finset.Ico (1 : ℕ) (a + 2) := by
    intro m hm
    rw [Finset.mem_Ico] at hm ⊢
    have h1 : 1 ≤ (2 : ℕ) ^ 31 := Nat.one_le_pow 31 2 (by omega)
    omega
  have hnonneg : ∀ m ∈ Finset.Ico (1 : ℕ) (a + 2), 0 ≤ (1 - (1 - p) ^ m) / (m : ℝ) := by
    intro m _
    have h1mp : (1 - p) ^ m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    exact div_nonneg (by linarith) (Nat.cast_nonneg m)
  have hterm_ge : ∀ m ∈ Finset.Ico ((2 : ℕ) ^ 31) a,
      (3 / 4 : ℝ) * (1 / (m : ℝ)) ≤ (1 - (1 - p) ^ m) / (m : ℝ) := by
    intro m hm
    have hm1 : (2 : ℕ) ^ 31 ≤ m := (Finset.mem_Ico.mp hm).1
    have hm_le : (1 - p) ^ m ≤ 1 / 4 := by
      have h1 : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
      have h2 : (1 - p) ^ m ≤ (Real.exp (-p)) ^ m := pow_le_pow_left₀ (by linarith) h1 m
      rw [← Real.exp_nat_mul] at h2
      have hpm : (2 : ℝ) ≤ (m : ℝ) * p := by
        have hmR : (((2 : ℕ) ^ 31 : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm1
        have hcalc : (((2 : ℕ) ^ 31 : ℕ) : ℝ) * p = 2 := by
          rw [Nat.cast_pow, Nat.cast_ofNat]
          norm_num [p]
        nlinarith
      have h3 : Real.exp ((m : ℝ) * -p) ≤ Real.exp (-2) :=
        Real.exp_le_exp.mpr (by linarith)
      have h4 : Real.exp (-2) ≤ 1 / 4 := by
        rw [Real.exp_neg, show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        have he := Real.exp_one_gt_d9
        have hsq : (4 : ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith
        rw [inv_le_comm₀ (by positivity) (by norm_num)]
        linarith
      exact h2.trans (h3.trans h4)
    have hnum : (3 / 4 : ℝ) ≤ 1 - (1 - p) ^ m := by linarith
    have hmpos : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
    calc (3 / 4 : ℝ) * (1 / (m : ℝ))
        ≤ (1 - (1 - p) ^ m) * (1 / (m : ℝ)) := mul_le_mul_of_nonneg_right hnum hmpos
      _ = (1 - (1 - p) ^ m) / (m : ℝ) := by ring
  have hfirst : (337 : ℝ) ≤ ∑ m ∈ Finset.Ico (1 : ℕ) (a + 2), (1 - (1 - p) ^ m) / (m : ℝ) := by
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsubIco (fun m hm _ => hnonneg m hm)
    have h2 : (3 / 4 : ℝ) * ∑ m ∈ Finset.Ico ((2 : ℕ) ^ 31) a, (1 / (m : ℝ)) ≤
        ∑ m ∈ Finset.Ico ((2 : ℕ) ^ 31) a, (1 - (1 - p) ^ m) / (m : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum hterm_ge
    linarith
  linarith

/-! ### Part 7: Concrete parameter verification and final contradiction -/

private lemma param_k_delta (n : ℕ) (L eps : ℝ) (hL_def : L = Real.log (n : ℝ))
    (heps_def : eps = 3999999 / 4000000)
    (hL_lo : (1386 : ℝ) < L) (hL_hi : L < 1387) (hn_huge : (10 : ℝ) ^ 15 ≤ (n : ℝ)) :
    ∃ (k : ℕ) (delta : ℝ),
      1 ≤ k ∧ k ≤ n ∧ (k : ℝ) ≤ (n : ℝ) / (2 * L ^ 2) ∧
      2 * L ≤ delta ∧ delta ≤ 2 * L + 1 ∧
      rhoPar n k eps delta = 1 ∧ tauPar n k eps = 2 := by
  have heps : 0 < eps := by rw [heps_def]; norm_num
  have h2e_pos : 0 < 2 + eps := by rw [heps_def]; norm_num
  have hlog2_lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2_hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hLpos : 0 < L := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith [show (0 : ℝ) < (10 : ℝ) ^ 15 by norm_num]
  obtain ⟨num, hnum_def⟩ : ∃ num : ℝ, num = 2 * eps ^ 2 * (n : ℝ) / (2 + eps) - Real.log 2 :=
    ⟨_, rfl⟩
  obtain ⟨k, hk_def⟩ : ∃ k : ℕ, k = Nat.floor (num / (2 * L ^ 2)) := ⟨_, rfl⟩
  have hnum_ge : (1 / 2 : ℝ) * (n : ℝ) ≤ num := by
    have hcoef : (2 : ℝ) * eps ^ 2 / (2 + eps) > 0.6 := by rw [heps_def]; norm_num
    have hmul : (2 : ℝ) * eps ^ 2 * (n : ℝ) / (2 + eps) =
        (2 * eps ^ 2 / (2 + eps)) * (n : ℝ) := by ring
    rw [hnum_def, hmul]; nlinarith
  have hnum_le_n : num ≤ (n : ℝ) := by
    have hcoef : (2 : ℝ) * eps ^ 2 / (2 + eps) ≤ 1 := by rw [heps_def]; norm_num
    have hmul : (2 : ℝ) * eps ^ 2 * (n : ℝ) / (2 + eps) =
        (2 * eps ^ 2 / (2 + eps)) * (n : ℝ) := by ring
    rw [hnum_def, hmul]; nlinarith
  have h2L2_pos : 0 < 2 * L ^ 2 := by positivity
  have h2L2_le : 2 * L ^ 2 ≤ 4000000 := by nlinarith
  have hnum_over_ge : (10 : ℝ) ^ 8 ≤ num / (2 * L ^ 2) := by
    rw [le_div_iff₀ h2L2_pos]
    have h10 : (10 : ℝ) ^ 8 * 4000000 ≤ (1 / 2 : ℝ) * (10 : ℝ) ^ 15 := by norm_num
    nlinarith
  have hk_le_real : (k : ℝ) ≤ num / (2 * L ^ 2) := by
    rw [hk_def]
    exact Nat.floor_le (by linarith [show (0 : ℝ) ≤ (10 : ℝ) ^ 8 by norm_num])
  have hk_gt_sub : num / (2 * L ^ 2) - 1 < (k : ℝ) := by
    rw [hk_def]; linarith [Nat.lt_floor_add_one (num / (2 * L ^ 2))]
  have hk_ge_big : (10 : ℝ) ^ 7 ≤ (k : ℝ) := by
    have : (10 : ℝ) ^ 7 ≤ (10 : ℝ) ^ 8 - 1 := by norm_num
    linarith
  have hk1 : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos (by omega)
    rw [hk0] at hk_ge_big; norm_num at hk_ge_big
  have hk_lt_n : (k : ℝ) ≤ (n : ℝ) / (2 * L ^ 2) :=
    hk_le_real.trans (div_le_div_of_nonneg_right hnum_le_n h2L2_pos.le)
  have hkn : k ≤ n := by
    have h1 : (k : ℝ) ≤ (n : ℝ) := by
      have hden_ge : (1 : ℝ) ≤ 2 * L ^ 2 := by nlinarith
      exact hk_lt_n.trans (div_le_self hn_pos.le hden_ge)
    exact_mod_cast h1
  obtain ⟨delta, hdelta_def⟩ : ∃ delta : ℝ, delta = num / ((k : ℝ) * L) := ⟨_, rfl⟩
  have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk1
  have hdelta_ge : 2 * L ≤ delta := by
    rw [hdelta_def, le_div_iff₀ (mul_pos hkpos hLpos)]
    have h2 : (k : ℝ) * (2 * L ^ 2) ≤ num := (le_div_iff₀ h2L2_pos).mp hk_le_real
    linarith
  have hdelta_le : delta ≤ 2 * L + 1 := by
    have hnum_lt : num < ((k : ℝ) + 1) * (2 * L ^ 2) := (div_lt_iff₀ h2L2_pos).mp (by linarith)
    rw [hdelta_def, div_le_iff₀ (mul_pos hkpos hLpos)]
    have h2Lk : 2 * L ≤ (k : ℝ) := by
      have : (2 * 1387 : ℝ) ≤ (10 : ℝ) ^ 7 := by norm_num
      linarith
    have hmul : 2 * L ^ 2 ≤ (k : ℝ) * L := by
      have := mul_le_mul_of_nonneg_right h2Lk hLpos.le
      linarith
    linarith
  have hrho_eq : rhoPar n k eps delta = 1 := by
    unfold rhoPar
    rw [← hL_def]
    have hdkL : delta * (k : ℝ) * L = num := by
      rw [hdelta_def]
      have hne : (k : ℝ) * L ≠ 0 := ne_of_gt (mul_pos hkpos hLpos)
      field_simp [hne]
    rw [hdkL, hnum_def]
    have h2e : (2 : ℝ) + eps ≠ 0 := ne_of_gt h2e_pos
    have hden : 2 * eps ^ 2 * (n : ℝ) ≠ 0 := by positivity
    field_simp [h2e, hden]
    ring
  have htau_eq : tauPar n k eps = 2 := by
    unfold tauPar
    have hlog_lo : 1 - eps ≤ -Real.log eps := by
      linarith [Real.log_le_sub_one_of_pos heps]
    have hlog_hi : -Real.log eps ≤ (1 - eps) / eps := by
      have h1 := Real.log_le_sub_one_of_pos (inv_pos.mpr heps)
      rw [Real.log_inv] at h1
      have : eps⁻¹ - 1 = (1 - eps) / eps := by field_simp [ne_of_gt heps]
      linarith
    have hD_pos : 0 < (2 + eps) * L ^ 2 := by positivity
    have htau_gt1 : (1 : ℝ) < -((n : ℝ) * Real.log eps) / (eps * (k : ℝ)) := by
      rw [lt_div_iff₀ (mul_pos heps hkpos)]
      have hnum_le2 : num ≤ 2 * eps ^ 2 * (n : ℝ) / (2 + eps) := by rw [hnum_def]; linarith
      have hk_D : (k : ℝ) * ((2 + eps) * L ^ 2) ≤ eps ^ 2 * (n : ℝ) := by
        have h1 : (k : ℝ) * (2 * L ^ 2) ≤ 2 * eps ^ 2 * (n : ℝ) / (2 + eps) :=
          (le_div_iff₀ h2L2_pos).mp (hk_le_real.trans (div_le_div_of_nonneg_right hnum_le2 h2L2_pos.le))
        have h2 : (k : ℝ) * (2 * L ^ 2) * (2 + eps) ≤ 2 * eps ^ 2 * (n : ℝ) :=
          (le_div_iff₀ h2e_pos).mp h1
        linarith
      have hcoef : eps ^ 3 < (1 - eps) * ((2 + eps) * L ^ 2) := by
        have hL2 : (1386 : ℝ) ^ 2 < L ^ 2 := by
          have := mul_lt_mul hL_lo hL_lo.le (by norm_num) hLpos.le
          linarith
        have hc : eps ^ 3 < (1 - eps) * ((2 + eps) * (1386 : ℝ) ^ 2) := by
          rw [heps_def]; norm_num
        have hpos_c : (0 : ℝ) < (1 - eps) * (2 + eps) := by rw [heps_def]; norm_num
        have hmul := mul_lt_mul_of_pos_left hL2 hpos_c
        linarith
      have hprod : eps * (k : ℝ) < (n : ℝ) * (1 - eps) := by
        have hA : eps * (k : ℝ) * ((2 + eps) * L ^ 2) ≤ eps ^ 3 * (n : ℝ) := by
          have := mul_le_mul_of_nonneg_left hk_D heps.le
          linarith
        have hB : eps ^ 3 * (n : ℝ) < (n : ℝ) * (1 - eps) * ((2 + eps) * L ^ 2) := by
          have := mul_lt_mul_of_pos_right hcoef hn_pos
          linarith
        exact lt_of_mul_lt_mul_right (lt_of_le_of_lt hA hB) hD_pos.le
      have hmul_log := mul_le_mul_of_nonneg_left hlog_lo hn_pos.le
      linarith
    have htau_le2 : -((n : ℝ) * Real.log eps) / (eps * (k : ℝ)) ≤ 2 := by
      rw [div_le_iff₀ (mul_pos heps hkpos)]
      have hk_D_ge : (99 / 100 : ℝ) * (eps ^ 2 * (n : ℝ)) ≤ (k : ℝ) * ((2 + eps) * L ^ 2) := by
        have hnum_split : num / (2 * L ^ 2) =
            eps ^ 2 * (n : ℝ) / ((2 + eps) * L ^ 2) - Real.log 2 / (2 * L ^ 2) := by
          rw [hnum_def, sub_div]
          congr 1
          have h2e : (2 : ℝ) + eps ≠ 0 := ne_of_gt h2e_pos
          have hL0 : L ≠ 0 := ne_of_gt hLpos
          field_simp [h2e, hL0]
        have hlog_small : Real.log 2 / (2 * L ^ 2) ≤ 1 := by
          rw [div_le_one h2L2_pos]
          have : (1 : ℝ) ≤ 2 * L ^ 2 := by
            have hL1 : (1 : ℝ) ≤ L := by linarith
            have := mul_le_mul hL1 hL1 zero_le_one hLpos.le
            linarith
          linarith
        have h2_small : (200 : ℝ) * ((2 + eps) * L ^ 2) ≤ eps ^ 2 * (n : ℝ) := by
          have hL2 : L ^ 2 ≤ 1387 ^ 2 := by
            have := mul_le_mul hL_hi.le hL_hi.le hLpos.le (by norm_num)
            linarith
          have hc : (200 : ℝ) * ((2 + eps) * 1387 ^ 2) ≤ eps ^ 2 * (10 : ℝ) ^ 15 := by
            rw [heps_def]; norm_num
          have h1 := mul_le_mul_of_nonneg_left hL2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 200) h2e_pos.le)
          have h2 := mul_le_mul_of_nonneg_left hn_huge (sq_nonneg eps)
          linarith
        have hfrac : (2 : ℝ) ≤ (1 / 100 : ℝ) * (eps ^ 2 * (n : ℝ) / ((2 + eps) * L ^ 2)) := by
          have h200 : (200 : ℝ) ≤ eps ^ 2 * (n : ℝ) / ((2 + eps) * L ^ 2) :=
            (le_div_iff₀ hD_pos).mpr h2_small
          linarith
        have hk_ge_frac : (99 / 100 : ℝ) * (eps ^ 2 * (n : ℝ)) / ((2 + eps) * L ^ 2) ≤ (k : ℝ) := by
          rw [mul_div_assoc]; linarith
        exact (div_le_iff₀ hD_pos).mp hk_ge_frac
      have hcoef : (1 - eps) / eps * ((2 + eps) * L ^ 2) ≤ 2 * (99 / 100 : ℝ) * eps ^ 3 := by
        have hL2 : L ^ 2 ≤ 1387 ^ 2 := by
          have := mul_le_mul hL_hi.le hL_hi.le hLpos.le (by norm_num)
          linarith
        have hc : (1 - eps) / eps * ((2 + eps) * (1387 : ℝ) ^ 2) ≤
            2 * (99 / 100 : ℝ) * eps ^ 3 := by rw [heps_def]; norm_num
        have hpos_c : (0 : ℝ) < (1 - eps) / eps * (2 + eps) := by rw [heps_def]; norm_num
        have hmul := mul_le_mul_of_nonneg_left hL2 hpos_c.le
        linarith
      have hstep : (n : ℝ) * ((1 - eps) / eps) ≤ 2 * eps * (k : ℝ) := by
        have hA : (n : ℝ) * ((1 - eps) / eps) * ((2 + eps) * L ^ 2) ≤
            2 * (99 / 100 : ℝ) * eps ^ 3 * (n : ℝ) := by
          have := mul_le_mul_of_nonneg_right hcoef hn_pos.le
          linarith
        have hB : 2 * (99 / 100 : ℝ) * eps ^ 3 * (n : ℝ) ≤
            2 * eps * (k : ℝ) * ((2 + eps) * L ^ 2) := by
          have := mul_le_mul_of_nonneg_left hk_D_ge (by positivity : (0 : ℝ) ≤ 2 * eps)
          linarith
        exact le_of_mul_le_mul_right (le_trans hA hB) hD_pos
      have hmul_log := mul_le_mul_of_nonneg_left hlog_hi hn_pos.le
      linarith
    exact le_antisymm (Nat.ceil_le.mpr htau_le2)
      (Nat.succ_le_of_lt (Nat.lt_ceil.mpr (by exact_mod_cast htau_gt1)))
  exact ⟨k, delta, hk1, hkn, hk_lt_n, hdelta_ge, hdelta_le, hrho_eq, htau_eq⟩

private lemma param_T_Q_bounds (n k : ℕ) (L eps p delta : ℝ)
    (hL_def : L = Real.log (n : ℝ)) (heps_def : eps = 3999999 / 4000000)
    (hp_def : p = 1 / (2 : ℝ) ^ 30)
    (hL_lo : (1386 : ℝ) < L) (hL_hi : L < 1387)
    (hn_huge : (10 : ℝ) ^ 15 ≤ (n : ℝ)) (hk_lt : (k : ℝ) ≤ (n : ℝ) / (2 * L ^ 2))
    (hdelta_ge : 2 * L ≤ delta) (hdelta_le : delta ≤ 2 * L + 1)
    (hrho_eq : rhoPar n k eps delta = 1)
    (htau_eq : tauPar n k eps = 2) :
    0 < TPar n k eps delta ∧
    Real.sqrt (delta + Real.log (TPar n k eps delta : ℝ)) ≤ (n : ℝ) ∧
    0 ≤ QPar n k p eps delta ∧
    QPar n k p eps delta / (TPar n k eps delta : ℝ) ≤ 232 * (n : ℝ) := by
  have heps : 0 < eps := by rw [heps_def]; norm_num
  have hp0 : 0 ≤ p := by rw [hp_def]; positivity
  have hLpos : 0 < L := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith [show (0 : ℝ) < (10 : ℝ) ^ 15 by norm_num]
  have hlog2_lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2_hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  obtain ⟨T, hT_def⟩ : ∃ T : ℕ, T = TPar n k eps delta := ⟨_, rfl⟩
  rw [← hT_def]
  have hT_pos : 0 < T := by
    rw [hT_def]; unfold TPar
    apply Nat.lt_ceil.mpr
    simp only [Nat.cast_zero]
    rw [← hL_def]
    have hdpos : 0 < delta + Real.log 2 := by linarith
    have hk1pos : 0 < (k : ℝ) + 1 := by positivity
    exact div_pos (by positivity) (pow_pos heps 2)
  have hT_le : (T : ℝ) ≤ 32 * (n : ℝ) := by
    rw [hT_def]; unfold TPar
    rw [← hL_def]
    have h1 : delta + Real.log 2 ≤ 3 * L := by linarith
    have h2 : (k : ℝ) + 1 ≤ (n : ℝ) / L ^ 2 := by
      have h1L : (1 : ℝ) ≤ (n : ℝ) / (2 * L ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        have : 2 * L ^ 2 ≤ 4000000 := by nlinarith
        have : (4000000 : ℝ) ≤ (10 : ℝ) ^ 15 := by norm_num
        linarith
      have : (n : ℝ) / (2 * L ^ 2) + (n : ℝ) / (2 * L ^ 2) = (n : ℝ) / L ^ 2 := by ring
      linarith
    have hnum_le : 3 * (delta + Real.log 2) * ((k : ℝ) + 1) * L ≤ 9 * (n : ℝ) := by
      have hA : 3 * (delta + Real.log 2) * ((k : ℝ) + 1) ≤ 3 * (3 * L) * ((n : ℝ) / L ^ 2) := by
        have hA1 : 3 * (delta + Real.log 2) * ((k : ℝ) + 1) ≤ 3 * (3 * L) * ((k : ℝ) + 1) := by
          have : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
          nlinarith
        have hA2 : 3 * (3 * L) * ((k : ℝ) + 1) ≤ 3 * (3 * L) * ((n : ℝ) / L ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        linarith
      have hB : 3 * (delta + Real.log 2) * ((k : ℝ) + 1) * L ≤
          3 * (3 * L) * ((n : ℝ) / L ^ 2) * L := mul_le_mul_of_nonneg_right hA hLpos.le
      have hC : 3 * (3 * L) * ((n : ℝ) / L ^ 2) * L = 9 * (n : ℝ) := by
        have hL0 : L ≠ 0 := ne_of_gt hLpos
        field_simp [hL0]; ring
      linarith
    have harg : 3 * (delta + Real.log 2) * ((k : ℝ) + 1) * L / eps ^ 2 ≤ 30 * (n : ℝ) := by
      rw [div_le_iff₀ (pow_pos heps 2)]
      have he2 : (1 / 2 : ℝ) ≤ eps ^ 2 := by rw [heps_def]; norm_num
      nlinarith
    have harg0 : 0 ≤ 3 * (delta + Real.log 2) * ((k : ℝ) + 1) * L / eps ^ 2 := by
      have : 0 ≤ delta + Real.log 2 := by linarith
      positivity
    have hceil := Nat.ceil_lt_add_one harg0
    have h1n : (1 : ℝ) ≤ (n : ℝ) := by linarith [show (1 : ℝ) ≤ (10 : ℝ) ^ 15 by norm_num]
    linarith
  have hlogT_le : Real.log (T : ℝ) ≤ 1400 := by
    have h1 : Real.log (T : ℝ) ≤ Real.log (32 * (n : ℝ)) :=
      Real.log_le_log (Nat.cast_pos.mpr hT_pos) hT_le
    rw [Real.log_mul (by norm_num) (ne_of_gt hn_pos), ← hL_def] at h1
    have h32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
      rw [show (32 : ℝ) = (2 : ℝ) ^ 5 by norm_num, Real.log_pow]; norm_num
    rw [h32] at h1
    linarith
  have hsqrt_le : Real.sqrt (delta + Real.log (T : ℝ)) ≤ 65 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by linarith⟩
  have hsize : Real.sqrt (delta + Real.log (T : ℝ)) ≤ (n : ℝ) := by
    have h65 : (65 : ℝ) ≤ (10 : ℝ) ^ 15 := by norm_num
    linarith
  have hE_eq : EPar n k p eps = p := by
    unfold EPar; rw [htau_eq]; norm_num
  have hTposR : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT_pos
  have hC_le : CPar n k p eps delta ≤ 2 * (n : ℝ) * (T : ℝ) := by
    unfold CPar
    rw [← hT_def, hrho_eq, hE_eq, htau_eq, ← hL_def, Nat.cast_ofNat]
    have hlogT0 : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hT_pos)
    have hsq_arg : delta * ((2 : ℝ) * L + Real.log (T : ℝ)) * p ≤ 1 / 4 := by
      have h1 : delta * ((2 : ℝ) * L + Real.log (T : ℝ)) ≤ 2775 * (2 * 1387 + 1400) := by
        nlinarith
      have h2 : (2775 : ℝ) * (2 * 1387 + 1400) * p ≤ 1 / 4 := by rw [hp_def]; norm_num
      nlinarith
    have hsqrt_half : Real.sqrt (delta * ((2 : ℝ) * L + Real.log (T : ℝ)) * p) ≤ 1 / 2 := by
      rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by linarith⟩
    have hp_half : p ≤ 1 / 2 := by rw [hp_def]; norm_num
    have hsum2 : 1 + p + Real.sqrt (delta * ((2 : ℝ) * L + Real.log (T : ℝ)) * p) ≤ 2 := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsum2 (mul_nonneg hn_pos.le hTposR.le)
    linarith
  have hQ_nonneg : 0 ≤ QPar n k p eps delta := by
    unfold QPar CPar
    rw [← hT_def, hrho_eq, hE_eq]
    have h1 : 0 ≤ (n : ℝ) * 1 * (T : ℝ) *
        (1 + p + Real.sqrt (delta * ((tauPar n k eps : ℝ) * Real.log (n : ℝ) + Real.log (T : ℝ)) * p)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hn_pos.le zero_le_one) hTposR.le)
        (by linarith [Real.sqrt_nonneg (delta * ((tauPar n k eps : ℝ) * Real.log (n : ℝ) +
          Real.log (T : ℝ)) * p)])
    have h2 : 0 ≤ (2 + Real.sqrt 2) * (T : ℝ) * (n : ℝ) *
        Real.sqrt (delta + Real.log (T : ℝ)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith [Real.sqrt_nonneg 2]) hTposR.le)
        hn_pos.le) (Real.sqrt_nonneg _)
    linarith
  have hQ_le : QPar n k p eps delta / (T : ℝ) ≤ 232 * (n : ℝ) := by
    rw [div_le_iff₀ hTposR]
    unfold QPar
    rw [← hT_def]
    have hsqrt2 : Real.sqrt 2 ≤ 1.5 := by
      rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
    have hA : (2 + Real.sqrt 2) * Real.sqrt (delta + Real.log (T : ℝ)) ≤ 3.5 * 65 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (delta + Real.log (T : ℝ))]
    have hB : (2 + Real.sqrt 2) * (T : ℝ) * (n : ℝ) * Real.sqrt (delta + Real.log (T : ℝ)) ≤
        3.5 * 65 * (n : ℝ) * (T : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hA (mul_nonneg hn_pos.le hTposR.le)
      linarith
    nlinarith
  exact ⟨hT_pos, hsize, hQ_nonneg, hQ_le⟩

private lemma pow_setup :
    ∃ (a n : ℕ),
      a * a = n ∧ a < n ∧ 5 ≤ n ∧ 100 * a ≤ n ∧
      (1386 : ℝ) < Real.log (n : ℝ) ∧ Real.log (n : ℝ) < 1387 ∧
      (10 : ℝ) ^ 15 ≤ (n : ℝ) ∧
      (484 : ℝ) ≤ ∑ m ∈ Finset.Ico ((2 : ℕ) ^ 31) a, (1 / (m : ℝ)) := by
  refine ⟨2 ^ 1000, 2 ^ 2000, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← pow_add]
  · exact Nat.pow_lt_pow_right (by omega) (by omega)
  · exact le_trans (by norm_num : 5 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by omega) (by omega))
  · have h100 : 100 ≤ 2 ^ 1000 :=
      le_trans (by norm_num : 100 ≤ 2 ^ 7) (Nat.pow_le_pow_right (by omega) (by omega))
    calc 100 * 2 ^ 1000 ≤ 2 ^ 1000 * 2 ^ 1000 := Nat.mul_le_mul_right _ h100
      _ = 2 ^ 2000 := by rw [← pow_add]
  · rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]; push_cast; linarith [Real.log_two_gt_d9]
  · rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]; push_cast; linarith [Real.log_two_lt_d9]
  · have h1 : 2 ^ 50 ≤ 2 ^ 2000 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1R : (((2 : ℕ) ^ 50 : ℕ) : ℝ) ≤ (((2 : ℕ) ^ 2000 : ℕ) : ℝ) := Nat.cast_le.mpr h1
    have h2 : (10 : ℝ) ^ 15 ≤ (((2 : ℕ) ^ 50 : ℕ) : ℝ) := by norm_num
    linarith
  · have h := dyadic_harmonic_sum 31 1000 (by omega)
    have hnum : (484 : ℝ) ≤ ((1000 - 31 : ℕ) : ℝ) / 2 := by norm_num
    exact le_trans hnum h

private lemma counterexample_parameters :
    ∃ (n k : ℕ), 1 ≤ k ∧ k ≤ n ∧ 5 ≤ n ∧
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj)
        (p : ℝ), 0 ≤ p ∧ p ≤ 1 ∧
        ∃ (eps delta : ℝ), 0 < eps ∧ eps < 1 ∧
          2 * Real.log (n : ℝ) ≤ delta ∧
          rhoPar n k eps delta ≤ 1 ∧
          Real.sqrt (delta + Real.log (TPar n k eps delta)) ≤ (n : ℝ) ∧
          ¬ (1 - 3 * Real.exp (-delta) ≤
              probeEventProb (T := TPar n k eps delta) p
                (Nat.ceil ((n : ℝ) * rhoPar n k eps delta)) (fun Vrho ss =>
                  (queries G Vrho (tauPar n k eps) ss : ℝ) ≤ QPar n k p eps delta)) := by
  obtain ⟨a, n, ha_sq, ha_lt_n, hn5, h100a, hL_lo, hL_hi, hn_huge, hdyad⟩ := pow_setup
  obtain ⟨eps, heps_def⟩ : ∃ eps : ℝ, eps = 3999999 / 4000000 := ⟨_, rfl⟩
  obtain ⟨p, hp_def⟩ : ∃ p : ℝ, p = 1 / (2 : ℝ) ^ 30 := ⟨_, rfl⟩
  obtain ⟨k, delta, hk1, hkn, hk_lt, hdelta_ge, hdelta_le, hrho_eq, htau_eq⟩ :=
    param_k_delta n (Real.log (n : ℝ)) eps rfl heps_def hL_lo hL_hi hn_huge
  obtain ⟨hT_pos, hsize, hQ_nonneg, hQ_le⟩ :=
    param_T_Q_bounds n k (Real.log (n : ℝ)) eps p delta rfl heps_def hp_def
      hL_lo hL_hi hn_huge hk_lt hdelta_ge hdelta_le hrho_eq htau_eq
  have hp0 : 0 ≤ p := by rw [hp_def]; positivity
  have hp1 : p ≤ 1 := by rw [hp_def]; norm_num
  have heps : 0 < eps := by rw [heps_def]; norm_num
  have heps1 : eps < 1 := by rw [heps_def]; norm_num
  refine ⟨n, k, hk1, hkn, hn5, bipGraph n a, bipGraphDec n a,
          p, hp0, hp1, eps, delta, heps, heps1, hdelta_ge, hrho_eq.le, hsize, ?_⟩
  intro hthm
  have hceil_eq : Nat.ceil ((n : ℝ) * rhoPar n k eps delta) = n := by
    rw [hrho_eq, mul_one, Nat.ceil_natCast]
  rw [hceil_eq, htau_eq] at hthm
  have hexp_upper :
      ∑ s : ProbeSeed n, seedW p s * ((probeCopy (bipGraph n a) Finset.univ 2 s).2 : ℝ) ≤
        232 * (n : ℝ) + 3 := by
    have h := expect_single_le_of_prob_ge (by omega : 0 < n) hT_pos (bipGraph n a)
      p delta (QPar n k p eps delta) hp0 hp1 hQ_nonneg hdelta_ge hthm
    linarith
  have hexp_lower :
      (330 : ℝ) * (n : ℝ) ≤
        ∑ s : ProbeSeed n, seedW p s * ((probeCopy (bipGraph n a) Finset.univ 2 s).2 : ℝ) := by
    have hdet : ∀ s : ProbeSeed n,
        (∑ v ∈ setB n a, (Zval a s v : ℝ)) - (n : ℝ) ≤
          ((probeCopy (bipGraph n a) Finset.univ 2 s).2 : ℝ) := by
      intro s
      have h1 : (∑ v ∈ setB n a, Zval a s v : ℝ) ≤
          ((probeCopy (bipGraph n a) Finset.univ 2 s).2 : ℝ) + (n : ℝ) := by
        have hnat := probeCopy_lower_bound ha_lt_n.le s
        rw [ha_sq] at hnat
        exact_mod_cast hnat
      linarith
    have hsum_ge :
        ∑ s : ProbeSeed n, seedW p s * ((∑ v ∈ setB n a, (Zval a s v : ℝ)) - (n : ℝ)) ≤
          ∑ s : ProbeSeed n, seedW p s * ((probeCopy (bipGraph n a) Finset.univ 2 s).2 : ℝ) :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hdet s) (seedW_nonneg hp0 hp1 s)
    have hlhs_rw :
        ∑ s : ProbeSeed n, seedW p s * ((∑ v ∈ setB n a, (Zval a s v : ℝ)) - (n : ℝ)) =
          (∑ v ∈ setB n a, ∑ s : ProbeSeed n, seedW p s * (Zval a s v : ℝ)) - (n : ℝ) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_seedW, one_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hlhs_rw] at hsum_ge
    have hB_ge : ((setB n a).card : ℝ) * 336 ≤
        ∑ v ∈ setB n a, ∑ s : ProbeSeed n, seedW p s * (Zval a s v : ℝ) := by
      calc ((setB n a).card : ℝ) * 336
          = ∑ _ ∈ setB n a, (336 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ v ∈ setB n a, ∑ s : ProbeSeed n, seedW p s * (Zval a s v : ℝ) :=
            Finset.sum_le_sum fun v hv => by
              rw [hp_def]; exact expect_Zval_ge_336 ha_lt_n hdyad v (mem_setB.mp hv)
    have hcardB : (99 / 100 : ℝ) * (n : ℝ) ≤ ((setB n a).card : ℝ) := by
      rw [card_setB ha_lt_n.le, Nat.cast_sub ha_lt_n.le]
      have h1R : (100 : ℝ) * (a : ℝ) ≤ (n : ℝ) := by exact_mod_cast h100a
      linarith
    linarith
  linarith [show (3 : ℝ) < (10 : ℝ) ^ 15 by norm_num]

end Theorem5Disproof

theorem solution : ¬ (∀ (n k : ℕ),
    1 ≤ k →
      k ≤ n →
        5 ≤ n →
          ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℝ),
            0 ≤ p →
              p ≤ 1 →
                ∀ (eps delta : ℝ),
                  0 < eps →
                    eps < 1 →
                      2 * Real.log (n : ℝ) ≤ delta →
                        rhoPar n k eps delta ≤ 1 →
                          Real.sqrt (delta + Real.log (TPar n k eps delta)) ≤ (n : ℝ) →
                            1 - 3 * Real.exp (-delta) ≤
                              probeEventProb (T := TPar n k eps delta) p
                                (Nat.ceil ((n : ℝ) * rhoPar n k eps delta)) (fun Vrho ss =>
                                  (queries G Vrho (tauPar n k eps) ss : ℝ) ≤
                                    QPar n k p eps delta)) := by
  intro h
  obtain ⟨n, k, hk, hkn, hn, G, inst, p, hp0, hp1, eps, delta, heps, heps1,
          hdelta, hrho, hsize, hnot⟩ := Theorem5Disproof.counterexample_parameters
  exact hnot (@h n k hk hkn hn G inst p hp0 hp1 eps delta heps heps1 hdelta hrho hsize)
