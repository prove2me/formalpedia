-- Prove2me | solution 1 for BudgetAgg.NashChar.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T21:06:25.807042+00:00
-- url     : https://prove2.me/submissions/0c590a04-031a-4bb2-a9ef-bd6c31637683

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

open BudgetAgg.NashChar

theorem nc_leontief_le {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (k : Fin m)
    (hk : 0 < p.1 k) : leontief p q ≤ q k / p.1 k := by
  unfold leontief
  exact Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)

theorem nc_lt_leontief {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (c : ℝ)
    (h : ∀ k, 0 < p.1 k → c < q k / p.1 k) : c < leontief p q := by
  unfold leontief
  rw [Finset.lt_inf'_iff]
  intro k hk
  exact h k (Finset.mem_filter.mp hk).2

theorem nc_exists_crit {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) :
    ∃ k, 0 < p.1 k ∧ q k / p.1 k = leontief p q := by
  unfold leontief
  obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_inf' (positive_support_nonempty p)
    (fun j => q j / p.1 j)
  exact ⟨k, (Finset.mem_filter.mp hk).2, he.symm⟩

theorem nc_mem_crit {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (k : Fin m) :
    k ∈ crit p q ↔ 0 < p.1 k ∧ q k / p.1 k = leontief p q := by
  unfold crit
  simp [Finset.mem_filter]

/-- A distribution that makes every agent strictly better off violates core fair share
(take the grand coalition). -/
theorem nc_not_core {n m : ℕ} [NeZero n] (P : Profile n m) (q qs : stdSimplex ℝ (Fin m))
    (h : ∀ i, leontief (P i) q.1 < leontief (P i) qs.1) : ¬ IsCoreFairShare P q := by
  intro hc
  apply hc Finset.univ Finset.univ_nonempty
  refine ⟨qs, fun q'' i _ => ?_⟩
  have hn : ((Finset.univ : Finset (Fin n)).card : ℝ) / (n : ℝ) = 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact div_self (Nat.cast_ne_zero.mpr (NeZero.ne n))
  have hf : (fun j => ((Finset.univ : Finset (Fin n)).card : ℝ) / (n : ℝ) * qs.1 j +
      (1 - ((Finset.univ : Finset (Fin n)).card : ℝ) / (n : ℝ)) * q''.1 j) = qs.1 := by
    funext j; rw [hn]; ring
  rw [hf]
  exact h i

theorem nc_leontief_nonneg {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : stdSimplex ℝ (Fin m)) :
    0 ≤ leontief p q.1 := by
  obtain ⟨k, hk, hke⟩ := nc_exists_crit p q.1
  rw [← hke]; exact div_nonneg (q.2.1 k) hk.le

/-- Decomposition supported on critical alternatives ⇒ Nash optimality. -/
theorem nc_decomp_nash {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q : stdSimplex ℝ (Fin m)) (s : Fin n → Fin m → ℝ)
    (hs : IsDecomposition q.1 s) (hsupp : ∀ i j, j ∉ crit (P i) q.1 → s i j = 0) :
    IsNashOutcome P q.1 := by
  obtain ⟨hs0, hscol, hsrow⟩ := hs
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  -- on the support of s_i, q_j > 0 and q_j / p_ij = u_i(q)
  have hsup : ∀ i j, 0 < s i j → 0 < (P i).1 j ∧ q.1 j / (P i).1 j = leontief (P i) q.1 ∧
      0 < q.1 j := by
    intro i j hij
    have hc : j ∈ crit (P i) q.1 := by
      by_contra hc; rw [hsupp i j hc] at hij; exact lt_irrefl _ hij
    obtain ⟨hp, he⟩ := (nc_mem_crit _ _ j).mp hc
    have hqj : s i j ≤ q.1 j := by
      rw [← hscol j]
      exact Finset.single_le_sum (fun a _ => hs0 a j) (Finset.mem_univ i)
    exact ⟨hp, he, lt_of_lt_of_le hij hqj⟩
  have hupos : ∀ i, 0 < leontief (P i) q.1 := by
    intro i
    have : ∃ j, 0 < s i j := by
      by_contra h
      push_neg at h
      have : ∑ j, s i j ≤ 0 := Finset.sum_nonpos (fun j _ => h j)
      rw [hsrow i] at this
      have : (0 : ℝ) < 1 / n := by positivity
      linarith
    obtain ⟨j, hj⟩ := this
    obtain ⟨hp, he, hq⟩ := hsup i j hj
    rw [← he]; exact div_pos hq hp
  refine ⟨q.2, fun q' hq' => ?_⟩
  set q'' : stdSimplex ℝ (Fin m) := ⟨q', hq'⟩
  have hnn : ∀ i, 0 ≤ leontief (P i) q' := fun i => nc_leontief_nonneg (P i) q''
  by_cases hz : ∃ i, leontief (P i) q' = 0
  · obtain ⟨i, hi⟩ := hz
    have : nashProduct P q' = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [this]
    exact le_of_lt (Finset.prod_pos (fun i _ => hupos i))
  push_neg at hz
  have hpos' : ∀ i, 0 < leontief (P i) q' := fun i => lt_of_le_of_ne (hnn i) (Ne.symm (hz i))
  set r : Fin n → ℝ := fun i => leontief (P i) q' / leontief (P i) q.1 with hr
  have hrpos : ∀ i, 0 < r i := fun i => div_pos (hpos' i) (hupos i)
  -- r_i ≤ q'_j / q_j on the support of s_i
  have hrle : ∀ i j, 0 < s i j → r i ≤ q' j / q.1 j := by
    intro i j hij
    obtain ⟨hp, he, hq⟩ := hsup i j hij
    have h1 := nc_leontief_le (P i) q' j hp
    calc r i = leontief (P i) q' / (q.1 j / (P i).1 j) := by rw [he]
      _ ≤ (q' j / (P i).1 j) / (q.1 j / (P i).1 j) :=
          div_le_div_of_nonneg_right h1 (div_pos hq hp).le
      _ = q' j / q.1 j := by field_simp
  have hri : ∀ i, r i ≤ (n : ℝ) * ∑ j, s i j * (q' j / q.1 j) := by
    intro i
    have : r i = (n : ℝ) * ∑ j, s i j * r i := by
      rw [← Finset.sum_mul, hsrow i]; field_simp
    rw [this]
    apply mul_le_mul_of_nonneg_left _ hn.le
    apply Finset.sum_le_sum
    intro j _
    rcases lt_or_eq_of_le (hs0 i j) with h | h
    · exact mul_le_mul_of_nonneg_left (hrle i j h) (hs0 i j)
    · rw [← h]; simp
  have hsum : ∑ i, r i ≤ n := by
    calc ∑ i, r i ≤ ∑ i, (n : ℝ) * ∑ j, s i j * (q' j / q.1 j) := Finset.sum_le_sum (fun i _ => hri i)
      _ = (n : ℝ) * ∑ j, q.1 j * (q' j / q.1 j) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [← Finset.sum_mul, hscol j]
      _ ≤ (n : ℝ) * ∑ j, q' j := by
          apply mul_le_mul_of_nonneg_left _ hn.le
          apply Finset.sum_le_sum
          intro j _
          rcases lt_or_eq_of_le (q.2.1 j) with h | h
          · rw [mul_div_cancel₀ _ h.ne']
          · rw [← h, zero_mul]; exact hq'.1 j
      _ = n := by rw [hq'.2, mul_one]
  have hlog : ∑ i, Real.log (r i) ≤ 0 := by
    calc ∑ i, Real.log (r i) ≤ ∑ i, (r i - 1) :=
          Finset.sum_le_sum (fun i _ => Real.log_le_sub_one_of_pos (hrpos i))
      _ = ∑ i, r i - n := by
          rw [Finset.sum_sub_distrib]; simp
      _ ≤ 0 := by linarith
  have hprodpos : 0 < ∏ i, r i := Finset.prod_pos (fun i _ => hrpos i)
  have hprod : ∏ i, r i ≤ 1 := by
    rw [← Real.log_prod (fun i _ => (hrpos i).ne')] at hlog
    exact (Real.log_nonpos_iff hprodpos.le).mp hlog
  have heq : nashProduct P q' = (∏ i, r i) * nashProduct P q.1 := by
    unfold nashProduct
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp only [hr]
    field_simp [(hupos i).ne']
  rw [heq]
  have : 0 < nashProduct P q.1 := Finset.prod_pos (fun i _ => hupos i)
  nlinarith

/-- Fractional Hall theorem (equal demands `1/n`), proved by minimizing the convex potential
`∑_j col_j^2 / q_j` over shares supported on `T'`. -/
theorem nc_frac_hall {n m : ℕ} [NeZero n] [NeZero m] (T : Fin n → Finset (Fin m)) (q : Fin m → ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin m))
    (hH : ∀ G : Finset (Fin n), (G.card : ℝ) / (n : ℝ) ≤ ∑ j ∈ G.biUnion T, q j) :
    ∃ s : Fin n → Fin m → ℝ, IsDecomposition q s ∧ ∀ i j, j ∉ T i → s i j = 0 := by
  classical
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  set T' : Fin n → Finset (Fin m) := fun i => (T i).filter (fun j => 0 < q j) with hT'
  -- Hall condition is unchanged on `T'`
  have hsumT : ∀ G : Finset (Fin n), ∑ j ∈ G.biUnion T, q j = ∑ j ∈ G.biUnion T', q j := by
    intro G
    have : G.biUnion T' = (G.biUnion T).filter (fun j => 0 < q j) := by
      ext j; simp [hT', Finset.mem_biUnion, Finset.mem_filter]; tauto
    rw [this, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with h
    · rfl
    · exact le_antisymm (not_lt.mp h) (hq.1 j)
  have hT'ne : ∀ i, (T' i).Nonempty := by
    intro i
    have h1 := hH {i}
    rw [hsumT] at h1
    simp only [Finset.singleton_biUnion, Finset.card_singleton, Nat.cast_one] at h1
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at h1
    have : (0 : ℝ) < 1 / n := by positivity
    linarith
  -- feasible set
  set X : Set (Fin n → Fin m → ℝ) := {s | (∀ i j, 0 ≤ s i j) ∧ (∀ i j, j ∉ T' i → s i j = 0) ∧
      ∀ i, ∑ j, s i j = 1 / (n : ℝ)} with hX
  have hXc : IsCompact X := by
    have hsub : X ⊆ Set.Icc 0 (fun _ _ => 1 / (n : ℝ)) := by
      intro s hs
      refine ⟨fun i j => hs.1 i j, fun i j => ?_⟩
      rw [← hs.2.2 i]
      exact Finset.single_le_sum (fun k _ => hs.1 i k) (Finset.mem_univ j)
    apply isCompact_Icc.of_isClosed_subset _ hsub
    have e : X = (⋂ i, ⋂ j, {s : Fin n → Fin m → ℝ | 0 ≤ s i j}) ∩
        ((⋂ i, ⋂ j, {s : Fin n → Fin m → ℝ | s i j * (if j ∈ T' i then 0 else 1) = 0}) ∩
        (⋂ i, {s : Fin n → Fin m → ℝ | ∑ j, s i j = 1 / (n : ℝ)})) := by
      ext s
      simp only [hX, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, fun i j => ?_, h3⟩
        by_cases hj : j ∈ T' i
        · simp [hj]
        · simp [hj, h2 i j hj]
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, fun i j hj => ?_, h3⟩
        have := h2 i j; simpa [hj] using this
    rw [e]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
      (IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
        (isClosed_iInter fun i => ?_))
    · exact isClosed_le continuous_const (by fun_prop)
    · exact isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_eq (by fun_prop) continuous_const
  have hXne : X.Nonempty := by
    refine ⟨fun i j => if j ∈ T' i then (1 / (n : ℝ)) / ((T' i).card : ℝ) else 0, ?_, ?_, ?_⟩
    · intro i j; dsimp only; split_ifs <;> positivity
    · intro i j hj; simp [hj]
    · intro i
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      have : (0 : ℝ) < (T' i).card := Nat.cast_pos.mpr (Finset.card_pos.mpr (hT'ne i))
      field_simp
  -- potential
  let col : (Fin n → Fin m → ℝ) → Fin m → ℝ := fun s j => ∑ i, s i j
  let Ψ : (Fin n → Fin m → ℝ) → ℝ := fun s => ∑ j, (col s j) ^ 2 / q j
  have hΨc : Continuous Ψ := by
    apply continuous_finset_sum
    intro j _
    apply Continuous.div_const
    apply Continuous.pow
    exact continuous_finset_sum _ fun i _ => (continuous_apply j).comp (continuous_apply i)
  obtain ⟨s, hsX, hmin⟩ := hXc.exists_isMinOn hXne hΨc.continuousOn
  obtain ⟨hs0, hsT, hsrow⟩ := hsX
  set r : Fin m → ℝ := fun j => col s j / q j with hr
  -- support facts
  have hsupp_pos : ∀ i j, 0 < s i j → 0 < q j := by
    intro i j h
    by_contra hc
    have : j ∉ T' i := by simp [hT', hc]
    rw [hsT i j this] at h; exact lt_irrefl _ h
  -- local optimality: mass of agent `i` sits on alternatives of minimal ratio within `T' i`
  have hloc : ∀ i j j', 0 < s i j → j' ∈ T' i → r j ≤ r j' := by
    intro i j j' hij hj'
    by_contra hlt
    push_neg at hlt
    have hqj : 0 < q j := hsupp_pos i j hij
    have hqj' : 0 < q j' := (Finset.mem_filter.mp hj').2
    have hjj : j ≠ j' := by rintro rfl; exact lt_irrefl _ hlt
    set K := 1 / q j + 1 / q j' with hK
    have hKpos : 0 < K := by positivity
    set ε := min (s i j) ((r j - r j') / K) with hε
    have hεpos : 0 < ε := lt_min hij (div_pos (by linarith) hKpos)
    have hε1 : ε ≤ s i j := min_le_left _ _
    have hε2 : ε * K ≤ r j - r j' := by
      have := min_le_right (s i j) ((r j - r j') / K)
      rw [← hε] at this
      rwa [le_div_iff₀ hKpos] at this
    let s' : Fin n → Fin m → ℝ := fun a b =>
      s a b + (if a = i ∧ b = j' then ε else 0) - (if a = i ∧ b = j then ε else 0)
    have hs'X : s' ∈ X := by
      refine ⟨fun a b => ?_, fun a b hb => ?_, fun a => ?_⟩
      · simp only [s']
        by_cases h1 : a = i ∧ b = j
        · obtain ⟨rfl, rfl⟩ := h1
          have : ¬ (a = a ∧ b = j') := fun h => hjj h.2
          rw [if_neg this, if_pos ⟨rfl, rfl⟩]; linarith
        · simp only [h1, if_false]
          split_ifs <;> linarith [hs0 a b]
      · have hne : ¬ (a = i ∧ b = j') := by
          rintro ⟨rfl, rfl⟩; exact hb hj'
        have hne2 : ¬ (a = i ∧ b = j) := by
          rintro ⟨rfl, rfl⟩
          exact hb (by
            by_contra hc; rw [hsT a b hc] at hij; exact lt_irrefl _ hij)
        simp only [s', hne, hne2, if_false, hsT a b hb]; ring
      · simp only [s']
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsrow a]
        by_cases ha : a = i
        · subst ha; simp
        · simp [ha]
    have hcol' : ∀ b, col s' b = col s b + (if b = j' then ε else 0) - (if b = j then ε else 0) := by
      intro b
      simp only [col, s']
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      congr 1
      · congr 1
        rw [Finset.sum_eq_single i]
        · by_cases hb : b = j' <;> simp [hb]
        · intro a _ ha; simp [ha]
        · simp
      · rw [Finset.sum_eq_single i]
        · by_cases hb : b = j <;> simp [hb]
        · intro a _ ha; simp [ha]
        · simp
    have hle := hmin hs'X
    simp only [Set.mem_setOf_eq] at hle
    -- compute the change of Ψ
    have hdiff : Ψ s' - Ψ s = ε * (2 * (r j' - r j) + ε * K) := by
      simp only [Ψ]
      rw [← Finset.sum_sub_distrib]
      rw [Fintype.sum_eq_add j j' hjj]
      · rw [hcol' j, hcol' j']
        simp only [if_pos rfl, if_neg hjj, if_neg (Ne.symm hjj), hr, hK]
        have h1 : q j ≠ 0 := hqj.ne'
        have h2 : q j' ≠ 0 := hqj'.ne'
        simp only [if_true, add_zero, sub_zero]
        field_simp
        ring
      · intro b ⟨hb1, hb2⟩
        rw [hcol' b]; simp [hb1, hb2]
    have : ε * (2 * (r j' - r j) + ε * K) < 0 := by
      apply mul_neg_of_pos_of_neg hεpos; linarith
    linarith
  -- the maximal ratio is at most one
  set R := Finset.univ.sup' Finset.univ_nonempty r with hR
  have hR1 : R ≤ 1 := by
    by_contra hR1
    push_neg at hR1
    set U := Finset.univ.filter (fun j => r j = R) with hU
    set G := Finset.univ.filter (fun i => ∃ j ∈ U, 0 < s i j) with hG
    have hUq : ∀ j ∈ U, 0 < q j := by
      intro j hj
      have hj' : r j = R := (Finset.mem_filter.mp hj).2
      by_contra hc
      have : q j = 0 := le_antisymm (not_lt.mp hc) (hq.1 j)
      simp only [hr, this, div_zero] at hj'
      linarith
    have hUne : U.Nonempty := by
      obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty r
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.symm⟩⟩
    have hrR : ∀ j, r j ≤ R := fun j => Finset.le_sup' r (Finset.mem_univ j)
    have hT'U : G.biUnion T' ⊆ U := by
      intro j' hj'
      obtain ⟨i, hi, hj'i⟩ := Finset.mem_biUnion.mp hj'
      obtain ⟨j, hjU, hij⟩ := (Finset.mem_filter.mp hi).2
      have h1 := hloc i j j' hij hj'i
      have h2 : r j = R := (Finset.mem_filter.mp hjU).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_antisymm (hrR j') (h2 ▸ h1)⟩
    have hqU : (G.card : ℝ) / n ≤ ∑ j ∈ U, q j := by
      calc (G.card : ℝ) / n ≤ ∑ j ∈ G.biUnion T, q j := hH G
        _ = ∑ j ∈ G.biUnion T', q j := hsumT G
        _ ≤ ∑ j ∈ U, q j := Finset.sum_le_sum_of_subset_of_nonneg hT'U (fun j _ _ => hq.1 j)
    have hcolU : ∑ j ∈ U, col s j = R * ∑ j ∈ U, q j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have h2 : r j = R := (Finset.mem_filter.mp hj).2
      rw [← h2]; simp only [hr]; field_simp [(hUq j hj).ne']
    have hcolG : ∑ j ∈ U, col s j ≤ (G.card : ℝ) / n := by
      simp only [col]
      rw [Finset.sum_comm]
      calc ∑ i, ∑ j ∈ U, s i j = ∑ i ∈ G, ∑ j ∈ U, s i j := by
            symm
            apply Finset.sum_subset (Finset.subset_univ _)
            intro i _ hi
            apply Finset.sum_eq_zero
            intro j hj
            by_contra hne
            exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj,
              lt_of_le_of_ne (hs0 i j) (Ne.symm hne)⟩)
        _ ≤ ∑ i ∈ G, (1 / (n : ℝ)) := by
            apply Finset.sum_le_sum
            intro i _
            rw [← hsrow i]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun j _ _ => hs0 i j)
        _ = (G.card : ℝ) / n := by simp [div_eq_mul_inv]
    have hqUpos : 0 < ∑ j ∈ U, q j := Finset.sum_pos hUq hUne
    nlinarith
  -- conclude: column sums are at most q, hence equal
  have hcolle : ∀ j, col s j ≤ q j := by
    intro j
    rcases lt_or_eq_of_le (hq.1 j) with h | h
    · have : r j ≤ 1 := le_trans (Finset.le_sup' r (Finset.mem_univ j)) hR1
      simp only [hr] at this
      rwa [div_le_one h] at this
    · have : col s j = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        apply hsT
        simp [hT', ← h]
      rw [this, ← h]
  have htot : ∑ j, col s j = ∑ j, q j := by
    simp only [col]
    rw [Finset.sum_comm, hq.2]
    simp only [hsrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ => hcolle j)).mp htot
  refine ⟨s, ⟨hs0, fun j => heq j (Finset.mem_univ j), hsrow⟩, fun i j hj => ?_⟩
  apply hsT
  simp [hT', hj]

theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (Ps : Profile n m) (q : stdSimplex ℝ (Fin m))
    (hsupp : ∀ i j, j ∉ crit (Ps i) q.1 → (Ps i).1 j = 0)
    (hcore : IsCoreFairShare Ps q) : IsNashOutcome Ps q.1 := by
  classical
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  -- core fair share implies the Hall condition on critical sets
  have hH : ∀ G : Finset (Fin n), (G.card : ℝ) / (n : ℝ) ≤
      ∑ j ∈ G.biUnion (fun i => crit (Ps i) q.1), q.1 j := by
    intro G
    by_contra hlt
    push_neg at hlt
    set T := G.biUnion (fun i => crit (Ps i) q.1) with hT
    set x := ∑ j ∈ T, q.1 j with hx
    set c := (G.card : ℝ) / (n : ℝ) with hc
    have hx0 : 0 ≤ x := Finset.sum_nonneg (fun j _ => q.2.1 j)
    have hGne : G.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      have : c = 0 := by rw [hc, h]; simp
      linarith
    have hcpos : 0 < c := by linarith
    set lam := 1 - x / c with hlam
    have hlam0 : 0 < lam := by
      rw [hlam, sub_pos, div_lt_one hcpos]; exact hlt
    let f : Fin m → ℝ := fun j => (x / c) * (if j ∈ T then q.1 j / x else 0) + lam / m
    have hfmem : f ∈ stdSimplex ℝ (Fin m) := by
      refine ⟨fun j => ?_, ?_⟩
      · simp only [f]
        have h1 : 0 ≤ x / c := div_nonneg hx0 hcpos.le
        have h2 : 0 ≤ (if j ∈ T then q.1 j / x else 0) := by
          split_ifs
          · exact div_nonneg (q.2.1 j) hx0
          · exact le_refl _
        have h3 : 0 ≤ lam / m := div_nonneg hlam0.le hm.le
        nlinarith
      · simp only [f]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter,
          ← Finset.sum_div, ← hx]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have e1 : x / c * (x / x) = x / c := by
          rcases eq_or_ne x 0 with h | h
          · rw [h]; simp
          · rw [div_self h, mul_one]
        rw [e1, hlam]
        field_simp
        ring
    let q' : stdSimplex ℝ (Fin m) := ⟨f, hfmem⟩
    apply hcore G hGne
    refine ⟨q', fun q'' i hi => ?_⟩
    apply nc_lt_leontief
    intro k hk
    have hkc : k ∈ crit (Ps i) q.1 := by
      by_contra hc'
      rw [hsupp i k hc'] at hk; exact lt_irrefl _ hk
    obtain ⟨_, he⟩ := (nc_mem_crit _ _ k).mp hkc
    have hkT : k ∈ T := Finset.mem_biUnion.mpr ⟨i, hi, hkc⟩
    -- c * q'_k = q_k + c * lam / m
    have hcq : c * f k = q.1 k + c * (lam / m) := by
      simp only [f, if_pos hkT]
      rcases eq_or_ne x 0 with h | h
      · have hqk : q.1 k = 0 := by
          have := Finset.single_le_sum (fun j _ => q.2.1 j) hkT
          rw [← hx, h] at this
          exact le_antisymm this (q.2.1 k)
        rw [h, hqk]; ring
      · field_simp
    have hw : q.1 k < c * f k + (1 - c) * q''.1 k := by
      have h1 : 0 ≤ (1 - c) * q''.1 k := by
        apply mul_nonneg _ (q''.2.1 k)
        have : (G.card : ℝ) ≤ n := by
          have := Finset.card_le_univ G; rw [Fintype.card_fin] at this; exact_mod_cast this
        rw [hc, sub_nonneg, div_le_one hn]; exact this
      have h2 : 0 < c * (lam / m) := by positivity
      linarith
    rw [← he]
    exact div_lt_div_of_pos_right hw hk
  obtain ⟨s, hs, hsT⟩ := nc_frac_hall (fun i => crit (Ps i) q.1) q.1 q.2 hH
  exact nc_decomp_nash Ps q s hs hsT
