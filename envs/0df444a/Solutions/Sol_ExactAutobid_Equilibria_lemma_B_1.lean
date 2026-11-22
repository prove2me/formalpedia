-- Prove2me | solution 1 for ExactAutobid.Equilibria.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T09:02:43.453884+00:00
-- url     : https://prove2.me/submissions/56788932-41aa-46a1-b324-e241b4b4b14c

import Mathlib

open scoped BigOperators

private def cumSum {m : ℕ} (k : Fin m → ℕ) (μ : (j : Fin m) → Fin (k j) → ℝ)
    (j : Fin m) (n : ℕ) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c : Fin (k j) => (c : ℕ) < n), μ j c

private lemma cumSum_zero {m : ℕ} (k : Fin m → ℕ) (μ : (j : Fin m) → Fin (k j) → ℝ) (j : Fin m) :
    cumSum k μ j 0 = 0 := by
  simp [cumSum]

private lemma cumSum_top {m : ℕ} (k : Fin m → ℕ) (μ : (j : Fin m) → Fin (k j) → ℝ) (j : Fin m)
    (hμ1 : ∑ c, μ j c = 1) : cumSum k μ j (k j) = 1 := by
  have h : Finset.filter (fun c : Fin (k j) => (c : ℕ) < k j) Finset.univ = Finset.univ := by
    ext c; simp
  simp [cumSum, hμ1]

private lemma cumSum_mono {m : ℕ} (k : Fin m → ℕ) (μ : (j : Fin m) → Fin (k j) → ℝ)
    (hμ0 : ∀ j c, 0 ≤ μ j c) (j : Fin m) : Monotone (cumSum k μ j) := by
  intro a b hab
  simp only [cumSum]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun c hc => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢; omega)
    (fun c _ _ => hμ0 j c)

private lemma cumSum_nonneg {m : ℕ} (k : Fin m → ℕ) (μ : (j : Fin m) → Fin (k j) → ℝ)
    (hμ0 : ∀ j c, 0 ≤ μ j c) (j : Fin m) (n : ℕ) : 0 ≤ cumSum k μ j n := by
  simp only [cumSum]
  exact Finset.sum_nonneg (fun c _ => hμ0 j c)

private lemma cumSum_step {m : ℕ} (k : Fin m → ℕ) (μ : (j : Fin m) → Fin (k j) → ℝ)
    (j : Fin m) (c : Fin (k j)) :
    cumSum k μ j ((c : ℕ) + 1) - cumSum k μ j (c : ℕ) = μ j c := by
  have hf : Finset.filter (fun c' : Fin (k j) => (c' : ℕ) < (c : ℕ) + 1) Finset.univ
      = insert c (Finset.filter (fun c' : Fin (k j) => (c' : ℕ) < (c : ℕ)) Finset.univ) := by
    ext c'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
      · exact Or.inr h'
      · exact Or.inl (Fin.ext h')
    · rintro (rfl | h)
      · simp
      · omega
  simp only [cumSum]
  rw [hf, Finset.sum_insert (by simp), add_sub_cancel_right]

private lemma cumSum_const {m : ℕ} (k : Fin m → ℕ) (μ : (j : Fin m) → Fin (k j) → ℝ)
    (j : Fin m) {n : ℕ} (hn : k j ≤ n) : cumSum k μ j n = cumSum k μ j (k j) := by
  simp only [cumSum]
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

private lemma cumSum_le_one {m : ℕ} (k : Fin m → ℕ) (μ : (j : Fin m) → Fin (k j) → ℝ)
    (hμ0 : ∀ j c, 0 ≤ μ j c) (hμ1 : ∀ j, ∑ c, μ j c = 1) (j : Fin m) (n : ℕ) :
    cumSum k μ j n ≤ 1 := by
  by_cases hn : n ≤ k j
  · rw [← cumSum_top k μ j (hμ1 j)]
    exact cumSum_mono k μ hμ0 j hn
  · rw [cumSum_const k μ j (by omega), cumSum_top k μ j (hμ1 j)]

private noncomputable def breakpoints {m : ℕ} (k : Fin m → ℕ)
    (μ : (j : Fin m) → Fin (k j) → ℝ) : Finset ℝ :=
  insert 0 (insert 1 (Finset.univ.biUnion fun j : Fin m => (Finset.Ico 1 (k j)).image (cumSum k μ j)))

private lemma mem_breakpoints {m : ℕ} (k : Fin m → ℕ) (μ : (j : Fin m) → Fin (k j) → ℝ)
    (hμ1 : ∀ j, ∑ c, μ j c = 1) (j : Fin m) {n : ℕ} (hn : n ≤ k j) :
    cumSum k μ j n ∈ breakpoints k μ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · rw [cumSum_zero]
    exact Finset.mem_insert.mpr (Or.inl rfl)
  · rcases eq_or_lt_of_le hn with heq | hlt
    · rw [heq, cumSum_top k μ j (hμ1 j)]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))
    · refine Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr ?_)))
      refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, ?_⟩
      exact Finset.mem_image.mpr ⟨n, by simp [Finset.mem_Ico]; omega, rfl⟩

private lemma breakpoints_nonneg {m : ℕ} (k : Fin m → ℕ) (μ : (j : Fin m) → Fin (k j) → ℝ)
    (hμ0 : ∀ j c, 0 ≤ μ j c) :
    ∀ x ∈ breakpoints k μ, 0 ≤ x := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · norm_num
  rcases Finset.mem_insert.mp hx with rfl | hx
  · norm_num
  rw [Finset.mem_biUnion] at hx
  obtain ⟨j, -, hx⟩ := hx
  rw [Finset.mem_image] at hx
  obtain ⟨n, -, hn⟩ := hx
  rw [← hn]
  exact cumSum_nonneg k μ hμ0 j n

private lemma breakpoints_le_one {m : ℕ} (k : Fin m → ℕ) (μ : (j : Fin m) → Fin (k j) → ℝ)
    (hμ0 : ∀ j c, 0 ≤ μ j c) (hμ1 : ∀ j, ∑ c, μ j c = 1) :
    ∀ x ∈ breakpoints k μ, x ≤ 1 := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · norm_num
  rcases Finset.mem_insert.mp hx with rfl | hx
  · norm_num
  rw [Finset.mem_biUnion] at hx
  obtain ⟨j, -, hx⟩ := hx
  rw [Finset.mem_image] at hx
  obtain ⟨n, -, hn⟩ := hx
  rw [← hn]
  exact cumSum_le_one k μ hμ0 hμ1 j n

private lemma breakpoints_card {m : ℕ} (k : Fin m → ℕ) (μ : (j : Fin m) → Fin (k j) → ℝ) :
    (breakpoints k μ).card ≤ 2 + ∑ j, (k j - 1) := by
  have h2 : (Finset.univ.biUnion fun j : Fin m => (Finset.Ico 1 (k j)).image (cumSum k μ j)).card
      ≤ ∑ j, (k j - 1) := by
    refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum (fun j _ => ?_))
    refine le_trans Finset.card_image_le ?_
    simp [Nat.card_Ico]
  have h1 : (breakpoints k μ).card
      ≤ 2 + (Finset.univ.biUnion fun j : Fin m =>
          (Finset.Ico 1 (k j)).image (cumSum k μ j)).card := by
    simp only [breakpoints]
    have a := Finset.card_insert_le (0:ℝ)
      (insert 1 (Finset.univ.biUnion fun j : Fin m => (Finset.Ico 1 (k j)).image (cumSum k μ j)))
    have b := Finset.card_insert_le (1:ℝ)
      (Finset.univ.biUnion fun j : Fin m => (Finset.Ico 1 (k j)).image (cumSum k μ j))
    omega
  omega

private lemma quantile_coupling {m : ℕ} (k : Fin m → ℕ) (hk : ∀ j, 1 ≤ k j)
    (μ : (j : Fin m) → Fin (k j) → ℝ) (hμ0 : ∀ j c, 0 ≤ μ j c) (hμ1 : ∀ j, ∑ c, μ j c = 1) :
    ∃ (s : ℕ) (t : Fin s → (j : Fin m) → Fin (k j)) (w : Fin s → ℝ),
      s ≤ 1 + ∑ j, (k j - 1) ∧ (∀ l, 0 ≤ w l) ∧ ∑ l, w l = 1 ∧
      (∀ j c, ∑ l ∈ Finset.univ.filter (fun l => t l j = c), w l = μ j c) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨1, fun _ j => Fin.elim0 j, fun _ => 1, by simp, fun _ => by norm_num, by simp,
      fun j => Fin.elim0 j⟩
  let T := breakpoints k μ
  have h0T : (0:ℝ) ∈ T := Finset.mem_insert.mpr (Or.inl rfl)
  have h1T : (1:ℝ) ∈ T := Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))
  have hTnn : ∀ x ∈ T, 0 ≤ x := fun x hx => breakpoints_nonneg k μ hμ0 x hx
  have hTle : ∀ x ∈ T, x ≤ 1 := fun x hx => breakpoints_le_one k μ hμ0 hμ1 x hx
  have h2T : 2 ≤ T.card := by
    have hsub : ({0, 1} : Finset ℝ) ⊆ T := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact h0T
      · rw [Finset.mem_singleton] at hx; subst hx; exact h1T
    have hc : ({0, 1} : Finset ℝ).card = 2 := by simp
    have h := Finset.card_le_card hsub
    rw [hc] at h
    exact h
  let τ : ℕ → ℝ := fun n => if h : n < T.card then (T.orderEmbOfFin rfl) ⟨n, h⟩ else 0
  have hτ : ∀ n (h : n < T.card), τ n = (T.orderEmbOfFin rfl) ⟨n, h⟩ := by
    intro n h; simp [τ, dif_pos h]
  have hτ_mem : ∀ n (h : n < T.card), τ n ∈ T := by
    intro n h
    rw [hτ n h]
    exact Finset.orderEmbOfFin_mem T rfl ⟨n, h⟩
  have hτ_strict : ∀ {a b : ℕ} (ha : a < T.card) (hb : b < T.card), a < b → τ a < τ b := by
    intro a b ha hb hab
    rw [hτ a ha, hτ b hb]
    exact (T.orderEmbOfFin rfl).strictMono (by simp [hab])
  have hτ0 : τ 0 = 0 := by
    have h0c : 0 < T.card := by omega
    rw [hτ 0 h0c, Finset.orderEmbOfFin_zero (s := T) (k := T.card) rfl h0c]
    exact le_antisymm (Finset.min'_le T 0 h0T)
      (Finset.le_min' T (Finset.card_pos.mp h0c) 0 (fun y hy => hTnn y hy))
  have hτs : τ (T.card - 1) = 1 := by
    have h0c : 0 < T.card := by omega
    rw [hτ (T.card - 1) (by omega), Finset.orderEmbOfFin_last (s := T) (k := T.card) rfl h0c]
    exact le_antisymm (Finset.max'_le T (Finset.card_pos.mp h0c) 1 (fun y hy => hTle y hy))
      (Finset.le_max' T 1 h1T)
  have hτnn : ∀ n, n < T.card → 0 ≤ τ n := fun n h => hTnn _ (hτ_mem n h)
  have hτle : ∀ n, n < T.card → τ n ≤ 1 := fun n h => hTle _ (hτ_mem n h)
  have hτlt : ∀ n, n < T.card - 1 → τ n < 1 := by
    intro n h
    have hlt := hτ_strict (a := n) (b := T.card - 1) (by omega) (by omega) h
    rwa [hτs] at hlt
  have hne : ∀ (l : Fin (T.card - 1)) (j : Fin m),
      (Finset.univ.filter (fun c : Fin (k j) => cumSum k μ j (c:ℕ) ≤ τ (l:ℕ))).Nonempty := by
    intro l j
    exact ⟨⟨0, by have := hk j; omega⟩, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [cumSum_zero]
      exact hτnn (l:ℕ) (by omega)⟩
  let tt : Fin (T.card - 1) → (j : Fin m) → Fin (k j) := fun l j =>
    (Finset.univ.filter (fun c : Fin (k j) => cumSum k μ j (c:ℕ) ≤ τ (l:ℕ))).max' (hne l j)
  let wf : Fin (T.card - 1) → ℝ := fun l => τ ((l:ℕ) + 1) - τ (l:ℕ)
  have htt_mem : ∀ (l : Fin (T.card - 1)) (j : Fin m),
      cumSum k μ j ((tt l j : ℕ)) ≤ τ (l:ℕ) := by
    intro l j
    have := Finset.max'_mem (Finset.univ.filter
      (fun c : Fin (k j) => cumSum k μ j (c:ℕ) ≤ τ (l:ℕ))) (hne l j)
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, tt] using this
  have htt_lt : ∀ (l : Fin (T.card - 1)) (j : Fin m),
      τ (l:ℕ) < cumSum k μ j ((tt l j : ℕ) + 1) := by
    intro l j
    set c : Fin (k j) := tt l j with hc
    by_cases hlast : (c:ℕ) + 1 = k j
    · rw [hlast, cumSum_top k μ j (hμ1 j)]
      exact hτlt (l:ℕ) (by omega)
    · have hlt : (c:ℕ) + 1 < k j := by
        have := c.isLt; omega
      by_contra hcon
      push_neg at hcon
      have hmem : (⟨(c:ℕ)+1, hlt⟩ : Fin (k j)) ∈ Finset.univ.filter
          (fun c' : Fin (k j) => cumSum k μ j (c':ℕ) ≤ τ (l:ℕ)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hcon
      have hmax : (Finset.univ.filter
          (fun c' : Fin (k j) => cumSum k μ j (c':ℕ) ≤ τ (l:ℕ))).max' (hne l j) = c := by
        rw [hc]
      have hle := Finset.le_max' _ (⟨(c:ℕ)+1, hlt⟩ : Fin (k j)) hmem
      rw [hmax] at hle
      simp only [Fin.le_def] at hle
      omega
  have htt_eq : ∀ (l : Fin (T.card - 1)) (j : Fin m) (c : Fin (k j)),
      tt l j = c ↔ (cumSum k μ j (c:ℕ) ≤ τ (l:ℕ) ∧ τ (l:ℕ) < cumSum k μ j ((c:ℕ)+1)) := by
    intro l j c
    constructor
    · intro h
      rw [← h]
      exact ⟨htt_mem l j, htt_lt l j⟩
    · rintro ⟨h1, h2⟩
      by_contra hne'
      have hle : c ≤ tt l j := by
        refine Finset.le_max' _ c ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h1
      have hlt : c < tt l j := lt_of_le_of_ne hle (fun hEq => hne' hEq.symm)
      have hsucc : (c:ℕ) + 1 ≤ (tt l j : ℕ) := by simpa using hlt
      have hmono := cumSum_mono k μ hμ0 j hsucc
      have hmem := htt_mem l j
      linarith
  have htail : ∀ (a : ℝ) (ha : a ∈ T),
      ∑ l : Fin (T.card - 1), wf l * (if a ≤ τ (l:ℕ) then 1 else 0) = 1 - a := by
    intro a ha
    have h0c : 0 < T.card := by omega
    let ia : Fin T.card := (T.orderIsoOfFin rfl).symm ⟨a, ha⟩
    have hia : τ (ia:ℕ) = a := by
      rw [hτ (ia:ℕ) ia.isLt, ← Finset.coe_orderIsoOfFin_apply]
      simp [ia]
    have his : (ia:ℕ) ≤ T.card - 1 := by
      have := ia.isLt
      omega
    have hiff : ∀ l : Fin (T.card - 1), (a ≤ τ (l:ℕ)) ↔ ((ia:ℕ) ≤ (l:ℕ)) := by
      intro l
      have hl : (l:ℕ) < T.card := by
        have := l.isLt; omega
      have hkey : τ (l:ℕ) = ↑((T.orderIsoOfFin rfl) ⟨(l:ℕ), hl⟩) := by
        rw [hτ (l:ℕ) hl, ← Finset.coe_orderIsoOfFin_apply]
      have hkeya : a = ↑((T.orderIsoOfFin rfl) ia) := by
        rw [← hia, hτ (ia:ℕ) ia.isLt, ← Finset.coe_orderIsoOfFin_apply]
      rw [hkeya, hkey]
      constructor
      · intro h
        exact Fin.le_def.mp ((T.orderIsoOfFin rfl).le_iff_le.mp h)
      · intro h
        exact (T.orderIsoOfFin rfl).le_iff_le.mpr (Fin.le_def.mpr h)
    have hstep : ∀ l : Fin (T.card - 1), wf l * (if a ≤ τ (l:ℕ) then 1 else 0)
        = if (ia:ℕ) ≤ (l:ℕ) then (τ ((l:ℕ)+1) - τ (l:ℕ)) else 0 := by
      intro l
      simp only [wf]
      by_cases h : (ia:ℕ) ≤ (l:ℕ)
      · have h' : a ≤ τ (l:ℕ) := (hiff l).mpr h
        simp [h, h']
      · have h' : ¬ (a ≤ τ (l:ℕ)) := fun hh => h ((hiff l).mp hh)
        simp [h, h']
    rw [Finset.sum_congr rfl (fun l _ => hstep l)]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => if (ia:ℕ) ≤ i then (τ (i+1) - τ i) else 0) (T.card - 1)]
    rw [← Finset.sum_filter]
    have hIco : (Finset.range (T.card - 1)).filter (fun i => (ia:ℕ) ≤ i)
        = Finset.Ico (ia:ℕ) (T.card - 1) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [hIco, Finset.sum_Ico_eq_sub _ his]
    rw [Finset.sum_range_sub, Finset.sum_range_sub, hτs, hia]
    ring
  have hw0 : ∀ l : Fin (T.card - 1), 0 ≤ wf l := by
    intro l
    simp only [wf]
    have h := hτ_strict (a := (l:ℕ)) (b := (l:ℕ)+1) (by omega) (by omega) (by omega)
    linarith
  have hsum1 : ∑ l : Fin (T.card - 1), wf l = 1 := by
    simp only [wf]
    rw [Fin.sum_univ_eq_sum_range (fun i => τ (i+1) - τ i) (T.card - 1)]
    rw [Finset.sum_range_sub, hτs, hτ0]
    ring
  have hmarg : ∀ (j : Fin m) (c : Fin (k j)),
      ∑ l ∈ Finset.univ.filter (fun l : Fin (T.card - 1) => tt l j = c), wf l = μ j c := by
    intro j c
    have hind : ∀ l : Fin (T.card - 1),
        (if tt l j = c then (1:ℝ) else 0)
          = (if cumSum k μ j (c:ℕ) ≤ τ (l:ℕ) then 1 else 0)
            - (if cumSum k μ j ((c:ℕ)+1) ≤ τ (l:ℕ) then 1 else 0) := by
      intro l
      by_cases h2 : cumSum k μ j ((c:ℕ)+1) ≤ τ (l:ℕ)
      · have h3 : cumSum k μ j (c:ℕ) ≤ τ (l:ℕ) :=
          le_trans (cumSum_mono k μ hμ0 j (by omega)) h2
        have h4 : ¬ (tt l j = c) := by
          intro hh
          have hh' := (htt_eq l j c).mp hh
          linarith [hh'.2]
        simp [h2, h3, h4]
      · by_cases h3 : cumSum k μ j (c:ℕ) ≤ τ (l:ℕ)
        · have h4 : tt l j = c := (htt_eq l j c).mpr ⟨h3, lt_of_not_ge h2⟩
          simp [h2, h3, h4]
        · have h4 : ¬ (tt l j = c) := by
            intro hh
            exact h3 ((htt_eq l j c).mp hh).1
          simp [h2, h3, h4]
    calc ∑ l ∈ Finset.univ.filter (fun l : Fin (T.card - 1) => tt l j = c), wf l
        = ∑ l : Fin (T.card - 1), wf l * (if tt l j = c then 1 else 0) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          by_cases h : tt l j = c <;> simp [h]
      _ = ∑ l : Fin (T.card - 1), (wf l * (if cumSum k μ j (c:ℕ) ≤ τ (l:ℕ) then 1 else 0)
            - wf l * (if cumSum k μ j ((c:ℕ)+1) ≤ τ (l:ℕ) then 1 else 0)) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hind l, mul_sub]
      _ = (∑ l : Fin (T.card - 1), wf l * (if cumSum k μ j (c:ℕ) ≤ τ (l:ℕ) then 1 else 0))
            - (∑ l : Fin (T.card - 1),
                wf l * (if cumSum k μ j ((c:ℕ)+1) ≤ τ (l:ℕ) then 1 else 0)) := by
          rw [Finset.sum_sub_distrib]
      _ = (1 - cumSum k μ j (c:ℕ)) - (1 - cumSum k μ j ((c:ℕ)+1)) := by
          rw [htail _ (mem_breakpoints k μ hμ1 j (by omega)),
            htail _ (mem_breakpoints k μ hμ1 j (by omega))]
      _ = μ j c := by
          have := cumSum_step k μ j c
          linarith
  refine ⟨T.card - 1, tt, wf, ?_, hw0, hsum1, hmarg⟩
  have hTcard : T.card ≤ 2 + ∑ j, (k j - 1) := breakpoints_card k μ
  omega

theorem solution {O ι : Type} (valid : O → Prop) (pay : ι → O → ℝ) (m : ℕ) (k : Fin m → ℕ)
    (hk : ∀ j, 1 ≤ k j) (comb : ((j : Fin m) → Fin (k j)) → O) (hcomb : ∀ c, valid (comb c))
    (f : ι → (j : Fin m) → Fin (k j) → ℝ) (hpay : ∀ i c, pay i (comb c) = ∑ j, f i j (c j))
    (μ : (j : Fin m) → Fin (k j) → ℝ) (hμ0 : ∀ j c, 0 ≤ μ j c) (hμ1 : ∀ j, ∑ c, μ j c = 1) :
    ∃ (s : ℕ) (t : Fin s → (j : Fin m) → Fin (k j)) (w : Fin s → ℝ),
      s ≤ 1 + ∑ j, (k j - 1) ∧ (∀ l, 0 ≤ w l) ∧ ∑ l, w l = 1 ∧
      (∀ j c, ∑ l ∈ Finset.univ.filter (fun l => t l j = c), w l = μ j c) ∧
      (∀ l, valid (comb (t l))) ∧
      ∀ i, ∑ l, w l * pay i (comb (t l)) = ∑ j, ∑ c, μ j c * f i j c := by
  classical
  obtain ⟨s, t, w, hb, hw0, hw1, hmarg⟩ := quantile_coupling k hk μ hμ0 hμ1
  refine ⟨s, t, w, hb, hw0, hw1, hmarg, fun l => hcomb _, ?_⟩
  intro i
  have hfib : ∀ j : Fin m, ∑ l : Fin s, w l * f i j (t l j)
      = ∑ c, (∑ l ∈ Finset.univ.filter (fun l => t l j = c), w l) * f i j c := by
    intro j
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin s)) (fun l => t l j)
      (fun l => w l * f i j (t l j))]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hstep : ∀ l ∈ Finset.univ.filter (fun l => t l j = c),
        w l * f i j (t l j) = w l * f i j c := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      rw [hl]
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul]
  calc ∑ l, w l * pay i (comb (t l))
      = ∑ l, w l * (∑ j, f i j (t l j)) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hpay]
    _ = ∑ j, ∑ l, w l * f i j (t l j) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
    _ = ∑ j, ∑ c, μ j c * f i j c := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [hfib j]
          exact Finset.sum_congr rfl (fun c _ => by rw [hmarg j c])
