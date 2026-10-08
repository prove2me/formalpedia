-- Prove2me | solution 1 for FedergruenZhengRQ.OPT.lemma2_optimal_order_size
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T11:55:07.578901+00:00
-- url     : https://prove2.me/submissions/a9ecafb6-1902-4571-8016-b546fa97e7e0

import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model



namespace FedergruenZhengRQ.OPT

lemma fz_left (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t)
    (t s : ℤ) (hts : t ≤ s) (hs : s ≤ y₁) : G s ≤ G t := by
  obtain ⟨m, hA, hM⟩ := hG
  by_cases hsm : s ≤ m
  · exact hA (Set.mem_Iic.2 (le_trans hts hsm)) (Set.mem_Iic.2 hsm) hts
  · rw [not_le] at hsm
    have : G s ≤ G y₁ := hM (Set.mem_Ici.2 hsm.le) (Set.mem_Ici.2 (by omega)) hs
    linarith [hy₁ t]

lemma fz_right (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t)
    (t s : ℤ) (hts : s ≤ t) (hs : y₁ ≤ s) : G s ≤ G t := by
  obtain ⟨m, hA, hM⟩ := hG
  by_cases hsm : m ≤ s
  · exact hM (Set.mem_Ici.2 hsm) (Set.mem_Ici.2 (le_trans hsm hts)) hts
  · rw [not_le] at hsm
    have : G s ≤ G y₁ := hA (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 hsm.le) hs
    linarith [hy₁ t]

/-- invariant of the window -/
lemma fz_inv (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t) (n : ℕ) :
    (window G y₁ n).1 ≤ y₁ ∧ y₁ ≤ (window G y₁ n).2 ∧
    (window G y₁ n).2 - (window G y₁ n).1 = n ∧
    ∀ x, (window G y₁ n).1 ≤ x → x ≤ (window G y₁ n).2 →
      G x ≤ G ((window G y₁ n).1 - 1) ∧ G x ≤ G ((window G y₁ n).2 + 1) := by
  induction n with
  | zero =>
    simp only [window]
    refine ⟨le_rfl, le_rfl, by simp, fun x h1 h2 => ?_⟩
    have : x = y₁ := le_antisymm h2 h1
    subst this; exact ⟨hy₁ _, hy₁ _⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    set a := (window G y₁ n).1 with ha
    set b := (window G y₁ n).2 with hb
    have hw : window G y₁ (n+1) = if G (a - 1) ≤ G (b + 1) then (a - 1, b) else (a, b + 1) := by
      simp only [window, ha, hb]
    rw [hw]
    split_ifs with hc
    · simp only
      refine ⟨by omega, h2, by push_cast; omega, fun x hx1 hx2 => ?_⟩
      have hl : G (a - 1) ≤ G (a - 1 - 1) := fz_left G hG y₁ hy₁ _ _ (by omega) (by omega)
      by_cases hxa : x = a - 1
      · subst hxa; exact ⟨hl, hc⟩
      · have := h4 x (by omega) hx2
        exact ⟨le_trans this.1 hl, this.2⟩
    · simp only
      rw [not_le] at hc
      refine ⟨h1, by omega, by push_cast; omega, fun x hx1 hx2 => ?_⟩
      have hr : G (b + 1) ≤ G (b + 1 + 1) := fz_right G hG y₁ hy₁ _ _ (by omega) (by omega)
      by_cases hxb : x = b + 1
      · subst hxb; exact ⟨hc.le, hr⟩
      · have := h4 x hx1 (by omega)
        exact ⟨this.1, le_trans this.2 hr⟩

lemma fz_window_succ (G : ℤ → ℝ) (y₁ : ℤ) (n : ℕ) :
    window G y₁ (n+1) = if G ((window G y₁ n).1 - 1) ≤ G ((window G y₁ n).2 + 1) then
      ((window G y₁ n).1 - 1, (window G y₁ n).2) else ((window G y₁ n).1, (window G y₁ n).2 + 1) := by
  rfl

lemma fz_y_succ (G : ℤ → ℝ) (y₁ : ℤ) (n : ℕ) :
    y G y₁ (n+2) = if G ((window G y₁ n).1 - 1) ≤ G ((window G y₁ n).2 + 1) then
      (window G y₁ n).1 - 1 else (window G y₁ n).2 + 1 := by
  simp [y, L, R]

/-- the image/sum of the first n+1 points -/
lemma fz_image (G : ℤ → ℝ) (y₁ : ℤ) (n : ℕ) :
    (Finset.Icc 1 (n+1)).image (y G y₁) = Finset.Icc (window G y₁ n).1 (window G y₁ n).2 ∧
    ∑ i ∈ Finset.Icc 1 (n+1), G (y G y₁ i) = ∑ t ∈ Finset.Icc (window G y₁ n).1 (window G y₁ n).2, G t := by
  induction n with
  | zero => simp [window, y]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hI : Finset.Icc 1 (n+1+1) = insert (n+2) (Finset.Icc 1 (n+1)) := by
      ext i; simp; omega
    have hn : (n+2) ∉ Finset.Icc 1 (n+1) := by simp
    rw [hI, Finset.image_insert, Finset.sum_insert hn, h1, h2, fz_y_succ, fz_window_succ]
    have hle : (window G y₁ n).1 ≤ (window G y₁ n).2 + 1 := by
      have := Finset.mem_image_of_mem (y G y₁) (show 1 ∈ Finset.Icc 1 (n+1) by simp)
      rw [h1] at this; simp at this; omega
    split_ifs with hc
    · have e : Finset.Icc ((window G y₁ n).1 - 1) (window G y₁ n).2 =
          insert ((window G y₁ n).1 - 1) (Finset.Icc (window G y₁ n).1 (window G y₁ n).2) := by
        ext t; simp; omega
      rw [e, Finset.sum_insert (by simp)]
      exact ⟨rfl, rfl⟩
    · have e : Finset.Icc (window G y₁ n).1 ((window G y₁ n).2 + 1) =
          insert ((window G y₁ n).2 + 1) (Finset.Icc (window G y₁ n).1 (window G y₁ n).2) := by
        ext t; simp; omega
      rw [e, Finset.sum_insert (by simp)]
      exact ⟨rfl, rfl⟩

lemma fz_exchange (G : ℤ → ℝ) (W T : Finset ℤ) (c : ℝ) (hcard : T.card = W.card)
    (hW : ∀ x ∈ W, G x ≤ c) (hT : ∀ t, t ∉ W → c ≤ G t) :
    ∑ x ∈ W, G x ≤ ∑ t ∈ T, G t := by
  classical
  have e1 := Finset.sum_sdiff (s₁ := W ∩ T) (s₂ := W) (f := G) Finset.inter_subset_left
  have e2 := Finset.sum_sdiff (s₁ := W ∩ T) (s₂ := T) (f := G) Finset.inter_subset_right
  have hc1 : (W \ (W ∩ T)).card = (T \ (W ∩ T)).card := by
    rw [Finset.card_sdiff_of_subset Finset.inter_subset_left,
      Finset.card_sdiff_of_subset Finset.inter_subset_right, hcard]
  have s1 : ∑ x ∈ W \ (W ∩ T), G x ≤ ∑ x ∈ W \ (W ∩ T), c :=
    Finset.sum_le_sum fun x hx => hW x (Finset.mem_sdiff.1 hx).1
  have s2 : ∑ x ∈ T \ (W ∩ T), c ≤ ∑ x ∈ T \ (W ∩ T), G x :=
    Finset.sum_le_sum fun x hx => hT x (by
      intro hxW; exact (Finset.mem_sdiff.1 hx).2 (Finset.mem_inter.2 ⟨hxW, (Finset.mem_sdiff.1 hx).1⟩))
  simp only [Finset.sum_const, nsmul_eq_mul] at s1 s2
  rw [hc1] at s1
  linarith

lemma fz_LR (G : ℤ → ℝ) (y₁ : ℤ) (n : ℕ) :
    L G y₁ (n+1) = (window G y₁ n).1 ∧ R G y₁ (n+1) = (window G y₁ n).2 := by
  simp [L, R]

theorem window_contiguous_smallest_core (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ)
    (hy₁ : ∀ t, G y₁ ≤ G t) (Q : ℕ) (hQ : 1 ≤ Q) :
    (Finset.Icc 1 Q).image (y G y₁) = Finset.Icc (L G y₁ Q) (R G y₁ Q) ∧
    R G y₁ Q - L G y₁ Q + 1 = (Q : ℤ) ∧
    (∀ i ∈ Finset.Icc 1 Q, ∀ t : ℤ, t ∉ Finset.Icc (L G y₁ Q) (R G y₁ Q) → G (y G y₁ i) ≤ G t) ∧
    (∀ T : Finset ℤ, T.card = Q → ∑ i ∈ Finset.Icc 1 Q, G (y G y₁ i) ≤ ∑ t ∈ T, G t) := by
  obtain ⟨n, rfl⟩ : ∃ n, Q = n + 1 := ⟨Q - 1, by omega⟩
  obtain ⟨hL, hR⟩ := fz_LR G y₁ n
  rw [hL, hR]
  obtain ⟨h1, h2⟩ := fz_image G y₁ n
  obtain ⟨i1, i2, i3, i4⟩ := fz_inv G hG y₁ hy₁ n
  set a := (window G y₁ n).1
  set b := (window G y₁ n).2
  have hout : ∀ x, a ≤ x → x ≤ b → ∀ t : ℤ, t ∉ Finset.Icc a b → G x ≤ G t := by
    intro x hx1 hx2 t ht
    simp only [Finset.mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · exact le_trans (i4 x hx1 hx2).1 (fz_left G hG y₁ hy₁ t (a-1) (by omega) (by omega))
    · exact le_trans (i4 x hx1 hx2).2 (fz_right G hG y₁ hy₁ t (b+1) (by omega) (by omega))
  refine ⟨h1, by push_cast; omega, ?_, ?_⟩
  · intro i hi t ht
    have hm := Finset.mem_image_of_mem (y G y₁) hi
    rw [h1, Finset.mem_Icc] at hm
    exact hout _ hm.1 hm.2 t ht
  · intro T hT
    rw [h2]
    apply fz_exchange G _ T (min (G (a-1)) (G (b+1)))
    · rw [hT, Int.card_Icc]; omega
    · intro x hx; rw [Finset.mem_Icc] at hx
      exact le_min (i4 x hx.1 hx.2).1 (i4 x hx.1 hx.2).2
    · intro t ht
      simp only [Finset.mem_Icc, not_and_or, not_le] at ht
      rcases ht with ht | ht
      · exact le_trans (min_le_left _ _) (fz_left G hG y₁ hy₁ t (a-1) (by omega) (by omega))
      · exact le_trans (min_le_right _ _) (fz_right G hG y₁ hy₁ t (b+1) (by omega) (by omega))

lemma fz_cost_window (κ : ℝ) (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ)
    (hy₁ : ∀ t, G y₁ ≤ G t) (Q : ℕ) (hQ : 1 ≤ Q) :
    cost κ G (L G y₁ Q - 1) Q = Cstar κ G y₁ Q ∧
    ∀ r : ℤ, cost κ G (L G y₁ Q - 1) Q ≤ cost κ G r Q := by
  obtain ⟨h1, h2, h3, h4⟩ := window_contiguous_smallest_core G hG y₁ hy₁ Q hQ
  have hsum : ∑ t ∈ Finset.Ioc (L G y₁ Q - 1) (L G y₁ Q - 1 + Q), G t
      = ∑ i ∈ Finset.Icc 1 Q, G (y G y₁ i) := by
    have hinj : Set.InjOn (y G y₁) (Finset.Icc 1 Q) := by
      have hc := congrArg Finset.card h1
      rw [Int.card_Icc] at hc
      apply Finset.injOn_of_card_image_eq
      rw [hc]; simp; omega
    rw [← Finset.sum_image (f := G) hinj, h1]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext t; simp; omega
  have hQpos : (0:ℝ) < Q := by exact_mod_cast hQ
  have e : cost κ G (L G y₁ Q - 1) Q = Cstar κ G y₁ Q := by
    simp only [cost, Cstar]; rw [hsum]
  refine ⟨e, fun r => ?_⟩
  rw [e]
  simp only [cost, Cstar]
  apply div_le_div_of_nonneg_right _ hQpos.le
  have := h4 (Finset.Ioc r (r + Q)) (by simp)
  linarith

theorem corollary1_core (κ : ℝ) (hκ : 0 < κ) (G : ℤ → ℝ)
    (hG : NegUnimodal G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t)
    (Q : ℕ) (hQ : 1 ≤ Q) :
    (L G y₁ (Q + 1) = L G y₁ Q ∨ L G y₁ (Q + 1) = L G y₁ Q - 1) ∧
    (L G y₁ Q - 1) - 1 ≤ L G y₁ (Q + 1) - 1 ∧ L G y₁ (Q + 1) - 1 ≤ L G y₁ Q - 1 ∧
    (∀ r : ℤ, cost κ G (L G y₁ Q - 1) Q ≤ cost κ G r Q) ∧
    (∀ r : ℤ, cost κ G (L G y₁ (Q + 1) - 1) (Q + 1) ≤ cost κ G r (Q + 1)) := by
  have hor : L G y₁ (Q + 1) = L G y₁ Q ∨ L G y₁ (Q + 1) = L G y₁ Q - 1 := by
    obtain ⟨n, rfl⟩ : ∃ n, Q = n + 1 := ⟨Q - 1, by omega⟩
    rw [(fz_LR G y₁ (n+1)).1, (fz_LR G y₁ n).1, fz_window_succ]
    split_ifs <;> simp
  refine ⟨hor, by omega, by omega, (fz_cost_window κ G hG y₁ hy₁ Q hQ).2,
    (fz_cost_window κ G hG y₁ hy₁ (Q+1) (by omega)).2⟩

lemma fz_ymin (G : ℤ → ℝ) (y₁ : ℤ) (n : ℕ) :
    G (y G y₁ (n+2)) = min (G ((window G y₁ n).1 - 1)) (G ((window G y₁ n).2 + 1)) := by
  rw [fz_y_succ]
  split_ifs with hc
  · exact (min_eq_left hc).symm
  · rw [not_le] at hc; exact (min_eq_right hc.le).symm

lemma fz_gmono (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t) (Q : ℕ)
    (hQ : 1 ≤ Q) : G (y G y₁ (Q+1)) ≤ G (y G y₁ (Q+2)) := by
  obtain ⟨n, rfl⟩ : ∃ n, Q = n + 1 := ⟨Q - 1, by omega⟩
  rw [show n + 1 + 1 = n + 2 by omega, fz_ymin G y₁ n, fz_ymin G y₁ (n+1),
    fz_window_succ]
  obtain ⟨i1, i2, -, -⟩ := fz_inv G hG y₁ hy₁ n
  split_ifs with hc
  · simp only
    have := fz_left G hG y₁ hy₁ ((window G y₁ n).1 - 1 - 1) ((window G y₁ n).1 - 1) (by omega) (by omega)
    rw [min_eq_left hc]
    exact le_min this hc
  · simp only
    rw [not_le] at hc
    have := fz_right G hG y₁ hy₁ ((window G y₁ n).2 + 1 + 1) ((window G y₁ n).2 + 1) (by omega) (by omega)
    rw [min_eq_right hc.le]
    exact le_min hc.le this

lemma fz_crec (κ : ℝ) (G : ℤ → ℝ) (y₁ : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    ((k:ℝ) + 1) * Cstar κ G y₁ (k+1) = k * Cstar κ G y₁ k + G (y G y₁ (k+1)) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  simp only [Cstar]
  rw [Finset.sum_Icc_succ_top (by omega)]
  push_cast
  field_simp
  ring

lemma fz_C1 (κ : ℝ) (G : ℤ → ℝ) (y₁ : ℤ) : Cstar κ G y₁ 1 = κ + G y₁ := by
  simp [Cstar, y]

theorem lemma2_core (κ : ℝ) (hκ : 0 < κ) (G : ℤ → ℝ)
    (hG : NegUnimodal G) (hco : Coercive G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t) :
    (∃ q : ℕ, 1 ≤ q ∧ Cstar κ G y₁ q ≤ G (y G y₁ (q + 1))) ∧
    ∀ q : ℕ, 1 ≤ q → Cstar κ G y₁ q ≤ G (y G y₁ (q + 1)) →
      (∀ q' : ℕ, 1 ≤ q' → q' < q → G (y G y₁ (q' + 1)) < Cstar κ G y₁ q') →
      ∀ Q : ℕ, 1 ≤ Q → Cstar κ G y₁ q ≤ Cstar κ G y₁ Q := by
  constructor
  · by_contra hne
    push_neg at hne
    -- C* decreasing
    have hdec : ∀ d : ℕ, Cstar κ G y₁ (d+1) ≤ κ + G y₁ := by
      intro d
      induction d with
      | zero => rw [fz_C1]
      | succ d ih =>
        have h1 := hne (d+1) (by omega)
        have h2 := fz_crec κ G y₁ (d+1) (by omega)
        have hp : (0:ℝ) < ((d+1:ℕ):ℝ) + 1 := by positivity
        have : Cstar κ G y₁ (d+1+1) < Cstar κ G y₁ (d+1) := by nlinarith
        linarith
    have hall : ∀ i : ℕ, 1 ≤ i → G (y G y₁ i) < κ + G y₁ + 1 := by
      intro i hi
      rcases Nat.lt_or_ge i 2 with h | h
      · have : i = 1 := by omega
        subst this; simp [y]; linarith
      · obtain ⟨d, rfl⟩ : ∃ d, i = d + 2 := ⟨i - 2, by omega⟩
        have := hne (d+1) (by omega)
        have := hdec d
        rw [show d + 1 + 1 = d + 2 by omega] at *
        linarith
    obtain ⟨hbot, htop⟩ := hco
    obtain ⟨A, hA⟩ := Filter.tendsto_atBot_atTop.1 hbot (κ + G y₁ + 1)
    obtain ⟨B, hB⟩ := Filter.tendsto_atTop_atTop.1 htop (κ + G y₁ + 1)
    set n := (B - A).toNat + 1
    obtain ⟨h1, -⟩ := fz_image G y₁ n
    obtain ⟨-, -, h3, -⟩ := fz_inv G hG y₁ hy₁ n
    have hin : ∀ x, (window G y₁ n).1 ≤ x → x ≤ (window G y₁ n).2 → G x < κ + G y₁ + 1 := by
      intro x hx1 hx2
      have : x ∈ (Finset.Icc 1 (n+1)).image (y G y₁) := by rw [h1]; simp; omega
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 this
      exact hall i (Finset.mem_Icc.1 hi).1
    have ha : A < (window G y₁ n).1 := by
      by_contra h; push_neg at h
      have := hA _ h
      have := hin _ le_rfl (by omega)
      linarith
    have hb : (window G y₁ n).2 < B := by
      by_contra h; push_neg at h
      have := hB _ h
      have := hin _ (by omega) le_rfl
      linarith
    have : (n:ℤ) = (B - A).toNat + 1 := by simp [n]
    omega
  · intro q hq hqc hfirst Q hQ
    rcases Nat.lt_or_ge Q q with hlt | hge
    · have : ∀ d : ℕ, Q + d ≤ q → Cstar κ G y₁ (Q + d) ≤ Cstar κ G y₁ Q := by
        intro d
        induction d with
        | zero => intro _; simp
        | succ d ih =>
          intro hd
          have h1 := hfirst (Q + d) (by omega) (by omega)
          have h2 := fz_crec κ G y₁ (Q+d) (by omega)
          have hp : (0:ℝ) < ((Q+d:ℕ):ℝ) + 1 := by positivity
          have : Cstar κ G y₁ (Q+d+1) < Cstar κ G y₁ (Q+d) := by nlinarith
          rw [← add_assoc]
          linarith [ih (by omega)]
      have := this (q - Q) (by omega)
      rwa [show Q + (q - Q) = q by omega] at this
    · have : ∀ d : ℕ, Cstar κ G y₁ q ≤ Cstar κ G y₁ (q + d) ∧
          Cstar κ G y₁ (q + d) ≤ G (y G y₁ (q + d + 1)) := by
        intro d
        induction d with
        | zero => simpa using hqc
        | succ d ih =>
          obtain ⟨i1, i2⟩ := ih
          have h2 := fz_crec κ G y₁ (q+d) (by omega)
          have hm := fz_gmono G hG y₁ hy₁ (q+d) (by omega)
          have hp : (0:ℝ) < ((q+d:ℕ):ℝ) + 1 := by positivity
          have hk : (0:ℝ) ≤ ((q+d:ℕ):ℝ) := by positivity
          have a1 : Cstar κ G y₁ (q+d) ≤ Cstar κ G y₁ (q+d+1) := by nlinarith
          have a2 : Cstar κ G y₁ (q+d+1) ≤ G (y G y₁ (q+d+1)) := by nlinarith
          rw [← add_assoc]
          exact ⟨le_trans i1 a1, by rw [show q + d + 1 + 1 = q + d + 2 by omega]; linarith⟩
      have := (this (Q - q)).1
      rwa [show q + (Q - q) = Q by omega] at this

end FedergruenZhengRQ.OPT

open FedergruenZhengRQ.OPT


theorem solution (κ : ℝ) (hκ : 0 < κ) (G : ℤ → ℝ)
    (hG : NegUnimodal G) (hco : Coercive G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t) :
    (∃ q : ℕ, 1 ≤ q ∧ Cstar κ G y₁ q ≤ G (y G y₁ (q + 1))) ∧
    ∀ q : ℕ, 1 ≤ q → Cstar κ G y₁ q ≤ G (y G y₁ (q + 1)) →
      (∀ q' : ℕ, 1 ≤ q' → q' < q → G (y G y₁ (q' + 1)) < Cstar κ G y₁ q') →
      ∀ Q : ℕ, 1 ≤ Q → Cstar κ G y₁ q ≤ Cstar κ G y₁ Q := by
  exact lemma2_core κ hκ G hG hco y₁ hy₁
