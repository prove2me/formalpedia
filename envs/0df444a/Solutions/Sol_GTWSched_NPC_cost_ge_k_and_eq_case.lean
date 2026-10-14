-- Prove2me | solution 1 for GTWSched.NPC.cost_ge_k_and_eq_case
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:53:52.971409+00:00
-- url     : https://prove2.me/submissions/63d7ae5c-317e-4d85-8fcf-692b254da5ad

import Mathlib
import Definitions.Def_GTWSched_NPC_Schedules



namespace GTWSched.NPC


lemma sumIcc_bot (f : ℕ → ℝ) (a b : ℕ) (h : a ≤ b) :
    ∑ k ∈ Finset.Icc a b, f k = f a + ∑ k ∈ Finset.Icc (a+1) b, f k := by
  have : Finset.Icc a b = insert a (Finset.Icc (a+1) b) := by
    ext x; simp; omega
  rw [this, Finset.sum_insert (by simp)]

noncomputable def eSlack (Y L : ℕ → ℝ) (k : ℕ) : ℝ := Y (k+1) - Y k - (L k + L (k+1))/2

noncomputable def wsum (L : ℕ → ℝ) (r a : ℕ) : ℝ := ∑ q ∈ Finset.Icc a (a + 2*r), L q

noncomputable def gfun (L : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | r+1, a => gfun L r (a+1) + (wsum L r (a+1) + wsum L (r+1) a)/2

lemma telescope_aux (Y L : ℕ → ℝ) (a : ℕ) : ∀ j : ℕ,
    Y (a+j+1) - Y a = (L a + L (a+j+1))/2 + ∑ q ∈ Finset.Icc (a+1) (a+j), L q
      + ∑ k ∈ Finset.Ico a (a+j+1), eSlack Y L k := by
  intro j
  induction j with
  | zero => simp [eSlack]
  | succ j ih =>
    have h1 : ∑ q ∈ Finset.Icc (a+1) (a+(j+1)), L q = ∑ q ∈ Finset.Icc (a+1) (a+j), L q + L (a+j+1) := by
      rw [show a + (j+1) = (a+j)+1 by ring]
      exact Finset.sum_Icc_succ_top (by omega) L
    have h2 : ∑ k ∈ Finset.Ico a (a+(j+1)+1), eSlack Y L k = ∑ k ∈ Finset.Ico a (a+j+1), eSlack Y L k + eSlack Y L (a+j+1) := by
      rw [show a + (j+1) + 1 = (a+j+1)+1 by ring]
      exact Finset.sum_Ico_succ_top (by omega) _
    rw [h1, h2]
    have : eSlack Y L (a+j+1) = Y (a+j+1+1) - Y (a+j+1) - (L (a+j+1) + L (a+j+1+1))/2 := rfl
    rw [show a + (j+1) + 1 = a+j+1+1 by ring]
    linarith

lemma telescope (Y L : ℕ → ℝ) (a r : ℕ) :
    Y (a + 2*r + 2) - Y a = (L a + L (a+2*r+2))/2 + wsum L r (a+1)
      + ∑ k ∈ Finset.Ico a (a+2*r+2), eSlack Y L k := by
  have := telescope_aux Y L a (2*r+1)
  unfold wsum
  rw [show a + 2*r + 2 = a + (2*r+1) + 1 by ring]
  rw [show a + 1 + 2*r = a + (2*r+1) by ring]
  exact this

lemma window_bound (Y L : ℕ → ℝ) (M : ℝ) (N : ℕ) (he : ∀ k, k + 1 < N → 0 ≤ eSlack Y L k) :
    ∀ r a, a + 2*r < N →
      gfun L r a + |M - Y (a+r)| + ∑ k ∈ Finset.Ico a (a+2*r), eSlack Y L k
        ≤ ∑ q ∈ Finset.Icc a (a+2*r), |M - Y q| := by
  intro r
  induction r with
  | zero => intro a _; simp [gfun]
  | succ r ih =>
    intro a ha
    have ih' := ih (a+1) (by omega)
    have tel := telescope Y L a r
    -- decompositions
    have hs : ∑ q ∈ Finset.Icc a (a+2*(r+1)), |M - Y q| =
        |M - Y a| + ∑ q ∈ Finset.Icc (a+1) (a+1+2*r), |M - Y q| + |M - Y (a+2*(r+1))| := by
      rw [sumIcc_bot _ a _ (by omega)]
      rw [show a + 2*(r+1) = (a+1+2*r)+1 by ring]
      rw [Finset.sum_Icc_succ_top (by omega)]
      try ring_nf
    have he1 : ∑ k ∈ Finset.Ico a (a+2*(r+1)), eSlack Y L k =
        eSlack Y L a + ∑ k ∈ Finset.Ico (a+1) (a+1+2*r), eSlack Y L k + eSlack Y L (a+1+2*r) := by
      rw [show a + 2*(r+1) = (a+1+2*r)+1 by ring]
      rw [Finset.sum_Ico_succ_top (by omega)]
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      try ring
    have hnn : 0 ≤ ∑ k ∈ Finset.Ico (a+1) (a+1+2*r), eSlack Y L k :=
      Finset.sum_nonneg (fun k hk => he k (by simp at hk; omega))
    have hws : wsum L (r+1) a = L a + wsum L r (a+1) + L (a+2*(r+1)) := by
      unfold wsum
      rw [sumIcc_bot _ a _ (by omega)]
      rw [show a + 2*(r+1) = (a+1+2*r)+1 by ring]
      rw [Finset.sum_Icc_succ_top (by omega)]
      try ring_nf
    have htri : Y (a+2*(r+1)) - Y a ≤ |M - Y a| + |M - Y (a+2*(r+1))| := by
      linarith [le_abs_self (M - Y a), neg_le_abs (M - Y (a + 2*(r+1)))]
    have hcen : a + 1 + r = a + (r+1) := by ring
    rw [hcen] at ih'
    rw [show a + 2*r + 2 = a + 2*(r+1) by ring] at tel
    rw [he1] at tel
    have hg : gfun L (r+1) a = gfun L r (a+1) + (wsum L r (a+1) + wsum L (r+1) a)/2 := rfl
    have he0 : 0 ≤ eSlack Y L (a+1+2*r) := he _ (by omega)
    have he00 : 0 ≤ eSlack Y L a := he _ (by omega)
    rw [hg, hs, he1, hws]
    linarith


noncomputable def Lsum (l' : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, l' i

noncomputable def Gstar (l' : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | r+1 => Gstar l' r + (Lsum l' (2*r+1) + Lsum l' (2*r+3))/2

lemma layer (l' : ℕ → ℝ) (N k : ℕ) (hk : k ≤ N) (hmono : ∀ i j, i < j → j < N → l' i < l' j)
    (U : Finset ℕ) (hU : ∀ i ∈ U, i < N) (hc : U.card = k) :
    Lsum l' k ≤ ∑ i ∈ U, l' i ∧ (∑ i ∈ U, l' i = Lsum l' k → U = Finset.range k) := by
  unfold Lsum
  set T := Finset.range k with hT
  have hTc : T.card = k := by simp [hT]
  have hcard : (U \ T).card = (T \ U).card := by
    have h1 := Finset.card_sdiff_add_card_inter U T
    have h2 := Finset.card_sdiff_add_card_inter T U
    rw [Finset.inter_comm] at h2
    omega
  have hdiff : ∑ i ∈ U, l' i - ∑ i ∈ T, l' i = ∑ i ∈ U \ T, l' i - ∑ i ∈ T \ U, l' i :=
    (Finset.sum_sdiff_sub_sum_sdiff).symm
  by_cases hemp : U \ T = ∅
  · have hsub : U ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have : U = T := Finset.eq_of_subset_of_card_le hsub (by omega)
    subst this
    exact ⟨le_refl _, fun _ => rfl⟩
  · have hne : (U \ T).Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
    obtain ⟨u0, hu0⟩ := hne
    have hu0' := Finset.mem_sdiff.mp hu0
    have hu0N := hU u0 hu0'.1
    have hku0 : k ≤ u0 := by
      by_contra h; exact hu0'.2 (by simp [hT]; omega)
    have hcpos : 0 < (U \ T).card := Finset.card_pos.mpr ⟨u0, hu0⟩
    have hk1 : 1 ≤ k := by
      have : 0 < (T \ U).card := by omega
      obtain ⟨t0, ht0⟩ := Finset.card_pos.mp this
      have := Finset.mem_sdiff.mp ht0
      simp [hT] at this
      omega
    have hup : ∀ u ∈ U \ T, l' k ≤ l' u := by
      intro u hu
      have hu' := Finset.mem_sdiff.mp hu
      have huN := hU u hu'.1
      have : k ≤ u := by
        by_contra h; exact hu'.2 (by simp [hT]; omega)
      rcases this.lt_or_eq with h | h
      · exact (hmono k u h huN).le
      · rw [h]
    have hlo : ∀ t ∈ T \ U, l' t ≤ l' (k-1) := by
      intro t ht
      have ht' := Finset.mem_sdiff.mp ht
      have : t < k := by simpa [hT] using ht'.1
      rcases (show t ≤ k-1 by omega).lt_or_eq with h | h
      · exact (hmono t (k-1) h (by omega)).le
      · rw [h]
    have h1 := Finset.card_nsmul_le_sum (U \ T) l' (l' k) hup
    have h2 := Finset.sum_le_card_nsmul (T \ U) l' (l' (k-1)) hlo
    have hstep : l' (k-1) < l' k := hmono (k-1) k (by omega) (by omega)
    rw [← hcard] at h2
    have hc' : (0:ℝ) < ((U \ T).card : ℝ) := by exact_mod_cast hcpos
    simp only [nsmul_eq_mul] at h1 h2
    have : 0 < ∑ i ∈ U, l' i - ∑ i ∈ T, l' i := by
      rw [hdiff]; nlinarith
    constructor
    · linarith
    · intro h; linarith


lemma gfun_ge (Λ l' : ℕ → ℝ) (N : ℕ)
    (hS : ∀ r b, b + 2*r < N → Lsum l' (2*r+1) ≤ wsum Λ r b) :
    ∀ r a, a + 2*r < N → Gstar l' r ≤ gfun Λ r a ∧
      (gfun Λ r a = Gstar l' r → 1 ≤ r → ∀ r', r' ≤ r → wsum Λ r' (a + r - r') = Lsum l' (2*r'+1)) := by
  intro r
  induction r with
  | zero => intro a _; simp [Gstar, gfun]
  | succ r ih =>
    intro a ha
    obtain ⟨ih1, ih2⟩ := ih (a+1) (by omega)
    have h0 := hS r (a+1) (by omega)
    have h1 := hS (r+1) a (by omega)
    have hG : Gstar l' (r+1) = Gstar l' r + (Lsum l' (2*r+1) + Lsum l' (2*r+3))/2 := rfl
    have hg : gfun Λ (r+1) a = gfun Λ r (a+1) + (wsum Λ r (a+1) + wsum Λ (r+1) a)/2 := rfl
    have h1' : Lsum l' (2*r+3) ≤ wsum Λ (r+1) a := by
      have := h1; rwa [show 2*(r+1)+1 = 2*r+3 by ring] at this
    refine ⟨by rw [hG, hg]; linarith, ?_⟩
    intro heq _ r' hr'
    rw [hG, hg] at heq
    have e1 : gfun Λ r (a+1) = Gstar l' r := by linarith
    have e2 : wsum Λ r (a+1) = Lsum l' (2*r+1) := by linarith
    have e3 : wsum Λ (r+1) a = Lsum l' (2*r+3) := by linarith
    rcases (show r' = r+1 ∨ r' = r ∨ r' < r by omega) with h | h | h
    · subst h
      rw [show a + (r+1) - (r+1) = a by omega, e3]
      rw [show 2*(r+1)+1 = 2*r+3 by ring]
    · subst h
      rw [show a + (r'+1) - r' = a + 1 by omega, e2]
    · have := ih2 e1 (by omega) r' (by omega)
      rw [show a + (r+1) - r' = a + 1 + r - r' by omega]
      exact this


lemma Lsum_odd (l' : ℕ → ℝ) (n : ℕ) :
    Lsum l' (2*n+1) = l' 0 + ∑ j ∈ Finset.range n, (l' (2*j+1) + l' (2*j+2)) := by
  induction n with
  | zero => simp [Lsum]
  | succ n ih =>
    have : Lsum l' (2*(n+1)+1) = Lsum l' (2*n+1) + l' (2*n+1) + l' (2*n+2) := by
      unfold Lsum
      rw [show 2*(n+1)+1 = (2*n+1)+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ]
      try ring_nf
    rw [this, ih, Finset.sum_range_succ]
    ring

lemma Gstar_eq (l' : ℕ → ℝ) (n : ℕ) :
    Gstar l' n = (∑ j ∈ Finset.range n, (l' (2*j+2) + l' (2*j+1)) * ((n:ℝ) - j - 1/2)) + l' 0 * n := by
  induction n with
  | zero => simp [Gstar]
  | succ n ih =>
    have h1 : Gstar l' (n+1) = Gstar l' n + (Lsum l' (2*n+1) + Lsum l' (2*n+3))/2 := rfl
    have h3 : Lsum l' (2*n+3) = Lsum l' (2*n+1) + l' (2*n+1) + l' (2*n+2) := by
      unfold Lsum
      rw [show 2*n+3 = (2*n+1)+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [h1, h3, ih, Lsum_odd, Finset.sum_range_succ]
    have : ∑ j ∈ Finset.range n, (l' (2*j+2) + l' (2*j+1)) * (((n+1:ℕ):ℝ) - j - 1/2) =
        ∑ j ∈ Finset.range n, (l' (2*j+2) + l' (2*j+1)) * ((n:ℝ) - j - 1/2) +
        ∑ j ∈ Finset.range n, (l' (2*j+1) + l' (2*j+2)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    rw [this]
    push_cast
    ring


lemma main_nat (n : ℕ) (l' m' : ℕ → ℝ) (π : ℕ → ℕ) (M : ℝ)
    (hmono : ∀ i j, i < j → j < 2*n+1 → l' i < l' j)
    (hinj : Function.Injective π) (hlt : ∀ q, q < 2*n+1 → π q < 2*n+1)
    (hgap : ∀ k, k + 1 < 2*n+1 → (l' (π k) + l' (π (k+1)))/2 ≤ m' (π (k+1)) - m' (π k)) :
    Gstar l' n ≤ ∑ q ∈ Finset.Icc 0 (2*n), |M - m' (π q)| ∧
    (∑ q ∈ Finset.Icc 0 (2*n), |M - m' (π q)| = Gstar l' n →
      m' (π n) = M ∧
      (∀ k, k < 2*n → m' (π (k+1)) - m' (π k) = (l' (π k) + l' (π (k+1))) / 2) ∧
      (1 ≤ n → ∀ r, r ≤ n → (Finset.Icc (n-r) (n+r)).image π = Finset.range (2*r+1))) := by
  set Y : ℕ → ℝ := fun q => m' (π q) with hY
  set Λ : ℕ → ℝ := fun q => l' (π q) with hΛ
  have he : ∀ k, k + 1 < 2*n+1 → 0 ≤ eSlack Y Λ k := by
    intro k hk; have := hgap k hk; simp only [eSlack, hY, hΛ]; linarith
  have hlayer : ∀ r b, b + 2*r < 2*n+1 →
      Lsum l' (2*r+1) ≤ wsum Λ r b ∧
      (wsum Λ r b = Lsum l' (2*r+1) → (Finset.Icc b (b+2*r)).image π = Finset.range (2*r+1)) := by
    intro r b hb
    have hU := layer l' (2*n+1) (2*r+1) (by omega) hmono ((Finset.Icc b (b+2*r)).image π)
      (by
        intro i hi
        simp only [Finset.mem_image, Finset.mem_Icc] at hi
        obtain ⟨q, hq, rfl⟩ := hi
        exact hlt q (by omega))
      (by rw [Finset.card_image_of_injective _ hinj]; simp; omega)
    rw [Finset.sum_image (fun x _ y _ h => hinj h)] at hU
    exact hU
  have hS : ∀ r b, b + 2*r < 2*n+1 → Lsum l' (2*r+1) ≤ wsum Λ r b := fun r b hb => (hlayer r b hb).1
  have hwb := window_bound Y Λ M (2*n+1) he n 0 (by omega)
  have hgf := gfun_ge Λ l' (2*n+1) hS n 0 (by omega)
  simp only [zero_add] at hwb hgf
  have hEnn : 0 ≤ ∑ k ∈ Finset.Ico 0 (2*n), eSlack Y Λ k :=
    Finset.sum_nonneg (fun k hk => he k (by simp at hk; omega))
  have habs : 0 ≤ |M - Y n| := abs_nonneg _
  refine ⟨by linarith [hgf.1], ?_⟩
  intro hcost
  have hg : gfun Λ n 0 = Gstar l' n := by linarith [hgf.1]
  have hY0 : |M - Y n| = 0 := by linarith [hgf.1]
  have hMY : m' (π n) = M := by
    have := abs_eq_zero.mp hY0
    simp only [hY] at this
    linarith
  have hE0 : ∑ k ∈ Finset.Ico 0 (2*n), eSlack Y Λ k = 0 := by
    apply le_antisymm _ hEnn
    linarith [hgf.1]
  have hEk := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k hk => he k (by simp at hk; omega))).mp hE0
  refine ⟨hMY, ?_, ?_⟩
  · intro k hk
    have := hEk k (by simp; omega)
    simp only [eSlack, hY, hΛ] at this
    linarith
  intro hn r hr
  have hw := hgf.2 hg hn r hr
  have := (hlayer r (n-r) (by omega)).2 hw
  rwa [show n - r + 2*r = n + r by omega] at this

noncomputable def extF {N : ℕ} (f : Fin N → ℝ) (i : ℕ) : ℝ := if h : i < N then f ⟨i, h⟩ else 0

def extP {N : ℕ} (σ : Equiv.Perm (Fin N)) (q : ℕ) : ℕ := if h : q < N then (σ ⟨q, h⟩).val else q

lemma extF_val {N : ℕ} (f : Fin N → ℝ) (x : Fin N) : extF f x.val = f x := by
  simp [extF, x.isLt]

lemma extP_lt {N : ℕ} (σ : Equiv.Perm (Fin N)) (q : ℕ) (h : q < N) : extP σ q = (σ ⟨q, h⟩).val := by
  simp [extP, h]

lemma extP_inj {N : ℕ} (σ : Equiv.Perm (Fin N)) : Function.Injective (extP σ) := by
  intro a b hab
  by_cases ha : a < N <;> by_cases hb : b < N
  · rw [extP_lt σ a ha, extP_lt σ b hb] at hab
    have := σ.injective (Fin.ext hab)
    simpa using congrArg Fin.val this
  · rw [extP_lt σ a ha] at hab
    have := (σ ⟨a, ha⟩).isLt
    simp [extP, hb] at hab; omega
  · rw [extP_lt σ b hb] at hab
    have := (σ ⟨b, hb⟩).isLt
    simp [extP, ha] at hab; omega
  · simp [extP, ha, hb] at hab; exact hab

lemma kStar_eq_Gstar {n : ℕ} (l : Fin (2 * n + 1) → ℝ) : kStar l = Gstar (extF l) n := by
  rw [Gstar_eq]
  unfold kStar
  congr 1
  · rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro j _
    have h1 : extF l (2 * (j:ℕ) + 2) = l (evenTask j) := by
      have := extF_val l (evenTask j)
      simpa [evenTask] using this
    have h2 : extF l (2 * (j:ℕ) + 1) = l (oddTask j) := by
      have := extF_val l (oddTask j)
      simpa [oddTask] using this
    rw [h1, h2]

lemma gap_of_lt {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (hl0 : 0 < l 0) (hmono : StrictMono l)
    (s : Fin (2 * n + 1) → ℝ)
    (hns : ∀ i j, i ≠ j → s i + l i ≤ s j ∨ s j + l j ≤ s i) (i j : Fin (2 * n + 1))
    (h : mid l s i < mid l s j) : (l i + l j) / 2 ≤ mid l s j - mid l s i := by
  have hne : i ≠ j := by intro e; subst e; exact lt_irrefl _ h
  have hpi : 0 < l i := lt_of_lt_of_le hl0 (hmono.monotone (Fin.zero_le _))
  have hpj : 0 < l j := lt_of_lt_of_le hl0 (hmono.monotone (Fin.zero_le _))
  unfold mid at *
  rcases hns i j hne with h1 | h1
  · linarith
  · linarith

lemma mid_inj {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (hl0 : 0 < l 0) (hmono : StrictMono l)
    (s : Fin (2 * n + 1) → ℝ)
    (hns : ∀ i j, i ≠ j → s i + l i ≤ s j ∨ s j + l j ≤ s i) : Function.Injective (mid l s) := by
  intro i j hij
  by_contra hne
  have hpi : 0 < l i := lt_of_lt_of_le hl0 (hmono.monotone (Fin.zero_le _))
  have hpj : 0 < l j := lt_of_lt_of_le hl0 (hmono.monotone (Fin.zero_le _))
  unfold mid at hij
  rcases hns i j hne with h1 | h1 <;> linarith

theorem core_pos {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (hl0 : 0 < l 0) (hmono : StrictMono l)
    (M : ℝ) (s : Fin (2 * n + 1) → ℝ)
    (hns : ∀ i j, i ≠ j → s i + l i ≤ s j ∨ s j + l j ≤ s i) :
    kStar l ≤ commonCost l M s ∧
    (commonCost l M s = kStar l → ∃ σ : Equiv.Perm (Fin (2 * n + 1)),
      (∀ a b : Fin (2 * n + 1), a < b → mid l s (σ a) < mid l s (σ b)) ∧
      (∀ a b : Fin (2 * n + 1), a.val + 1 = b.val →
        mid l s (σ b) - mid l s (σ a) = (l (σ a) + l (σ b)) / 2) ∧
      σ ⟨n, by omega⟩ = 0 ∧ mid l s 0 = M ∧
      (∀ q : Fin (2 * n + 1), n < q.val →
        (σ q).val = 2 * (q.val - n) - 1 ∨ (σ q).val = 2 * (q.val - n)) ∧
      (∀ q : Fin (2 * n + 1), q.val < n →
        (σ q).val = 2 * (n - q.val) - 1 ∨ (σ q).val = 2 * (n - q.val))) := by
  classical
  set m : Fin (2 * n + 1) → ℝ := mid l s with hm
  set σ : Equiv.Perm (Fin (2 * n + 1)) := Tuple.sort m with hσ
  have hmono_s : Monotone (m ∘ σ) := Tuple.monotone_sort m
  have hinj := mid_inj l hl0 hmono s hns
  have hstrict : ∀ a b : Fin (2 * n + 1), a < b → m (σ a) < m (σ b) := by
    intro a b hab
    have h1 := hmono_s hab.le
    have h2 : σ a ≠ σ b := fun e => absurd (σ.injective e) (ne_of_lt hab)
    exact lt_of_le_of_ne h1 (fun e => h2 (hinj e))
  have hY : ∀ q (h : q < 2 * n + 1), extF m (extP σ q) = m (σ ⟨q, h⟩) := by
    intro q h
    rw [extP_lt σ q h, extF_val m (σ ⟨q, h⟩)]
  have hL : ∀ q (h : q < 2 * n + 1), extF l (extP σ q) = l (σ ⟨q, h⟩) := by
    intro q h
    rw [extP_lt σ q h, extF_val l (σ ⟨q, h⟩)]
  have hgap : ∀ k, k + 1 < 2 * n + 1 →
      (extF l (extP σ k) + extF l (extP σ (k + 1))) / 2 ≤
        extF m (extP σ (k + 1)) - extF m (extP σ k) := by
    intro k hk
    rw [hY k (by omega), hY (k+1) hk, hL k (by omega), hL (k+1) hk]
    exact gap_of_lt l hl0 hmono s hns _ _ (hstrict ⟨k, by omega⟩ ⟨k+1, hk⟩ (by simp [Fin.lt_def]))
  have hmono' : ∀ i j, i < j → j < 2 * n + 1 → extF l i < extF l j := by
    intro i j hij hj
    simp only [extF, dif_pos hj, dif_pos (lt_trans hij hj)]
    exact hmono (by simp [Fin.lt_def, hij])
  have hlt : ∀ q, q < 2 * n + 1 → extP σ q < 2 * n + 1 := by
    intro q hq
    rw [extP_lt σ q hq]; exact (σ ⟨q, hq⟩).isLt
  have hmain := main_nat n (extF l) (extF m) (extP σ) M hmono' (extP_inj σ) hlt hgap
  have hcost : ∑ q ∈ Finset.Icc 0 (2 * n), |M - extF m (extP σ q)| = commonCost l M s := by
    have : Finset.Icc 0 (2 * n) = Finset.range (2 * n + 1) := by ext; simp
    rw [this, Finset.sum_range (fun q => |M - extF m (extP σ q)|)]
    unfold commonCost
    rw [← Equiv.sum_comp σ (fun i => |M - mid l s i|)]
    apply Finset.sum_congr rfl
    intro q _
    rw [hY q.val q.isLt]
  rw [kStar_eq_Gstar, ← hcost]
  refine ⟨hmain.1, ?_⟩
  intro heq
  obtain ⟨hMy, hgp, hlay⟩ := hmain.2 heq
  have side : 1 ≤ n → ∀ q, q < 2 * n + 1 → ∀ d, 1 ≤ d → d ≤ n → (q = n + d ∨ q + d = n) →
      2 * d - 1 ≤ extP σ q ∧ extP σ q < 2 * d + 1 := by
    intro hn q hq d hd1 hdn hqd
    have h1 := hlay hn d hdn
    have hq1 : extP σ q ∈ Finset.range (2 * d + 1) := by
      rw [← h1]; exact Finset.mem_image_of_mem _ (by simp; omega)
    have h2 := hlay hn (d - 1) (by omega)
    have hq2 : extP σ q ∉ Finset.range (2 * (d - 1) + 1) := by
      rw [← h2]
      intro hmem
      obtain ⟨q', hq', hq'e⟩ := Finset.mem_image.mp hmem
      have := extP_inj σ hq'e
      subst this
      simp at hq'; omega
    simp at hq1 hq2; omega
  have hn0 : σ ⟨n, by omega⟩ = 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; apply Fin.ext; have := (σ ⟨0, by omega⟩).isLt; simp at this ⊢
    · have h1 := hlay h 0 (Nat.zero_le _)
      have hq1 : extP σ n ∈ Finset.range (2 * 0 + 1) := by
        rw [← h1]; exact Finset.mem_image_of_mem _ (by simp)
      rw [extP_lt σ n (by omega)] at hq1
      simp at hq1
      exact hq1
  refine ⟨σ, hstrict, ?_, hn0, ?_, ?_, ?_⟩
  · intro a b hab
    have := hgp a.val (by omega)
    rw [hY a.val a.isLt, hY (a.val + 1) (by omega), hL a.val a.isLt, hL (a.val+1) (by omega)] at this
    have e1 : (⟨a.val, a.isLt⟩ : Fin (2 * n + 1)) = a := rfl
    have e2 : (⟨a.val + 1, by omega⟩ : Fin (2 * n + 1)) = b := Fin.ext hab
    rw [e1, e2] at this
    exact this
  · have := hY n (by omega)
    rw [hMy] at this
    rw [← hn0]
    exact this.symm
  · intro q hq
    have hn : 1 ≤ n := by omega
    have := side hn q.val q.isLt (q.val - n) (by omega) (by have := q.isLt; omega) (Or.inl (by omega))
    rw [extP_lt σ q.val q.isLt] at this
    simp only [Fin.eta] at this
    omega
  · intro q hq
    have hn : 1 ≤ n := by omega
    have := side hn q.val q.isLt (n - q.val) (by omega) (by omega) (Or.inr (by omega))
    rw [extP_lt σ q.val q.isLt] at this
    simp only [Fin.eta] at this
    omega

lemma l_pos {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (hl0 : 0 < l 0) (hmono : StrictMono l) (i : Fin (2*n+1)) :
    0 < l i := lt_of_lt_of_le hl0 (hmono.monotone (Fin.zero_le _))

lemma card_lt_n (n : ℕ) : (Finset.univ.filter (fun q : Fin (2*n+1) => q.val < n)).card = n := by
  have : (Finset.univ.filter (fun q : Fin (2*n+1) => q.val < n)).map Fin.valEmbedding = Finset.range n := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  have h := congrArg Finset.card this
  simpa using h

lemma card_gt_n (n : ℕ) : (Finset.univ.filter (fun q : Fin (2*n+1) => n < q.val)).card = n := by
  have : (Finset.univ.filter (fun q : Fin (2*n+1) => n < q.val)).map Fin.valEmbedding = Finset.Ioo n (2*n+1) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ioo]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨ha, a.isLt⟩
    · intro hx; exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  have h := congrArg Finset.card this
  rw [Finset.card_map, Nat.card_Ioo] at h
  omega

theorem struct_eq {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (hl0 : 0 < l 0) (hmono : StrictMono l)
    (M : ℝ) (s : Fin (2 * n + 1) → ℝ)
    (hns : ∀ i j, i ≠ j → s i + l i ≤ s j ∨ s j + l j ≤ s i)
    (hc : commonCost l M s = kStar l) :
    Ordered l M s ∧ NoGaps l s ∧ mid l s 0 = M ∧
      (∀ i : Fin n,
        (oddTask i ∈ setA l M s ∧ evenTask i ∈ setB l M s) ∨
          (evenTask i ∈ setA l M s ∧ oddTask i ∈ setB l M s)) ∧
      (setA l M s).card = n ∧ (setB l M s).card = n := by
  classical
  obtain ⟨σ, hst, htight, hn0, hmid0, hodd, hlow⟩ := (core_pos l hl0 hmono M s hns).2 hc
  have hMeq : mid l s (σ ⟨n, by omega⟩) = M := by rw [hn0]; exact hmid0
  have hA : ∀ i, i ∈ setA l M s ↔ (σ.symm i).val < n := by
    intro i
    simp only [setA, Finset.mem_filter, Finset.mem_univ, true_and]
    have e : i = σ (σ.symm i) := (σ.apply_symm_apply i).symm
    constructor
    · intro h
      by_contra hn
      push_neg at hn
      rcases hn.lt_or_eq with h1 | h1
      · have := hst ⟨n, by omega⟩ (σ.symm i) h1
        rw [hMeq, ← e] at this; linarith
      · have : σ.symm i = ⟨n, by omega⟩ := Fin.ext h1.symm
        rw [e, this, hMeq] at h; exact lt_irrefl _ h
    · intro h
      have := hst (σ.symm i) ⟨n, by omega⟩ (by simp [Fin.lt_def, h])
      rw [hMeq, ← e] at this; exact this
  have hB : ∀ i, i ∈ setB l M s ↔ n < (σ.symm i).val := by
    intro i
    simp only [setB, Finset.mem_filter, Finset.mem_univ, true_and]
    have e : i = σ (σ.symm i) := (σ.apply_symm_apply i).symm
    constructor
    · intro h
      by_contra hn
      push_neg at hn
      rcases hn.lt_or_eq with h1 | h1
      · have := hst (σ.symm i) ⟨n, by omega⟩ h1
        rw [hMeq, ← e] at this; linarith
      · have : σ.symm i = ⟨n, by omega⟩ := Fin.ext h1
        rw [e, this, hMeq] at h; exact lt_irrefl _ h
    · intro h
      have := hst ⟨n, by omega⟩ (σ.symm i) (by simp [Fin.lt_def, h])
      rw [hMeq, ← e] at this; exact this
  -- value facts for each task
  have hvalA : ∀ i, (σ.symm i).val < n →
      i.val = 2 * (n - (σ.symm i).val) - 1 ∨ i.val = 2 * (n - (σ.symm i).val) := by
    intro i h
    have := hlow (σ.symm i) h
    simpa using this
  have hvalB : ∀ i, n < (σ.symm i).val →
      i.val = 2 * ((σ.symm i).val - n) - 1 ∨ i.val = 2 * ((σ.symm i).val - n) := by
    intro i h
    have := hodd (σ.symm i) h
    simpa using this
  refine ⟨⟨?_, ?_⟩, ?_, hmid0, ?_, ?_, ?_⟩
  · -- Ordered A
    intro i j hi hj hlij
    rw [hA] at hi hj
    have hij : i.val < j.val := by
      have := hmono.lt_iff_lt.mp hlij
      exact this
    have hqq : (σ.symm j).val < (σ.symm i).val := by
      by_contra hcon
      push_neg at hcon
      have a1 := hvalA i hi
      have a2 := hvalA j hj
      rcases hcon.lt_or_eq with h1 | h1
      · omega
      · have : σ.symm j = σ.symm i := Fin.ext h1.symm
        have := σ.symm.injective this
        subst this; exact lt_irrefl _ hij
    have := hst (σ.symm j) (σ.symm i) hqq
    simpa using this
  · -- Ordered B
    intro i j hi hj hlij
    rw [hB] at hi hj
    have hij : i.val < j.val := hmono.lt_iff_lt.mp hlij
    have hqq : (σ.symm i).val < (σ.symm j).val := by
      by_contra hcon
      push_neg at hcon
      have a1 := hvalB i hi
      have a2 := hvalB j hj
      rcases hcon.lt_or_eq with h1 | h1
      · omega
      · have : σ.symm j = σ.symm i := Fin.ext h1
        have := σ.symm.injective this
        subst this; exact lt_irrefl _ hij
    have := hst (σ.symm i) (σ.symm j) hqq
    simpa using this
  · -- NoGaps
    intro i
    set q := σ.symm i with hq
    have e : i = σ q := (σ.apply_symm_apply i).symm
    by_cases hq0 : q.val = 0
    · left
      intro j
      by_cases hji : j = i
      · rw [hji]
      · have hqj : q < σ.symm j := by
          have hne : σ.symm j ≠ q := fun h => hji (by have h5 := congrArg σ h; rw [σ.apply_symm_apply] at h5; exact h5.trans e.symm)
          have : (σ.symm j).val ≠ q.val := fun h => hne (Fin.ext h)
          simp only [Fin.lt_def]; omega
        have h1 := hst q (σ.symm j) hqj
        rw [← e] at h1
        have h2 : σ (σ.symm j) = j := σ.apply_symm_apply j
        rw [h2] at h1
        rcases hns i j (Ne.symm hji) with h3 | h3
        · have := l_pos l hl0 hmono i
          unfold mid at h1; linarith
        · have := l_pos l hl0 hmono j
          have := l_pos l hl0 hmono i
          unfold mid at h1; linarith
    · right
      have hq1 : q.val - 1 < 2 * n + 1 := by have := q.isLt; omega
      refine ⟨σ ⟨q.val - 1, hq1⟩, ?_, ?_⟩
      · intro h
        have h' := σ.injective (h.trans e)
        have := congrArg Fin.val h'
        simp at this; omega
      · have := htight ⟨q.val - 1, hq1⟩ q (by simp; omega)
        rw [← e] at this
        unfold mid at this
        linarith
  · -- pairs
    intro i
    have hov : (oddTask i).val = 2 * i.val + 1 := rfl
    have hev : (evenTask i).val = 2 * i.val + 2 := rfl
    have hne1 : (σ.symm (oddTask i)).val ≠ (σ.symm (evenTask i)).val := by
      intro h
      have := σ.symm.injective (Fin.ext h)
      have := congrArg Fin.val this
      omega
    have hn1 : (σ.symm (oddTask i)).val ≠ n := by
      intro h
      have : σ.symm (oddTask i) = ⟨n, by omega⟩ := Fin.ext h
      have h2 : oddTask i = σ ⟨n, by omega⟩ := by rw [← this]; simp
      rw [hn0] at h2
      have h3 : (oddTask i).val = 0 := by rw [h2]; simp
      omega
    have hn2 : (σ.symm (evenTask i)).val ≠ n := by
      intro h
      have : σ.symm (evenTask i) = ⟨n, by omega⟩ := Fin.ext h
      have h2 : evenTask i = σ ⟨n, by omega⟩ := by rw [← this]; simp
      rw [hn0] at h2
      have h3 : (evenTask i).val = 0 := by rw [h2]; simp
      omega
    have a1 := hvalA (oddTask i)
    have a2 := hvalB (oddTask i)
    have a3 := hvalA (evenTask i)
    have a4 := hvalB (evenTask i)
    simp only [hA, hB]
    have hlt1 := (σ.symm (oddTask i)).isLt
    have hlt2 := (σ.symm (evenTask i)).isLt
    omega
  · -- card A
    refine Eq.trans ?_ (card_lt_n n)
    exact Finset.card_equiv σ.symm (fun i => by simp [hA])
  · refine Eq.trans ?_ (card_gt_n n)
    exact Finset.card_equiv σ.symm (fun i => by simp [hB])

theorem cge_core {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (s : Fin (2 * n + 1) → ℝ) (hs : IsSchedule l s) :
    kStar l ≤ commonCost l M s ∧
      (commonCost l M s = kStar l →
        Ordered l M s ∧ NoGaps l s ∧ mid l s 0 = M ∧
          ∀ i : Fin n,
            (oddTask i ∈ setA l M s ∧ evenTask i ∈ setB l M s) ∨
              (evenTask i ∈ setA l M s ∧ oddTask i ∈ setB l M s)) := by
  refine ⟨(core_pos l hl0 hmono M s hs.2).1, fun hc => ?_⟩
  obtain ⟨h1, h2, h3, h4, _, _⟩ := struct_eq l hl0 hmono M s hs.2 hc
  exact ⟨h1, h2, h3, h4⟩

end GTWSched.NPC

open GTWSched.NPC


theorem solution {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (hM : M = (∑ i, l i) / 2)
    (s : Fin (2 * n + 1) → ℝ) (hs : IsSchedule l s) :
    kStar l ≤ commonCost l M s ∧
      (commonCost l M s = kStar l →
        Ordered l M s ∧ NoGaps l s ∧ mid l s 0 = M ∧
          ∀ i : Fin n,
            (oddTask i ∈ setA l M s ∧ evenTask i ∈ setB l M s) ∨
              (evenTask i ∈ setA l M s ∧ oddTask i ∈ setB l M s)) := by
  exact cge_core l M hl0 hmono s hs
