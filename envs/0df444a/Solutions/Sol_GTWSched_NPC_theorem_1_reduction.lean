-- Prove2me | solution 1 for GTWSched.NPC.theorem_1_reduction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:27:19.993992+00:00
-- url     : https://prove2.me/submissions/2c104bde-4318-4294-a525-6c4d9819b4fc

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems

open ProjSchedTW.Complexity

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

noncomputable def Rs (l' : ℕ → ℝ) (p : ℕ) : ℝ := ∑ t ∈ Finset.range p, l' (2*t+1)
noncomputable def Ls (l' : ℕ → ℝ) (p : ℕ) : ℝ := ∑ t ∈ Finset.range p, l' (2*t+2)
noncomputable def Sx (l' : ℕ → ℝ) (M : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then M - l' 0 / 2 else if k % 2 = 1 then M + l' 0 / 2 + Rs l' (k / 2)
  else M - l' 0 / 2 - Ls l' (k / 2)

lemma Sx_zero (l' : ℕ → ℝ) (M : ℝ) : Sx l' M 0 = M - l' 0 / 2 := by simp [Sx]
lemma Sx_odd (l' : ℕ → ℝ) (M : ℝ) (p : ℕ) : Sx l' M (2*p+1) = M + l' 0 / 2 + Rs l' p := by
  unfold Sx; rw [if_neg (by omega), if_pos (by omega), show (2*p+1)/2 = p by omega]
lemma Sx_even (l' : ℕ → ℝ) (M : ℝ) (p : ℕ) : Sx l' M (2*p+2) = M - l' 0 / 2 - Ls l' (p+1) := by
  unfold Sx; rw [if_neg (by omega), if_neg (by omega), show (2*p+2)/2 = p+1 by omega]

lemma Rs_succ (l' : ℕ → ℝ) (p : ℕ) : Rs l' (p+1) = Rs l' p + l' (2*p+1) := by
  unfold Rs; rw [Finset.sum_range_succ]
lemma Ls_succ (l' : ℕ → ℝ) (p : ℕ) : Ls l' (p+1) = Ls l' p + l' (2*p+2) := by
  unfold Ls; rw [Finset.sum_range_succ]

lemma Rs_nonneg (l' : ℕ → ℝ) (hnn : ∀ i, 0 ≤ l' i) (p : ℕ) : 0 ≤ Rs l' p :=
  Finset.sum_nonneg (fun t _ => hnn _)
lemma Ls_nonneg (l' : ℕ → ℝ) (hnn : ∀ i, 0 ≤ l' i) (p : ℕ) : 0 ≤ Ls l' p :=
  Finset.sum_nonneg (fun t _ => hnn _)
lemma Rs_mono (l' : ℕ → ℝ) (hnn : ∀ i, 0 ≤ l' i) {a b : ℕ} (h : a ≤ b) : Rs l' a ≤ Rs l' b :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun i _ _ => hnn _)
lemma Ls_mono (l' : ℕ → ℝ) (hnn : ∀ i, 0 ≤ l' i) {a b : ℕ} (h : a ≤ b) : Ls l' a ≤ Ls l' b :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun i _ _ => hnn _)

lemma Sx_before (l' : ℕ → ℝ) (M : ℝ) (hnn : ∀ i, 0 ≤ l' i) (k k' : ℕ) (hne : k ≠ k') :
    Sx l' M k + l' k ≤ Sx l' M k' ∨ Sx l' M k' + l' k' ≤ Sx l' M k := by
  have hb0r : ∀ p, Sx l' M 0 + l' 0 ≤ Sx l' M (2*p+1) := by
    intro p; rw [Sx_zero, Sx_odd]; linarith [Rs_nonneg l' hnn p]
  have hbl0 : ∀ p, Sx l' M (2*p+2) + l' (2*p+2) ≤ Sx l' M 0 := by
    intro p; rw [Sx_zero, Sx_even, Ls_succ]; linarith [Ls_nonneg l' hnn p]
  have hblr : ∀ p q, Sx l' M (2*p+2) + l' (2*p+2) ≤ Sx l' M (2*q+1) := by
    intro p q; rw [Sx_odd, Sx_even, Ls_succ]
    linarith [Ls_nonneg l' hnn p, Rs_nonneg l' hnn q, hnn 0]
  have hbrr : ∀ p q, p < q → Sx l' M (2*p+1) + l' (2*p+1) ≤ Sx l' M (2*q+1) := by
    intro p q h; rw [Sx_odd, Sx_odd]
    have := Rs_mono l' hnn (show p + 1 ≤ q by omega)
    rw [Rs_succ] at this; linarith
  have hbll : ∀ p q, q < p → Sx l' M (2*p+2) + l' (2*p+2) ≤ Sx l' M (2*q+2) := by
    intro p q h; rw [Sx_even, Sx_even, Ls_succ]
    have := Ls_mono l' hnn (show q + 1 ≤ p by omega)
    linarith
  by_cases h0 : k = 0
  · subst h0
    obtain ⟨q, rfl | rfl⟩ : ∃ q, k' = 2*q+1 ∨ k' = 2*q+2 := ⟨(k'-1)/2, by omega⟩
    · exact Or.inl (hb0r q)
    · exact Or.inr (hbl0 q)
  by_cases h0' : k' = 0
  · subst h0'
    obtain ⟨p, rfl | rfl⟩ : ∃ p, k = 2*p+1 ∨ k = 2*p+2 := ⟨(k-1)/2, by omega⟩
    · exact Or.inr (hb0r p)
    · exact Or.inl (hbl0 p)
  obtain ⟨p, rfl | rfl⟩ : ∃ p, k = 2*p+1 ∨ k = 2*p+2 := ⟨(k-1)/2, by omega⟩ <;>
  obtain ⟨q, rfl | rfl⟩ : ∃ q, k' = 2*q+1 ∨ k' = 2*q+2 := ⟨(k'-1)/2, by omega⟩
  · rcases lt_trichotomy p q with h | h | h
    · exact Or.inl (hbrr p q h)
    · exact absurd (by omega) hne
    · exact Or.inr (hbrr q p h)
  · exact Or.inr (hblr q p)
  · exact Or.inl (hblr p q)
  · rcases lt_trichotomy p q with h | h | h
    · exact Or.inr (hbll q p h)
    · exact absurd (by omega) hne
    · exact Or.inl (hbll p q h)

lemma sum_range_sum_range (f : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ Finset.range n, ∑ t ∈ Finset.range p, f t = ∑ t ∈ Finset.range n, ((n:ℝ) - 1 - t) * f t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have : ∑ t ∈ Finset.range n, (((n+1:ℕ):ℝ) - 1 - t) * f t =
        ∑ t ∈ Finset.range n, ((n:ℝ) - 1 - t) * f t + ∑ t ∈ Finset.range n, f t := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro t _; push_cast; ring
    rw [this]; push_cast; ring

lemma sum_range_odd_even (g : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (2*n+1), g k = g 0 + ∑ p ∈ Finset.range n, (g (2*p+1) + g (2*p+2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)+1 = (2*n+1)+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring_nf

lemma cost_Sx (n : ℕ) (l' : ℕ → ℝ) (M : ℝ) (hnn : ∀ i, 0 ≤ l' i) :
    ∑ k ∈ Finset.range (2 * n + 1), |M - (Sx l' M k + l' k / 2)| =
      (∑ j ∈ Finset.range n, (l' (2*j+2) + l' (2*j+1)) * ((n:ℝ) - j - 1/2)) + l' 0 * n := by
  rw [sum_range_odd_even]
  have g0 : |M - (Sx l' M 0 + l' 0 / 2)| = 0 := by rw [Sx_zero]; simp
  have g1 : ∀ p, |M - (Sx l' M (2*p+1) + l' (2*p+1) / 2)| = l' 0 / 2 + Rs l' p + l' (2*p+1) / 2 := by
    intro p
    rw [Sx_odd, abs_of_nonpos (by linarith [Rs_nonneg l' hnn p, hnn 0, hnn (2*p+1)])]
    ring
  have g2 : ∀ p, |M - (Sx l' M (2*p+2) + l' (2*p+2) / 2)| = l' 0 / 2 + Ls l' p + l' (2*p+2) / 2 := by
    intro p
    rw [Sx_even, Ls_succ, abs_of_nonneg (by linarith [Ls_nonneg l' hnn p, hnn 0, hnn (2*p+2)])]
    ring
  rw [g0]
  simp only [g1, g2]
  have e1 : ∑ p ∈ Finset.range n, (l' 0 / 2 + Rs l' p + l' (2*p+1) / 2 + (l' 0 / 2 + Ls l' p + l' (2*p+2) / 2))
      = ∑ p ∈ Finset.range n, (l' 0) + ∑ p ∈ Finset.range n, Rs l' p + ∑ p ∈ Finset.range n, Ls l' p
        + ∑ p ∈ Finset.range n, (l' (2*p+1) + l' (2*p+2)) / 2 := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro p _; ring
  rw [e1]
  have e2 : ∑ p ∈ Finset.range n, Rs l' p = ∑ t ∈ Finset.range n, ((n:ℝ) - 1 - t) * l' (2*t+1) :=
    sum_range_sum_range (fun t => l' (2*t+1)) n
  have e3 : ∑ p ∈ Finset.range n, Ls l' p = ∑ t ∈ Finset.range n, ((n:ℝ) - 1 - t) * l' (2*t+2) :=
    sum_range_sum_range (fun t => l' (2*t+2)) n
  have e4 : ∑ j ∈ Finset.range n, (l' (2*j+2) + l' (2*j+1)) * ((n:ℝ) - j - 1/2) =
      ∑ t ∈ Finset.range n, ((n:ℝ) - 1 - t) * l' (2*t+1) + ∑ t ∈ Finset.range n, ((n:ℝ) - 1 - t) * l' (2*t+2)
      + ∑ p ∈ Finset.range n, (l' (2*p+1) + l' (2*p+2)) / 2 := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro p _; ring
  rw [e2, e3, e4]
  simp
  ring

noncomputable def lsw (lx : ℕ → ℝ) (Q : ℕ → Prop) [DecidablePred Q] (u : ℕ) : ℝ :=
  if u = 0 then lx 0 else if u % 2 = 1 then (if Q (u - 1) then lx (u + 1) else lx u)
  else (if Q (u - 2) then lx (u - 1) else lx u)

def pislot (Q : ℕ → Prop) [DecidablePred Q] (t : ℕ) : ℕ :=
  if t = 0 then 0 else if t % 2 = 1 then (if Q (t - 1) then t + 1 else t)
  else (if Q (t - 1) then t else t - 1)

section SW
variable (lx : ℕ → ℝ) (Q : ℕ → Prop) [DecidablePred Q]

lemma lsw_zero : lsw lx Q 0 = lx 0 := by simp [lsw]

lemma lsw_odd (i : ℕ) : lsw lx Q (2*i+1) = if Q (2*i) then lx (2*i+2) else lx (2*i+1) := by
  unfold lsw
  rw [if_neg (by omega), if_pos (by omega)]
  simp

lemma lsw_even (i : ℕ) : lsw lx Q (2*i+2) = if Q (2*i) then lx (2*i+1) else lx (2*i+2) := by
  unfold lsw
  rw [if_neg (by omega), if_neg (by omega)]
  simp

lemma pi_zero : pislot Q 0 = 0 := by simp [pislot]

lemma pi_odd (i : ℕ) : pislot Q (2*i+1) = if Q (2*i) then 2*i+2 else 2*i+1 := by
  unfold pislot
  rw [if_neg (by omega), if_pos (by omega)]
  simp

lemma pi_even (i : ℕ) : pislot Q (2*i+2) = if Q (2*i+1) then 2*i+2 else 2*i+1 := by
  unfold pislot
  rw [if_neg (by omega), if_neg (by omega)]
  have : 2 * i + 2 - 1 = 2 * i + 1 := by omega
  rw [this]

lemma pi_lt (n : ℕ) (t : ℕ) (ht : t < 2 * n + 1) : pislot Q t < 2 * n + 1 := by
  rcases (show t = 0 ∨ (∃ i, t = 2*i+1) ∨ (∃ i, t = 2*i+2) by
    rcases Nat.eq_zero_or_pos t with h | h
    · left; exact h
    · right; rcases Nat.even_or_odd' t with ⟨k, hk | hk⟩
      · right; exact ⟨k-1, by omega⟩
      · left; exact ⟨k, hk⟩) with h | ⟨i, h⟩ | ⟨i, h⟩
  · subst h; rw [pi_zero]; omega
  · subst h; rw [pi_odd]; split_ifs <;> omega
  · subst h; rw [pi_even]; split_ifs <;> omega

lemma pi_invol (n : ℕ) (hQ : ∀ i < n, Q (2*i) ↔ ¬ Q (2*i+1)) (t : ℕ) (ht : t < 2 * n + 1) :
    pislot Q (pislot Q t) = t := by
  rcases (show t = 0 ∨ (∃ i, t = 2*i+1) ∨ (∃ i, t = 2*i+2) by
    rcases Nat.eq_zero_or_pos t with h | h
    · left; exact h
    · right; rcases Nat.even_or_odd' t with ⟨k, hk | hk⟩
      · right; exact ⟨k-1, by omega⟩
      · left; exact ⟨k, hk⟩) with h | ⟨i, h⟩ | ⟨i, h⟩
  · subst h; rw [pi_zero, pi_zero]
  · subst h
    have hi : i < n := by omega
    have hq := hQ i hi
    by_cases hc : Q (2*i)
    · rw [pi_odd, if_pos hc, pi_even, if_neg (hq.mp hc)]
    · rw [pi_odd, if_neg hc, pi_odd, if_neg hc]
  · subst h
    have hi : i < n := by omega
    have hq := hQ i hi
    by_cases hc : Q (2*i+1)
    · rw [pi_even, if_pos hc, pi_even, if_pos hc]
    · have hc' : Q (2*i) := by by_contra h'; exact hc (by tauto)
      rw [pi_even, if_neg hc, pi_odd, if_pos hc']

lemma lsw_pi (n : ℕ) (hQ : ∀ i < n, Q (2*i) ↔ ¬ Q (2*i+1)) (t : ℕ) (ht : t < 2 * n + 1) :
    lsw lx Q (pislot Q t) = lx t := by
  rcases (show t = 0 ∨ (∃ i, t = 2*i+1) ∨ (∃ i, t = 2*i+2) by
    rcases Nat.eq_zero_or_pos t with h | h
    · left; exact h
    · right; rcases Nat.even_or_odd' t with ⟨k, hk | hk⟩
      · right; exact ⟨k-1, by omega⟩
      · left; exact ⟨k, hk⟩) with h | ⟨i, h⟩ | ⟨i, h⟩
  · subst h; rw [pi_zero, lsw_zero]
  · subst h
    have hi : i < n := by omega
    have hq := hQ i hi
    by_cases hc : Q (2*i)
    · rw [pi_odd, if_pos hc, lsw_even, if_pos hc]
    · rw [pi_odd, if_neg hc, lsw_odd, if_neg hc]
  · subst h
    have hi : i < n := by omega
    have hq := hQ i hi
    by_cases hc : Q (2*i+1)
    · have hc' : ¬ Q (2*i) := fun h' => (hq.mp h') hc
      rw [pi_even, if_pos hc, lsw_even, if_neg hc']
    · have hc' : Q (2*i) := by by_contra h'; exact hc (by tauto)
      rw [pi_even, if_neg hc, lsw_odd, if_pos hc']

lemma lsw_pair (n : ℕ) (hQ : ∀ i < n, Q (2*i) ↔ ¬ Q (2*i+1)) (i : ℕ) :
    lsw lx Q (2*i+2) + lsw lx Q (2*i+1) = lx (2*i+2) + lx (2*i+1) := by
  rw [lsw_even, lsw_odd]
  by_cases hc : Q (2*i)
  · rw [if_pos hc, if_pos hc]; ring
  · rw [if_neg hc, if_neg hc]

end SW

theorem construct_sched {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (hl0 : 0 < l 0) (hmono : StrictMono l)
    (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ i < n, Q (2*i) ↔ ¬ Q (2*i+1))
    (hbal : Ls (lsw (extF l) Q) n = Rs (lsw (extF l) Q) n) (M : ℝ) (hM : M = (∑ i, l i) / 2) :
    ∃ s : Fin (2 * n + 1) → ℝ, IsSchedule l s ∧ commonCost l M s = kStar l ∧
      ∀ t, s t + l t ≤ ∑ i, l i := by
  set lx := extF l with hlx
  set l2 := lsw lx Q with hl2
  have hlxnn : ∀ i, 0 ≤ lx i := by
    intro i; show 0 ≤ extF l i; unfold extF
    split_ifs with h
    · exact (l_pos l hl0 hmono _).le
    · exact le_refl _
  have hnn2 : ∀ u, 0 ≤ l2 u := by
    intro u; simp only [hl2, lsw]
    split_ifs <;> exact hlxnn _
  have hlt : ∀ t : Fin (2 * n + 1), l t = l2 (pislot Q t.val) := by
    intro t
    rw [hl2, lsw_pi lx Q n hQ t.val t.isLt, hlx, extF_val]
  have hL : ∑ i, l i = l 0 + 2 * Rs l2 n := by
    have h1 : ∑ i, l i = Lsum lx (2 * n + 1) := by
      unfold Lsum
      rw [Finset.sum_range (fun i => lx i)]
      exact Finset.sum_congr rfl (fun i _ => (extF_val l i).symm)
    rw [h1, Lsum_odd]
    have h2 : ∑ j ∈ Finset.range n, (lx (2*j+1) + lx (2*j+2)) = Rs l2 n + Ls l2 n := by
      unfold Rs Ls
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      have := lsw_pair lx Q n hQ j
      linarith
    rw [h2, hbal]
    have : lx 0 = l 0 := by rw [hlx]; exact extF_val l 0
    rw [this]; ring
  have hB0 : 0 ≤ Rs l2 n := Rs_nonneg l2 hnn2 n
  have hl2zero : l2 0 = l 0 := by rw [hl2, lsw_zero]; exact extF_val l 0
  have hbd : ∀ u, u < 2 * n + 1 → 0 ≤ Sx l2 M u ∧ Sx l2 M u + l2 u ≤ ∑ i, l i := by
    intro u hu
    have hM' : M = l 0 / 2 + Rs l2 n := by rw [hM, hL]; ring
    rcases (show u = 0 ∨ (∃ i, u = 2*i+1) ∨ (∃ i, u = 2*i+2) by
      rcases Nat.eq_zero_or_pos u with h | h
      · left; exact h
      · right; rcases Nat.even_or_odd' u with ⟨k, hk | hk⟩
        · right; exact ⟨k-1, by omega⟩
        · left; exact ⟨k, hk⟩) with h | ⟨i, h⟩ | ⟨i, h⟩
    · subst h; rw [Sx_zero, hl2zero]; constructor <;> linarith
    · subst h
      have hmon := Rs_mono l2 hnn2 (show i + 1 ≤ n by omega)
      have hs := Rs_succ l2 i
      rw [Sx_odd, hl2zero]
      have := Rs_nonneg l2 hnn2 i
      have := hnn2 (2*i+1)
      constructor
      · linarith
      · rw [hL]; linarith
    · subst h
      have hmon := Ls_mono l2 hnn2 (show i + 1 ≤ n by omega)
      have hs := Ls_succ l2 i
      rw [Sx_even, hl2zero]
      have := Ls_nonneg l2 hnn2 i
      have := hnn2 (2*i+2)
      constructor
      · linarith
      · rw [hL]; linarith
  refine ⟨fun t => Sx l2 M (pislot Q t.val), ⟨?_, ?_⟩, ?_, ?_⟩
  · intro t; exact (hbd _ (pi_lt Q n t.val t.isLt)).1
  · intro i j hij
    have hne : pislot Q i.val ≠ pislot Q j.val := by
      intro h
      apply hij
      apply Fin.ext
      have := congrArg (pislot Q) h
      rwa [pi_invol Q n hQ i.val i.isLt, pi_invol Q n hQ j.val j.isLt] at this
    have := Sx_before l2 M hnn2 _ _ hne
    rw [hlt i, hlt j]
    exact this
  · -- cost
    have hcost : commonCost l M (fun t => Sx l2 M (pislot Q t.val)) =
        ∑ t ∈ Finset.range (2 * n + 1), |M - (Sx l2 M (pislot Q t) + l2 (pislot Q t) / 2)| := by
      unfold commonCost
      rw [Finset.sum_range (fun t => |M - (Sx l2 M (pislot Q t) + l2 (pislot Q t) / 2)|)]
      apply Finset.sum_congr rfl
      intro t _
      unfold mid
      rw [hlt t]
    rw [hcost]
    have hre : ∑ t ∈ Finset.range (2 * n + 1), |M - (Sx l2 M (pislot Q t) + l2 (pislot Q t) / 2)| =
        ∑ u ∈ Finset.range (2 * n + 1), |M - (Sx l2 M u + l2 u / 2)| := by
      apply Finset.sum_nbij (fun t => pislot Q t)
      · intro a ha; exact Finset.mem_range.mpr (pi_lt Q n a (Finset.mem_range.mp ha))
      · intro a ha b hb h
        have := congrArg (pislot Q) h
        simp only at this
        rwa [pi_invol Q n hQ a (Finset.mem_range.mp ha), pi_invol Q n hQ b (Finset.mem_range.mp hb)] at this
      · intro u hu
        exact ⟨pislot Q u, Finset.mem_coe.mpr (Finset.mem_range.mpr (pi_lt Q n u (Finset.mem_range.mp hu))),
          pi_invol Q n hQ u (Finset.mem_range.mp hu)⟩
      · intro a _; rfl
    rw [hre, cost_Sx n l2 M hnn2, kStar_eq_Gstar, Gstar_eq]
    rw [show l2 0 = extF l 0 from lsw_zero lx Q]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hl2, lsw_pair lx Q n hQ j]
  · intro t
    rw [hlt t]
    exact (hbd _ (pi_lt Q n t.val t.isLt)).2

noncomputable def dLenH (x : List ℕ) (i : Fin (2 * (x.length / 2) + 1)) : ℝ := dLen x i.castSucc

lemma dLen_last_eq (x : List ℕ) : dLen x (Fin.last (2 * (x.length / 2) + 1)) = 2 := by
  unfold dLen; simp

lemma dLenH_zero (x : List ℕ) : dLenH x 0 = (x.getD 0 0 : ℝ) - 1 := by
  unfold dLenH dLen; simp

lemma dLenH_pos (x : List ℕ) (i : Fin (2 * (x.length / 2) + 1)) (hi : 0 < i.val) :
    dLenH x i = (x.getD (i.val - 1) 0 : ℝ) := by
  unfold dLenH dLen
  have hlt := i.isLt
  simp only [Fin.val_castSucc]
  rw [if_neg (by omega), if_pos (by omega)]

lemma dK_eq (x : List ℕ) : dK x = kStar (dLenH x) := rfl

lemma dM_eq (x : List ℕ) : dM x = (∑ i, dLenH x i) / 2 := by
  unfold dM dLenH
  rw [Finset.sum_div]

lemma dMid_cs (x : List ℕ) (i : Fin (2 * (x.length / 2) + 1)) : dMid x i.castSucc = dM x := by
  unfold dMid
  have hlt := i.isLt
  rw [if_pos (by simp only [Fin.val_castSucc]; omega)]

lemma dMid_last (x : List ℕ) : dMid x (Fin.last _) = (∑ i, dLenH x i) + 1 := by
  unfold dMid
  rw [if_neg (by simp), dLen_last_eq, dM_eq]
  ring

lemma getD_lt_of_pairwise (x : List ℕ) (hp : x.Pairwise (· < ·)) (a b : ℕ) (hab : a < b)
    (hb : b < x.length) : x.getD a 0 < x.getD b 0 := by
  have h := List.pairwise_iff_getElem.mp hp a b (by omega) hb hab
  rw [List.getD_eq_getElem x 0 (by omega), List.getD_eq_getElem x 0 hb]
  exact h

lemma dLenH_strictMono (x : List ℕ) (hx : EOInstance x) (hx1 : 1 < x.getD 0 0) :
    StrictMono (dLenH x) := by
  obtain ⟨hev, hpos, hallpos, hpw⟩ := hx
  have hlen : x.length = 2 * (x.length / 2) := by
    obtain ⟨k, hk⟩ := hev; omega
  intro i j hij
  have hij' : i.val < j.val := hij
  have hjlt := j.isLt
  have hjx : j.val - 1 < x.length := by omega
  rcases Nat.eq_zero_or_pos i.val with h0 | h0
  · have hi0 : i = 0 := Fin.ext h0
    rw [hi0, dLenH_zero, dLenH_pos x j (by omega)]
    have : x.getD 0 0 ≤ x.getD (j.val - 1) 0 := by
      rcases Nat.eq_zero_or_pos (j.val - 1) with h | h
      · rw [h]
      · exact (getD_lt_of_pairwise x hpw 0 (j.val - 1) h hjx).le
    have : (x.getD 0 0 : ℝ) ≤ x.getD (j.val - 1) 0 := by exact_mod_cast this
    linarith
  · rw [dLenH_pos x i h0, dLenH_pos x j (by omega)]
    have := getD_lt_of_pairwise x hpw (i.val - 1) (j.val - 1) (by omega) hjx
    exact_mod_cast this

lemma dLenH_zero_pos (x : List ℕ) (hx1 : 1 < x.getD 0 0) : 0 < dLenH x 0 := by
  rw [dLenH_zero]
  have : (1:ℝ) < (x.getD 0 0 : ℝ) := by exact_mod_cast hx1
  linarith

lemma EO_len (x : List ℕ) (hx : EOInstance x) : x.length = 2 * (x.length / 2) := by
  obtain ⟨⟨k, hk⟩, _⟩ := hx; omega


section L1
open Classical


lemma eoAux_length (ys : List ℕ) : ∀ a, (eoAux a ys).length = 2 * ys.length := by
  induction ys with
  | nil => intro a; simp [eoAux]
  | cons y ys ih => intro a; simp [eoAux, ih]; ring

lemma eoAux_ge (ys : List ℕ) : ∀ a, ∀ v ∈ eoAux a ys, a ≤ v := by
  induction ys with
  | nil => intro a v hv; simp [eoAux] at hv
  | cons y ys ih =>
    intro a v hv
    simp only [eoAux, List.mem_cons] at hv
    rcases hv with rfl | rfl | hv
    · exact le_rfl
    · omega
    · have := ih (a+y+1) v hv; omega

lemma eoAux_pairwise (ys : List ℕ) (hy : ∀ v ∈ ys, 1 < v) :
    ∀ a, (eoAux a ys).Pairwise (· < ·) := by
  induction ys with
  | nil => intro a; simp [eoAux]
  | cons y ys ih =>
    intro a
    have hy0 : 1 < y := hy y (by simp)
    have hrest := ih (fun v hv => hy v (by simp [hv])) (a+y+1)
    simp only [eoAux]
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ hrest)
    · intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · omega
      · have := eoAux_ge ys (a+y+1) b hb; omega
    · intro b hb
      have := eoAux_ge ys (a+y+1) b hb; omega

lemma eoAux_getD (ys : List ℕ) : ∀ (a i : ℕ), i < ys.length →
    (eoAux a ys).getD (2*i) 0 = a + ∑ j ∈ Finset.range i, (ys.getD j 0 + 1) ∧
    (eoAux a ys).getD (2*i+1) 0 = a + ∑ j ∈ Finset.range i, (ys.getD j 0 + 1) + ys.getD i 0 := by
  induction ys with
  | nil => intro a i hi; simp at hi
  | cons y ys ih =>
    intro a i hi
    cases i with
    | zero => simp [eoAux]
    | succ i =>
      have hi' : i < ys.length := by simpa using hi
      obtain ⟨h1, h2⟩ := ih (a+y+1) i hi'
      rw [Finset.sum_range_succ']
      constructor
      · have : (eoAux a (y :: ys)).getD (2*(i+1)) 0 = (eoAux (a+y+1) ys).getD (2*i) 0 := by
          simp [eoAux, show 2*(i+1) = 2*i+1+1 by ring]
        rw [this, h1]; simp; omega
      · have : (eoAux a (y :: ys)).getD (2*(i+1)+1) 0 = (eoAux (a+y+1) ys).getD (2*i+1) 0 := by
          simp [eoAux, show 2*(i+1)+1 = 2*i+1+1+1 by ring]
        rw [this, h2]; simp; omega

lemma sum_fin_pred (l : List ℕ) (A : Finset (Fin l.length)) :
    ∑ i ∈ A, l.get i = ∑ p ∈ Finset.range l.length,
      if (∃ h : p < l.length, (⟨p, h⟩ : Fin l.length) ∈ A) then l.getD p 0 else 0 := by
  rw [Finset.sum_range (fun p => if (∃ h : p < l.length, (⟨p, h⟩ : Fin l.length) ∈ A) then l.getD p 0 else 0)]
  have key : ∀ i : Fin l.length, (if (∃ h : i.val < l.length, (⟨i.val, h⟩ : Fin l.length) ∈ A) then l.getD i.val 0 else 0)
      = if i ∈ A then l.get i else 0 := by
    intro i
    have e1 : (∃ h : i.val < l.length, (⟨i.val, h⟩ : Fin l.length) ∈ A) ↔ i ∈ A := by
      constructor
      · rintro ⟨h, hh⟩; exact hh
      · intro h; exact ⟨i.isLt, h⟩
    have e2 : l.getD i.val 0 = l.get i := by simp [List.getD_eq_getElem?_getD]
    by_cases hi : i ∈ A
    · rw [if_pos (e1.mpr hi), if_pos hi, e2]
    · rw [if_neg (fun h => hi (e1.mp h)), if_neg hi]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  rw [Finset.sum_ite_mem]
  simp

lemma sum_range_pairs (h : ℕ → ℕ) (n : ℕ) :
    ∑ p ∈ Finset.range (2*n), h p = ∑ i ∈ Finset.range n, (h (2*i) + h (2*i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring


lemma sum_cancel (L R g h : ℕ → ℕ) (n : ℕ)
    (term : ∀ i ∈ Finset.range n, L i + g i = R i + h i) :
    (∑ i ∈ Finset.range n, L i = ∑ i ∈ Finset.range n, R i) ↔
      (∑ i ∈ Finset.range n, h i = ∑ i ∈ Finset.range n, g i) := by
  have e1 := Finset.sum_congr rfl term
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at e1
  constructor <;> intro h <;> omega

lemma core_alg (x : List ℕ) (n : ℕ) (hlen : x.length = 2*n) (yv : ℕ → ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (hQ : ∀ i < n, Q (2*i) ↔ ¬ Q (2*i+1))
    (hxo : ∀ i < n, x.getD (2*i+1) 0 = x.getD (2*i) 0 + yv i) :
    (∑ p ∈ Finset.range x.length, (if Q p then x.getD p 0 else 0) =
      ∑ p ∈ Finset.range x.length, (if ¬ Q p then x.getD p 0 else 0)) ↔
    (∑ i ∈ Finset.range n, (if Q (2*i+1) then yv i else 0) =
      ∑ i ∈ Finset.range n, (if ¬ Q (2*i+1) then yv i else 0)) := by
  rw [hlen, sum_range_pairs (fun p => if Q p then x.getD p 0 else 0),
    sum_range_pairs (fun p => if ¬ Q p then x.getD p 0 else 0)]
  have term : ∀ i ∈ Finset.range n,
      ((if Q (2*i) then x.getD (2*i) 0 else 0) + (if Q (2*i+1) then x.getD (2*i+1) 0 else 0))
        + (if ¬ Q (2*i+1) then yv i else 0)
      = ((if ¬ Q (2*i) then x.getD (2*i) 0 else 0) + (if ¬ Q (2*i+1) then x.getD (2*i+1) 0 else 0))
        + (if Q (2*i+1) then yv i else 0) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have h1 := hxo i hi'
    have h2 := hQ i hi'
    by_cases h : Q (2*i+1)
    · have h3 : ¬ Q (2*i) := fun h4 => (h2.mp h4) h
      simp only [h, h3, not_true_eq_false, not_false_eq_true, if_true, if_false]
      omega
    · have h3 : Q (2*i) := h2.mpr h
      simp only [h, h3, not_true_eq_false, not_false_eq_true, if_true, if_false]
      omega
  exact sum_cancel _ _ _ _ n term


lemma pred_sum_iff (l : List ℕ) (g : ℕ → Prop) (A : Finset (Fin l.length))
    (hA : ∀ p (h : p < l.length), (⟨p, h⟩ : Fin l.length) ∈ A ↔ g p) :
    ∑ i ∈ A, l.get i = ∑ p ∈ Finset.range l.length, (if g p then l.getD p 0 else 0) ∧
    ∑ i ∈ Aᶜ, l.get i = ∑ p ∈ Finset.range l.length, (if ¬ g p then l.getD p 0 else 0) := by
  constructor
  · rw [sum_fin_pred]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.mem_range.mp hp
    have : (∃ h : p < l.length, (⟨p, h⟩ : Fin l.length) ∈ A) ↔ g p :=
      ⟨fun ⟨h, hh⟩ => (hA p h).mp hh, fun hg => ⟨hp', (hA p hp').mpr hg⟩⟩
    by_cases hg : g p
    · rw [if_pos (this.mpr hg), if_pos hg]
    · rw [if_neg (fun h => hg (this.mp h)), if_neg hg]
  · rw [sum_fin_pred]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.mem_range.mp hp
    have : (∃ h : p < l.length, (⟨p, h⟩ : Fin l.length) ∈ Aᶜ) ↔ ¬ g p := by
      constructor
      · rintro ⟨h, hh⟩ hg
        exact (Finset.mem_compl.mp hh) ((hA p h).mpr hg)
      · intro hg
        exact ⟨hp', Finset.mem_compl.mpr (fun hh => hg ((hA p hp').mp hh))⟩
    by_cases hg : g p
    · rw [if_neg (fun h => (this.mp h) hg), if_neg (not_not.mpr hg)]
    · rw [if_pos (this.mpr hg), if_pos hg]


lemma eoyes_pred (x : List ℕ) : EOYes x ↔ ∃ Q : ℕ → Prop,
    (∀ i, 2 * i + 1 < x.length → (Q (2 * i) ↔ ¬ Q (2 * i + 1))) ∧
    ∑ p ∈ Finset.range x.length, (if Q p then x.getD p 0 else 0) =
    ∑ p ∈ Finset.range x.length, (if ¬ Q p then x.getD p 0 else 0) := by
  constructor
  · rintro ⟨X1, hpair, hsum⟩
    refine ⟨fun p => ∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1, ?_, ?_⟩
    · intro i hi
      have h1 : 2*i < x.length := by omega
      have := hpair ⟨2*i, h1⟩ ⟨2*i+1, hi⟩ (by simp [Fin.ext_iff]) (by simp; omega)
      constructor
      · rintro ⟨h, hh⟩ ⟨h', hh'⟩
        exact (this.mp hh) hh'
      · intro hn
        have hn' : (⟨2*i+1, hi⟩ : Fin x.length) ∉ X1 := fun hh => hn ⟨hi, hh⟩
        exact ⟨h1, this.mpr hn'⟩
    · have := pred_sum_iff x (fun p => ∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1) X1
        (fun p h => ⟨fun hh => ⟨h, hh⟩, fun ⟨h', hh⟩ => hh⟩)
      rw [← this.1, ← this.2]; exact hsum
  · rintro ⟨Q, hQ, hsum⟩
    refine ⟨Finset.univ.filter (fun p : Fin x.length => Q p.val), ?_, ?_⟩
    · intro p q hpq hdiv
      have hne : p.val ≠ q.val := fun h => hpq (Fin.ext h)
      have hq := q.isLt
      have hp := p.isLt
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      obtain ⟨i, hi⟩ : ∃ i, i = p.val / 2 := ⟨_, rfl⟩
      rcases (show (p.val = 2 * i ∧ q.val = 2 * i + 1) ∨ (p.val = 2 * i + 1 ∧ q.val = 2 * i) by
        omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have key := hQ i (by omega)
        rw [h1, h2]; exact key
      · have key := hQ i (by omega)
        rw [h1, h2]; tauto
    · have := pred_sum_iff x Q (Finset.univ.filter (fun p : Fin x.length => Q p.val))
        (fun p h => by simp)
      rw [this.1, this.2]; exact hsum
end L1

lemma lx_succ (x : List ℕ) (t : ℕ) (ht : t < 2 * (x.length / 2)) :
    extF (dLenH x) (t + 1) = (x.getD t 0 : ℝ) := by
  have h : t + 1 < 2 * (x.length / 2) + 1 := by omega
  simp only [extF, dif_pos h]
  rw [dLenH_pos x ⟨t + 1, h⟩ (by simp)]
  simp

theorem eo_to_td (x : List ℕ) (hx : EOInstance x) (hx1 : 1 < x.getD 0 0) (h : EOYes x) :
    TDYesReal (dLen x) (dMid x) (dK x) := by
  classical
  have hlen := EO_len x hx
  obtain ⟨Q, hQ, hsum⟩ := (eoyes_pred x).mp h
  set n := x.length / 2 with hn
  have hQ' : ∀ i < n, Q (2*i) ↔ ¬ Q (2*i+1) := fun i hi => hQ i (by omega)
  have hmono := dLenH_strictMono x hx hx1
  have hl0 := dLenH_zero_pos x hx1
  -- balance
  have hbal : Ls (lsw (extF (dLenH x)) Q) n = Rs (lsw (extF (dLenH x)) Q) n := by
    have hs2 := sum_range_pairs (fun p => if Q p then x.getD p 0 else 0) n
    have hs3 := sum_range_pairs (fun p => if ¬ Q p then x.getD p 0 else 0) n
    rw [hlen, hs2, hs3] at hsum
    have hsumR : ∑ i ∈ Finset.range n, (((if Q (2*i) then x.getD (2*i) 0 else 0 : ℕ) : ℝ) +
        ((if Q (2*i+1) then x.getD (2*i+1) 0 else 0 : ℕ) : ℝ)) =
        ∑ i ∈ Finset.range n, (((if ¬ Q (2*i) then x.getD (2*i) 0 else 0 : ℕ) : ℝ) +
        ((if ¬ Q (2*i+1) then x.getD (2*i+1) 0 else 0 : ℕ) : ℝ)) := by
      have := congrArg (fun m : ℕ => (m : ℝ)) hsum
      simp only [Nat.cast_sum, Nat.cast_add] at this
      exact this
    unfold Ls Rs
    have e1 : ∀ i ∈ Finset.range n, lsw (extF (dLenH x)) Q (2*i+2) =
        ((if Q (2*i) then x.getD (2*i) 0 else 0 : ℕ) : ℝ) +
        ((if Q (2*i+1) then x.getD (2*i+1) 0 else 0 : ℕ) : ℝ) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hq := hQ' i hi'
      rw [lsw_even, lx_succ x (2*i) (by omega), show 2 * i + 2 = (2 * i + 1) + 1 by ring,
        lx_succ x (2*i+1) (by omega)]
      by_cases hc : Q (2*i)
      · have : ¬ Q (2*i+1) := hq.mp hc
        simp [hc, this]
      · have : Q (2*i+1) := by by_contra h'; exact hc (hq.mpr h')
        simp [hc, this]
    have e2 : ∀ i ∈ Finset.range n, lsw (extF (dLenH x)) Q (2*i+1) =
        ((if ¬ Q (2*i) then x.getD (2*i) 0 else 0 : ℕ) : ℝ) +
        ((if ¬ Q (2*i+1) then x.getD (2*i+1) 0 else 0 : ℕ) : ℝ) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hq := hQ' i hi'
      rw [lsw_odd, lx_succ x (2*i) (by omega), show 2 * i + 2 = (2 * i + 1) + 1 by ring,
        lx_succ x (2*i+1) (by omega)]
      by_cases hc : Q (2*i)
      · have : ¬ Q (2*i+1) := hq.mp hc
        simp [hc, this]
      · have : Q (2*i+1) := by by_contra h'; exact hc (hq.mpr h')
        simp [hc, this]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
    exact hsumR
  obtain ⟨s, hs, hcost, hend⟩ := construct_sched (dLenH x) hl0 hmono Q hQ' hbal (dM x) (dM_eq x)
  have hLnn : 0 ≤ ∑ i, dLenH x i := Finset.sum_nonneg (fun i _ => (l_pos _ hl0 hmono i).le)
  refine ⟨Fin.snoc (α := fun _ => ℝ) s (∑ i, dLenH x i), ⟨?_, ?_⟩, ?_⟩
  · intro j
    refine Fin.lastCases ?_ (fun a => ?_) j
    · simp [Fin.snoc_last]; exact hLnn
    · simp only [Fin.snoc_castSucc]; exact hs.1 a
  · intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast b =>
        right
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact hend b
    | cast a =>
      induction j using Fin.lastCases with
      | last =>
        left
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact hend a
      | cast b =>
        have hab : a ≠ b := fun h => hij (by rw [h])
        simp only [Fin.snoc_castSucc]
        exact hs.2 a b hab
  · unfold midCost
    have e : ∑ j : Fin (2 * n + 1 + 1), |mid (dLen x) (Fin.snoc (α := fun _ => ℝ) s (∑ i, dLenH x i)) j - dMid x j| =
        ∑ a : Fin (2 * n + 1), |mid (dLen x) (Fin.snoc (α := fun _ => ℝ) s (∑ i, dLenH x i)) a.castSucc - dMid x a.castSucc| +
        |mid (dLen x) (Fin.snoc (α := fun _ => ℝ) s (∑ i, dLenH x i)) (Fin.last _) - dMid x (Fin.last _)| :=
      Fin.sum_univ_castSucc _
    refine le_of_eq (e.trans ?_)
    have e1 : ∀ a : Fin (2 * n + 1), |mid (dLen x) (Fin.snoc (α := fun _ => ℝ) s (∑ i, dLenH x i)) a.castSucc - dMid x a.castSucc|
        = |dM x - mid (dLenH x) s a| := by
      intro a
      rw [dMid_cs, abs_sub_comm]
      unfold mid
      simp only [Fin.snoc_castSucc]
      rfl
    have e2 : |mid (dLen x) (Fin.snoc (α := fun _ => ℝ) s (∑ i, dLenH x i)) (Fin.last _) - dMid x (Fin.last _)| = 0 := by
      rw [dMid_last]
      unfold mid
      rw [Fin.snoc_last, dLen_last_eq]
      simp
    rw [e2, add_zero, Finset.sum_congr rfl (fun a _ => e1 a)]
    exact hcost

noncomputable def lamg {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (σ : Equiv.Perm (Fin (2 * n + 1))) (q : ℕ) : ℝ :=
  if h : q < 2 * n + 1 then l (σ ⟨q, h⟩) else 0

noncomputable def sg {n : ℕ} (s : Fin (2 * n + 1) → ℝ) (σ : Equiv.Perm (Fin (2 * n + 1))) (q : ℕ) : ℝ :=
  if h : q < 2 * n + 1 then s (σ ⟨q, h⟩) else 0

lemma pair_split {n : ℕ} (σ : Equiv.Perm (Fin (2 * n + 1))) (hn0 : σ ⟨n, by omega⟩ = 0)
    (hodd : ∀ q : Fin (2 * n + 1), n < q.val →
        (σ q).val = 2 * (q.val - n) - 1 ∨ (σ q).val = 2 * (q.val - n))
    (hlow : ∀ q : Fin (2 * n + 1), q.val < n →
        (σ q).val = 2 * (n - q.val) - 1 ∨ (σ q).val = 2 * (n - q.val)) (i : Fin n) :
    ((σ.symm (oddTask i)).val < n ↔ ¬ (σ.symm (evenTask i)).val < n) := by
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
  have hlt1 := (σ.symm (oddTask i)).isLt
  have hlt2 := (σ.symm (evenTask i)).isLt
  omega

lemma claimA {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (σ : Equiv.Perm (Fin (2 * n + 1)))
    (hn0 : σ ⟨n, by omega⟩ = 0) :
    ∑ i : Fin (2 * n), (if (σ.symm (Fin.succ i)).val < n then l (Fin.succ i) else 0) =
      ∑ q ∈ Finset.range n, lamg l σ q := by
  classical
  set G : Fin (2 * n + 1) → ℝ := fun t => if (σ.symm t).val < n then l t else 0 with hG
  have h1 : ∑ t, G t = G 0 + ∑ i : Fin (2 * n), G (Fin.succ i) := Fin.sum_univ_succ _
  have h2 : G 0 = 0 := by
    have : σ.symm 0 = ⟨n, by omega⟩ := by rw [← hn0]; simp
    simp [hG, this]
  have h3 : ∑ t, G t = ∑ q ∈ Finset.range n, lamg l σ q := by
    rw [← Equiv.sum_comp σ G]
    have : ∀ q : Fin (2 * n + 1), G (σ q) = if q.val < n then lamg l σ q.val else 0 := by
      intro q
      simp [hG, lamg, q.isLt]
    rw [Finset.sum_congr rfl (fun q _ => this q)]
    rw [Fin.sum_univ_eq_sum_range (fun q => if q < n then lamg l σ q else 0) (2 * n + 1)]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext q; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [h2, zero_add] at h1
  rw [← h3, h1]

lemma sg_eq {n : ℕ} (s : Fin (2 * n + 1) → ℝ) (σ : Equiv.Perm (Fin (2 * n + 1))) (q : ℕ)
    (h : q < 2 * n + 1) : sg s σ q = s (σ ⟨q, h⟩) := by
  unfold sg; rw [dif_pos h]

lemma lamg_eq {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (σ : Equiv.Perm (Fin (2 * n + 1))) (q : ℕ)
    (h : q < 2 * n + 1) : lamg l σ q = l (σ ⟨q, h⟩) := by
  unfold lamg; rw [dif_pos h]

theorem td_struct {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (hl0 : 0 < l 0) (hmono : StrictMono l)
    (M : ℝ) (s : Fin (2 * n + 1) → ℝ)
    (hns : ∀ i j, i ≠ j → s i + l i ≤ s j ∨ s j + l j ≤ s i)
    (hc : commonCost l M s = kStar l) (L : ℝ) (hL : L = ∑ i, l i) (hM : M = L / 2)
    (hend : ∀ a, s a + l a ≤ L ∨ L + 2 ≤ s a) (hs0 : ∀ a, 0 ≤ s a) :
    ∃ σ : Equiv.Perm (Fin (2 * n + 1)), σ ⟨n, by omega⟩ = 0 ∧
      (∀ i : Fin n, ((σ.symm (oddTask i)).val < n ↔ ¬ (σ.symm (evenTask i)).val < n)) ∧
      ∑ q ∈ Finset.range n, lamg l σ q = M - l 0 / 2 := by
  obtain ⟨σ, hst, htight, hn0, hmid0, hodd, hlow⟩ := (core_pos l hl0 hmono M s hns).2 hc
  refine ⟨σ, hn0, fun i => pair_split σ hn0 hodd hlow i, ?_⟩
  have hpos := l_pos l hl0 hmono
  have hS1 : ∀ q, q + 1 < 2 * n + 1 → sg s σ (q + 1) = sg s σ q + lamg l σ q := by
    intro q hq
    have h := htight ⟨q, by omega⟩ ⟨q + 1, hq⟩ (by simp)
    simp only [sg, lamg, dif_pos hq, dif_pos (show q < 2 * n + 1 by omega)]
    unfold mid at h
    linarith
  have hS2 : ∀ q, q < 2 * n + 1 → sg s σ q = sg s σ 0 + ∑ j ∈ Finset.range q, lamg l σ j := by
    intro q
    induction q with
    | zero => intro _; simp
    | succ q ih =>
      intro hq
      rw [hS1 q hq, ih (by omega), Finset.sum_range_succ]
      ring
  have hSn : sg s σ n + l 0 / 2 = M := by
    have : sg s σ n = s (σ ⟨n, by omega⟩) := sg_eq s σ n (by omega)
    rw [this, hn0]
    have := hmid0
    unfold mid at this
    exact this
  have hlam_nn : ∀ q, 0 ≤ lamg l σ q := by
    intro q; unfold lamg; split_ifs
    · exact (hpos _).le
    · exact le_refl _
  have htot : ∑ q ∈ Finset.range (2 * n + 1), lamg l σ q = L := by
    rw [← Fin.sum_univ_eq_sum_range (lamg l σ) (2 * n + 1), hL, ← Equiv.sum_comp σ l]
    apply Finset.sum_congr rfl
    intro q _
    simp [lamg, q.isLt]
  have hLnn : 0 ≤ L := by rw [hL]; exact Finset.sum_nonneg (fun i _ => (hpos i).le)
  have hsum_n : 0 ≤ ∑ j ∈ Finset.range n, lamg l σ j := Finset.sum_nonneg (fun j _ => hlam_nn j)
  have hSle : sg s σ 0 < L + 2 := by
    have := hS2 n (by omega)
    linarith
  have hendq : ∀ q, q < 2 * n + 1 → sg s σ q + lamg l σ q ≤ L := by
    intro q
    induction q with
    | zero =>
      intro hq
      rcases hend (σ ⟨0, hq⟩) with h | h
      · rw [sg_eq s σ 0 hq, lamg_eq l σ 0 hq]; exact h
      · exfalso
        have : sg s σ 0 = s (σ ⟨0, hq⟩) := sg_eq s σ 0 hq
        linarith
    | succ q ih =>
      intro hq
      have ih' := ih (by omega)
      rcases hend (σ ⟨q + 1, hq⟩) with h | h
      · rw [sg_eq s σ (q+1) hq, lamg_eq l σ (q+1) hq]; exact h
      · exfalso
        have h1 : sg s σ (q + 1) = s (σ ⟨q + 1, hq⟩) := sg_eq s σ (q+1) hq
        have := hS1 q hq
        linarith
  have hlast := hendq (2 * n) (by omega)
  have hS2' := hS2 (2 * n) (by omega)
  have hsr : ∑ j ∈ Finset.range (2 * n + 1), lamg l σ j =
      ∑ j ∈ Finset.range (2 * n), lamg l σ j + lamg l σ (2 * n) := Finset.sum_range_succ _ _
  have hS0le : sg s σ 0 ≤ 0 := by linarith
  have hS0ge : 0 ≤ sg s σ 0 := by
    have : sg s σ 0 = s (σ ⟨0, by omega⟩) := sg_eq s σ 0 (by omega)
    rw [this]; exact hs0 _
  have hS0 : sg s σ 0 = 0 := le_antisymm hS0le hS0ge
  have := hS2 n (by omega)
  linarith

theorem td_to_eo (x : List ℕ) (hx : EOInstance x) (hx1 : 1 < x.getD 0 0)
    (h : TDYesReal (dLen x) (dMid x) (dK x)) : EOYes x := by
  classical
  have hlen := EO_len x hx
  set n := x.length / 2 with hn
  obtain ⟨s', ⟨hs0', hns'⟩, hcost⟩ := h
  have hmono := dLenH_strictMono x hx hx1
  have hl0 := dLenH_zero_pos x hx1
  have hpos := l_pos (dLenH x) hl0 hmono
  set L : ℝ := ∑ i, dLenH x i with hLdef
  have hM : dM x = L / 2 := dM_eq x
  set s : Fin (2 * n + 1) → ℝ := fun a => s' a.castSucc with hsdef
  have hns : ∀ i j, i ≠ j → s i + dLenH x i ≤ s j ∨ s j + dLenH x j ≤ s i := by
    intro i j hij
    exact hns' i.castSucc j.castSucc (fun h => hij (Fin.castSucc_injective _ h))
  -- cost decomposition
  unfold midCost at hcost
  have e : ∑ j : Fin (2 * n + 1 + 1), |mid (dLen x) s' j - dMid x j| =
      ∑ a : Fin (2 * n + 1), |mid (dLen x) s' a.castSucc - dMid x a.castSucc| +
      |mid (dLen x) s' (Fin.last _) - dMid x (Fin.last _)| := Fin.sum_univ_castSucc _
  have e1 : ∀ a : Fin (2 * n + 1), |mid (dLen x) s' a.castSucc - dMid x a.castSucc|
      = |dM x - mid (dLenH x) s a| := by
    intro a
    rw [dMid_cs, abs_sub_comm]
    rfl
  have hcc : ∑ a : Fin (2 * n + 1), |mid (dLen x) s' a.castSucc - dMid x a.castSucc| =
      commonCost (dLenH x) (dM x) s := by
    unfold commonCost
    exact Finset.sum_congr rfl (fun a _ => e1 a)
  have hlow := (core_pos (dLenH x) hl0 hmono (dM x) s hns).1
  have hdK : dK x = kStar (dLenH x) := dK_eq x
  have hcost' : commonCost (dLenH x) (dM x) s + |mid (dLen x) s' (Fin.last _) - dMid x (Fin.last _)|
      ≤ kStar (dLenH x) := by
    rw [← hcc, ← hdK]; exact e ▸ hcost
  have habs := abs_nonneg (mid (dLen x) s' (Fin.last _) - dMid x (Fin.last _))
  have hceq : commonCost (dLenH x) (dM x) s = kStar (dLenH x) := by linarith
  have htl : |mid (dLen x) s' (Fin.last _) - dMid x (Fin.last _)| = 0 := by linarith
  have hlast : s' (Fin.last _) = L := by
    have := abs_eq_zero.mp htl
    rw [dMid_last] at this
    unfold mid at this
    rw [dLen_last_eq] at this
    linarith
  have hend : ∀ a, s a + dLenH x a ≤ L ∨ L + 2 ≤ s a := by
    intro a
    rcases hns' a.castSucc (Fin.last _) (Fin.castSucc_lt_last a).ne with h | h
    · left; rw [hlast] at h; exact h
    · right; rw [hlast, dLen_last_eq] at h; exact h
  have hs0 : ∀ a, 0 ≤ s a := fun a => hs0' a.castSucc
  obtain ⟨σ, hn0, hpair, hΛ⟩ := td_struct (dLenH x) hl0 hmono (dM x) s hns hceq L rfl hM hend hs0
  -- the predicate
  set Q : ℕ → Prop := fun p => ∃ h : p + 1 < 2 * n + 1, (σ.symm ⟨p + 1, h⟩).val < n with hQdef
  rw [eoyes_pred]
  refine ⟨Q, ?_, ?_⟩
  · intro i hi
    have hi' : i < n := by omega
    have := hpair ⟨i, hi'⟩
    constructor
    · rintro ⟨h1, h2⟩ ⟨h3, h4⟩
      exact (this.mp h2) h4
    · intro hn'
      have h1 : 2 * i + 1 < 2 * n + 1 := by omega
      refine ⟨h1, ?_⟩
      by_contra hc
      exact hn' ⟨by omega, by_contra fun h' => hc (this.mpr h')⟩
  · have hxp : ∀ i : Fin (2 * n), dLenH x (Fin.succ i) = (x.getD i.val 0 : ℝ) := by
      intro i
      rw [dLenH_pos x (Fin.succ i) (by simp)]
      simp
    have hQiff : ∀ i : Fin (2 * n), Q i.val ↔ (σ.symm (Fin.succ i)).val < n := by
      intro i
      constructor
      · rintro ⟨h1, h2⟩; exact h2
      · intro h2; exact ⟨by omega, h2⟩
    have hSQ : ∑ p ∈ Finset.range (2 * n), (if Q p then (x.getD p 0 : ℝ) else 0) =
        dM x - dLenH x 0 / 2 := by
      rw [← Fin.sum_univ_eq_sum_range (fun p => if Q p then (x.getD p 0 : ℝ) else 0) (2 * n)]
      have := claimA (dLenH x) σ hn0
      rw [hΛ] at this
      rw [← this]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hq : Q i.val
      · rw [if_pos hq, if_pos ((hQiff i).mp hq), hxp]
      · rw [if_neg hq, if_neg (fun h => hq ((hQiff i).mpr h))]
    have hall : ∑ p ∈ Finset.range (2 * n), (x.getD p 0 : ℝ) = L - dLenH x 0 := by
      have h1 : ∑ t, dLenH x t = dLenH x 0 + ∑ i : Fin (2 * n), dLenH x (Fin.succ i) := Fin.sum_univ_succ _
      rw [← Fin.sum_univ_eq_sum_range (fun p => (x.getD p 0 : ℝ)) (2 * n)]
      have : ∑ i : Fin (2 * n), (x.getD i.val 0 : ℝ) = ∑ i : Fin (2 * n), dLenH x (Fin.succ i) :=
        Finset.sum_congr rfl (fun i _ => (hxp i).symm)
      rw [this]
      rw [hLdef]; linarith
    have hnotQ : ∑ p ∈ Finset.range (2 * n), (if ¬ Q p then (x.getD p 0 : ℝ) else 0) =
        L - dLenH x 0 - (dM x - dLenH x 0 / 2) := by
      rw [← hSQ, ← hall, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hq : Q p
      · rw [if_neg (not_not.mpr hq), if_pos hq]; ring
      · rw [if_pos hq, if_neg hq]; ring
    have hreal : ∑ p ∈ Finset.range (2 * n), (if Q p then (x.getD p 0 : ℝ) else 0) =
        ∑ p ∈ Finset.range (2 * n), (if ¬ Q p then (x.getD p 0 : ℝ) else 0) := by
      rw [hSQ, hnotQ, hM]; ring
    rw [hlen]
    apply Nat.cast_injective (R := ℝ)
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
    exact hreal

theorem reduction_core (x : List ℕ) (hx : EOInstance x) (hx1 : 1 < x.getD 0 0) :
    EOYes x ↔ TDYesReal (dLen x) (dMid x) (dK x) :=
  ⟨eo_to_td x hx hx1, td_to_eo x hx hx1⟩

end GTWSched.NPC

open GTWSched.NPC


theorem solution (x : List ℕ) (hx : EOInstance x) (hx1 : 1 < x.getD 0 0) :
    EOYes x ↔ TDYesReal (dLen x) (dMid x) (dK x) := by
  exact reduction_core x hx hx1
