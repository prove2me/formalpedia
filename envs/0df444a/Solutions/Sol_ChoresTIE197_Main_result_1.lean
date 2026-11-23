-- Prove2me | solution 1 for ChoresTIE197.Main.result_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:27:37.374866+00:00
-- url     : https://prove2.me/submissions/6a45b9b7-432c-425a-b20b-41baa9086100

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Families

open Finset Classical
open scoped NNReal ENNReal
noncomputable section

-- ===== part A =====


namespace ChoresTIE197.Main.Sol
open ChoresTIE197.Main

variable {m : ℕ}

lemma rank_lt_rank (c : Fin m → ℝ≥0) {e f : Fin m}
    (h : c f < c e ∨ (c f = c e ∧ e.val < f.val)) : rank c e < rank c f := by
  unfold rank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨e, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h
    · simp
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rcases h with h | ⟨h1, h2⟩ <;> rcases hg with hg | ⟨hg1, hg2⟩
    · left; exact lt_trans h hg
    · left; rw [← hg1]; exact h
    · left; rw [h1]; exact hg
    · right; exact ⟨h1.trans hg1, lt_trans hg2 h2⟩

lemma rank_lt_m (c : Fin m → ℝ≥0) (e : Fin m) : rank c e < m := by
  unfold rank
  calc _ < (univ : Finset (Fin m)).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
        exact ⟨e, Finset.mem_univ _, by simp⟩
    _ = m := by simp

lemma rank_injective (c : Fin m → ℝ≥0) : Function.Injective (rank c) := by
  intro e f hef
  by_contra hne
  rcases lt_trichotomy (c e) (c f) with h | h | h
  · have := rank_lt_rank c (e := f) (f := e) (Or.inl h); omega
  · rcases lt_trichotomy e.val f.val with h2 | h2 | h2
    · have := rank_lt_rank c (e := e) (f := f) (Or.inr ⟨h.symm, h2⟩); omega
    · exact hne (Fin.ext h2)
    · have := rank_lt_rank c (e := f) (f := e) (Or.inr ⟨h, h2⟩); omega
  · have := rank_lt_rank c (e := e) (f := f) (Or.inl h); omega

lemma cost_le_of_rank_lt (c : Fin m → ℝ≥0) {e f : Fin m} (h : rank c e < rank c f) :
    c f ≤ c e := by
  by_contra h'
  rw [not_le] at h'
  have := rank_lt_rank c (e := f) (f := e) (Or.inl h')
  omega

lemma cost_le_of_rank_le (c : Fin m → ℝ≥0) {e f : Fin m} (h : rank c e ≤ rank c f) :
    c f ≤ c e := by
  rcases h.lt_or_eq with h | h
  · exact cost_le_of_rank_lt c h
  · rw [rank_injective c h]

/-- rank as an equivalence. -/
def rankEquiv (c : Fin m → ℝ≥0) : Fin m ≃ Fin m :=
  Equiv.ofBijective (fun e => ⟨rank c e, rank_lt_m c e⟩)
    ((Finite.injective_iff_bijective).mp (fun e f h => rank_injective c (by
      simpa using congrArg Fin.val h)))

@[simp] lemma rankEquiv_val (c : Fin m → ℝ≥0) (e : Fin m) : (rankEquiv c e).val = rank c e := rfl

lemma rank_symm (c : Fin m → ℝ≥0) (k : Fin m) : rank c ((rankEquiv c).symm k) = k.val := by
  rw [← rankEquiv_val, Equiv.apply_symm_apply]

/-- sorted cost: the cost of the chore of rank k (zero-based), 0 if none. -/
def sc (c : Fin m → ℝ≥0) (k : ℕ) : ℝ :=
  if h : k < m then (c ((rankEquiv c).symm ⟨k, h⟩) : ℝ) else 0

lemma sc_nonneg (c : Fin m → ℝ≥0) (k : ℕ) : 0 ≤ sc c k := by
  unfold sc; split_ifs <;> simp

lemma sc_rank (c : Fin m → ℝ≥0) (e : Fin m) : sc c (rank c e) = c e := by
  unfold sc
  rw [dif_pos (rank_lt_m c e)]
  have : (rankEquiv c).symm ⟨rank c e, rank_lt_m c e⟩ = e := by
    rw [Equiv.symm_apply_eq]; ext; simp
  rw [this]

lemma sc_le_of_rank_le (c : Fin m → ℝ≥0) {e : Fin m} {k : ℕ} (h : rank c e ≤ k) :
    sc c k ≤ c e := by
  unfold sc
  split_ifs with hk
  · have := cost_le_of_rank_le c (e := e) (f := (rankEquiv c).symm ⟨k, hk⟩)
      (by rw [rank_symm]; exact h)
    exact_mod_cast this
  · simp

lemma le_sc_of_le_rank (c : Fin m → ℝ≥0) {e : Fin m} {k : ℕ} (h : k ≤ rank c e) :
    (c e : ℝ) ≤ sc c k := by
  have hk : k < m := lt_of_le_of_lt h (rank_lt_m c e)
  unfold sc
  rw [dif_pos hk]
  have := cost_le_of_rank_le c (e := (rankEquiv c).symm ⟨k, hk⟩) (f := e)
    (by rw [rank_symm]; exact h)
  exact_mod_cast this

lemma le_sc_zero (c : Fin m → ℝ≥0) (e : Fin m) : (c e : ℝ) ≤ sc c 0 :=
  le_sc_of_le_rank c (Nat.zero_le _)

lemma mem_top (c : Fin m → ℝ≥0) (r : ℕ) (e : Fin m) : e ∈ top c r ↔ rank c e < r := by
  simp [top]

lemma card_top (c : Fin m → ℝ≥0) (r : ℕ) : (top c r).card = min r m := by
  have : top c r = (univ.filter (fun k : Fin m => k.val < r)).map (rankEquiv c).symm.toEmbedding := by
    ext e
    simp only [mem_top, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.toEmbedding_apply]
    constructor
    · intro h; exact ⟨rankEquiv c e, by simpa using h, by simp⟩
    · rintro ⟨k, hk, rfl⟩; rw [rank_symm]; exact hk
  rw [this, Finset.card_map]
  rcases le_total r m with h | h
  · rw [min_eq_left h]
    have : (univ.filter (fun k : Fin m => k.val < r)) = (Finset.range r).attachFin
        (fun k hk => lt_of_lt_of_le (Finset.mem_range.mp hk) h) := by
      ext k; simp
    rw [this, Finset.card_attachFin, Finset.card_range]
  · rw [min_eq_right h]
    have : (univ.filter (fun k : Fin m => k.val < r)) = univ := by
      ext k; simp; omega
    rw [this]; simp

/-- Sequence Abel lemma. -/
lemma seq_abel (N : ℕ) (a Y C : ℕ → ℝ)
    (hpre : ∀ r ≤ N, ∑ k ∈ range r, a k ≤ ∑ k ∈ range r, Y k)
    (hanti : ∀ k, k + 1 < N → C (k + 1) ≤ C k) (hnn : ∀ k < N, 0 ≤ C k) :
    ∑ k ∈ range N, a k * C k ≤ ∑ k ∈ range N, Y k * C k := by
  set C' : ℕ → ℝ := fun k => if k < N then C k else 0 with hC'
  set D : ℕ → ℝ := fun r => ∑ k ∈ range r, (Y k - a k) with hD
  have ident : ∀ M, ∑ k ∈ range M, (Y k - a k) * C' k =
      D M * C' M + ∑ k ∈ range M, D (k + 1) * (C' k - C' (k + 1)) := by
    intro M
    induction M with
    | zero => simp [hD]
    | succ M ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [hD, Finset.sum_range_succ]
      ring
  have h1 : ∑ k ∈ range N, (Y k - a k) * C' k = ∑ k ∈ range N, (Y k - a k) * C k := by
    apply Finset.sum_congr rfl
    intro k hk; rw [Finset.mem_range] at hk; simp [hC', hk]
  have h2 : 0 ≤ ∑ k ∈ range N, (Y k - a k) * C' k := by
    rw [ident N]
    have : C' N = 0 := by simp [hC']
    rw [this, mul_zero, zero_add]
    apply Finset.sum_nonneg
    intro k hk
    rw [Finset.mem_range] at hk
    apply mul_nonneg
    · simp only [hD, Finset.sum_sub_distrib, sub_nonneg]
      exact hpre (k + 1) hk
    · simp only [hC']
      rw [if_pos hk]
      by_cases hk1 : k + 1 < N
      · rw [if_pos hk1]; linarith [hanti k hk1]
      · rw [if_neg hk1]; linarith [hnn k hk]
  rw [h1] at h2
  have : ∑ k ∈ range N, (Y k - a k) * C k =
      ∑ k ∈ range N, Y k * C k - ∑ k ∈ range N, a k * C k := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro k _; ring
  linarith

/-- sequence version of a function on chores, in rank order. -/
def sq (c : Fin m → ℝ≥0) (g : Fin m → ℝ) (k : ℕ) : ℝ :=
  if hk : k < m then g ((rankEquiv c).symm ⟨k, hk⟩) else 0

lemma sum_eq_sq (c : Fin m → ℝ≥0) (g : Fin m → ℝ) :
    ∑ e, g e = ∑ k ∈ range m, sq c g k := by
  rw [Finset.sum_range, ← Equiv.sum_comp (rankEquiv c).symm]
  apply Finset.sum_congr rfl; intro k _; simp [sq]

lemma sum_range_eq_ite {r M : ℕ} (hr : r ≤ M) (F : ℕ → ℝ) :
    ∑ k ∈ range r, F k = ∑ k ∈ range M, if k < r then F k else 0 := by
  rw [← Finset.sum_filter]
  congr 1; ext k; simp; omega

lemma sum_top_eq_sq (c : Fin m → ℝ≥0) (g : Fin m → ℝ) {r : ℕ} (hr : r ≤ m) :
    ∑ e ∈ top c r, g e = ∑ k ∈ range r, sq c g k := by
  rw [top, Finset.sum_filter, sum_eq_sq c, sum_range_eq_ite hr]
  apply Finset.sum_congr rfl; intro k hk
  rw [Finset.mem_range] at hk
  simp [sq, hk, rank_symm]

lemma sum_top_of_le (c : Fin m → ℝ≥0) (g : Fin m → ℝ) {r : ℕ} (hr : m ≤ r) :
    ∑ e ∈ top c r, g e = ∑ e, g e := by
  congr 1; ext e; simp [mem_top]; have := rank_lt_m c e; omega

lemma top_of_le (c : Fin m → ℝ≥0) {r : ℕ} (hr : m ≤ r) : top c r = univ := by
  ext e; simp [mem_top]; have := rank_lt_m c e; omega

lemma sc_eq_sq (c : Fin m → ℝ≥0) (k : ℕ) : sc c k = sq c (fun e => (c e : ℝ)) k := rfl

/-- Master Abel lemma: prefix-count domination implies cost domination. -/
lemma master_abel (c : Fin m → ℝ≥0) (y : Fin m → ℝ) (B : Finset (Fin m))
    (h : ∀ r, ((B.filter (fun e => rank c e < r)).card : ℝ) ≤ ∑ e ∈ top c r, y e) :
    cost c B ≤ ∑ e, y e * c e := by
  set ind : Fin m → ℝ := fun e => if e ∈ B then 1 else 0
  have hcost : cost c B = ∑ e, ind e * c e := by
    unfold cost
    rw [← Finset.sum_subset (Finset.subset_univ B)]
    · apply Finset.sum_congr rfl; intro e he; simp [ind, he]
    · intro e _ he; simp [ind, he]
  have hseq : ∀ g : Fin m → ℝ, ∑ e, g e * c e = ∑ k ∈ range m, sq c g k * sc c k := by
    intro g
    rw [sum_eq_sq c]
    apply Finset.sum_congr rfl; intro k hk
    rw [Finset.mem_range] at hk
    simp [sq, sc, hk]
  rw [hcost, hseq, hseq]
  apply seq_abel m (sq c ind) (sq c y) (sc c)
  · intro r hr
    rw [← sum_top_eq_sq c ind hr, ← sum_top_eq_sq c y hr]
    have : ∑ e ∈ top c r, ind e = ((B.filter (fun e => rank c e < r)).card : ℝ) := by
      simp only [ind]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 2; ext e; simp [mem_top, and_comm]
    rw [this]; exact h r
  · intro k hk
    have hk' : k < m := by omega
    rw [sc_eq_sq, sc_eq_sq]
    simp only [sq, dif_pos hk, dif_pos hk']
    exact_mod_cast cost_le_of_rank_le c (by rw [rank_symm, rank_symm]; simp)
  · intro k _; exact sc_nonneg c k

end ChoresTIE197.Main.Sol

-- ===== part B =====


namespace ChoresTIE197.Main.Sol
open ChoresTIE197.Main

variable {m : ℕ}

lemma mms_ge {n : ℕ} (hn : 0 < n) (c : Fin m → ℝ≥0) (b : ℝ)
    (h : ∀ f : Fin m → Fin n, ∃ j, b ≤ cost c (univ.filter (fun g => f g = j))) :
    b ≤ mms c n univ := by
  unfold mms LittleCharity.MMS.mms
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  suffices H : (⨆ f : Fin m → Fin n, ⨅ j : Fin n,
      -cost c (univ.filter (fun g => f g = j))) ≤ -b by
    have : (⨆ f : Fin m → Fin n, ⨅ j : Fin n, (fun T => -cost c T)
        ((univ : Finset (Fin m)).filter (fun g => f g = j))) ≤ -b := by
      convert H
    linarith
  apply ciSup_le
  intro f
  obtain ⟨j, hj⟩ := h f
  exact (ciInf_le (Finite.bddBelow_range _) j).trans (by linarith)

lemma cost_nonneg (c : Fin m → ℝ≥0) (S : Finset (Fin m)) : 0 ≤ cost c S := by
  unfold cost; exact Finset.sum_nonneg (fun e _ => by positivity)

lemma cost_mono (c : Fin m → ℝ≥0) {S T : Finset (Fin m)} (h : S ⊆ T) : cost c S ≤ cost c T := by
  unfold cost
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun e _ _ => by positivity)

lemma mms_ge_avg {n : ℕ} (hn : 0 < n) (c : Fin m → ℝ≥0) :
    cost c univ / n ≤ mms c n univ := by
  apply mms_ge hn
  intro f
  have hsum : ∑ j, cost c (univ.filter (fun g => f g = j)) = cost c univ := by
    unfold cost; exact Finset.sum_fiberwise univ f (fun e => (c e : ℝ))
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => cost c univ / n) (g := fun j => cost c (univ.filter (fun g => f g = j)))
    (by rw [hsum]; simp; field_simp; rfl)
  exact ⟨j, hj⟩

lemma mms_ge_single {n : ℕ} (hn : 0 < n) (c : Fin m → ℝ≥0) (e : Fin m) :
    (c e : ℝ) ≤ mms c n univ := by
  apply mms_ge hn
  intro f
  refine ⟨f e, ?_⟩
  unfold cost
  exact Finset.single_le_sum (f := fun e => (c e : ℝ)) (fun _ _ => by positivity)
    (by simp)

lemma mms_nonneg {n : ℕ} (hn : 0 < n) (c : Fin m → ℝ≥0) : 0 ≤ mms c n univ :=
  le_trans (div_nonneg (cost_nonneg c univ) (by positivity)) (mms_ge_avg hn c)

lemma mms_ge_two_sc {n : ℕ} (hn : 0 < n) (c : Fin m → ℝ≥0) :
    2 * sc c n ≤ mms c n univ := by
  by_cases hnm : n < m
  · apply mms_ge hn
    intro f
    have hcard : (univ : Finset (Fin n)).card < (top c (n+1)).card := by
      rw [card_top]; simp; omega
    obtain ⟨x, hx, y, hy, hxy, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := f) (fun _ _ => mem_univ _)
    refine ⟨f x, ?_⟩
    rw [mem_top] at hx hy
    have h1 := sc_le_of_rank_le c (e := x) (k := n) (by omega)
    have h2 := sc_le_of_rank_le c (e := y) (k := n) (by omega)
    have : cost c {x, y} ≤ cost c (univ.filter (fun g => f g = f x)) := by
      apply cost_mono; intro z hz; simp at hz; rcases hz with rfl | rfl <;> simp [hf]
    have h3 : cost c {x, y} = c x + c y := by
      unfold cost; rw [Finset.sum_pair hxy]
    linarith
  · have : sc c n = 0 := by simp [sc, hnm]
    rw [this, mul_zero]; exact mms_nonneg hn c

/-- The lower bound L on the MMS. -/
def Lb (c : Fin m → ℝ≥0) (n : ℕ) : ℝ := max (cost c univ / n) (max (sc c 0) (2 * sc c n))

lemma Lb_le_mms {n : ℕ} (hn : 0 < n) (c : Fin m → ℝ≥0) : Lb c n ≤ mms c n univ := by
  unfold Lb
  refine max_le (mms_ge_avg hn c) (max_le ?_ (mms_ge_two_sc hn c))
  by_cases hm : 0 < m
  · have := sc_rank c ((rankEquiv c).symm ⟨0, hm⟩)
    rw [rank_symm] at this
    rw [this]; exact mms_ge_single hn c _
  · have : sc c 0 = 0 := by simp [sc, hm]
    rw [this]; exact mms_nonneg hn c

lemma Lb_nonneg (c : Fin m → ℝ≥0) (n : ℕ) : 0 ≤ Lb c n :=
  le_trans (sc_nonneg c 0) (le_trans (le_max_left _ _) (le_max_right _ _))

lemma tot_le_Lb {n : ℕ} (hn : 0 < n) (c : Fin m → ℝ≥0) : cost c univ ≤ n * Lb c n := by
  have := le_max_left (cost c univ / n) (max (sc c 0) (2 * sc c n))
  rw [div_le_iff₀ (by exact_mod_cast hn)] at this
  unfold Lb; linarith

lemma sc0_le_Lb (c : Fin m → ℝ≥0) (n : ℕ) : sc c 0 ≤ Lb c n :=
  le_trans (le_max_left _ _) (le_max_right _ _)

lemma scn_le_Lb (c : Fin m → ℝ≥0) (n : ℕ) : 2 * sc c n ≤ Lb c n :=
  le_trans (le_max_right _ _) (le_max_right _ _)

end ChoresTIE197.Main.Sol

-- ===== part C =====


namespace ChoresTIE197.Main.Sol
open ChoresTIE197.Main

/-! ### Abstract bipartite rounding via Birkhoff -/

section Bip
variable {R C : Type} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

def padMat (W : R → C → ℝ) : Matrix (R ⊕ C) (R ⊕ C) ℝ := fun a b =>
  match a, b with
  | .inl _, .inl _ => 0
  | .inl r, .inr c => W r c
  | .inr c', .inl r' => W r' c'
  | .inr c', .inr c => if c' = c then 1 - ∑ r, W r c else 0

lemma padMat_ds (W : R → C → ℝ) (hW0 : ∀ r c, 0 ≤ W r c) (hrow : ∀ r, ∑ c, W r c = 1)
    (hcol : ∀ c, ∑ r, W r c ≤ 1) : padMat W ∈ doublyStochastic ℝ (R ⊕ C) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · rintro (r | c) (r' | c') <;> simp only [padMat]
    · exact le_refl _
    · exact hW0 _ _
    · exact hW0 _ _
    · split_ifs with h
      · subst h; linarith [hcol c]
      · exact le_refl _
  · rintro (r | c)
    · simp only [Fintype.sum_sum_type, padMat, Finset.sum_const_zero, zero_add]; exact hrow r
    · simp only [Fintype.sum_sum_type, padMat, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
  · rintro (r | c)
    · simp only [Fintype.sum_sum_type, padMat]; rw [hrow r]; simp
    · simp only [Fintype.sum_sum_type, padMat, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring

lemma bip_round (W : R → C → ℝ) (hW0 : ∀ r c, 0 ≤ W r c) (hrow : ∀ r, ∑ c, W r c = 1)
    (hcol : ∀ c, ∑ r, W r c ≤ 1) :
    ∃ (w : Equiv.Perm (R ⊕ C) → ℝ) (g : Equiv.Perm (R ⊕ C) → R → C),
      (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧
      (∀ σ, 0 < w σ → Function.Injective (g σ) ∧ ∀ r, 0 < W r (g σ r)) ∧
      ∀ r c, ∑ σ, (if g σ r = c then w σ else 0) = W r c := by
  have hex : ∀ r, ∃ c, 0 < W r c := by
    intro r
    by_contra h
    push Not at h
    have : ∑ c, W r c ≤ 0 := Finset.sum_nonpos (fun c _ => h c)
    rw [hrow r] at this; linarith
  let fb : R → C := fun r => Classical.choose (hex r)
  obtain ⟨w, hw0, hw1, hwM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic
    (padMat_ds W hW0 hrow hcol)
  have hentry : ∀ a b, ∑ σ : Equiv.Perm (R ⊕ C), (if σ a = b then w σ else 0) = padMat W a b := by
    intro a b
    rw [← hwM, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro σ _
    simp [Matrix.smul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  let g : Equiv.Perm (R ⊕ C) → R → C := fun σ r => Sum.elim (fun _ => fb r) id (σ (Sum.inl r))
  have hpos : ∀ σ, 0 < w σ → ∀ r, ∃ c, σ (Sum.inl r) = Sum.inr c ∧ 0 < W r c := by
    intro σ hσ r
    have hge : w σ ≤ padMat W (Sum.inl r) (σ (Sum.inl r)) := by
      rw [← hentry]
      have := Finset.single_le_sum (f := fun τ : Equiv.Perm (R ⊕ C) =>
        if τ (Sum.inl r) = σ (Sum.inl r) then w τ else 0)
        (fun τ _ => by split_ifs <;> simp [hw0]) (Finset.mem_univ σ)
      simpa using this
    rcases hs : σ (Sum.inl r) with r' | c
    · rw [hs] at hge; simp [padMat] at hge; linarith
    · rw [hs] at hge; exact ⟨c, rfl, by simp only [padMat] at hge; linarith⟩
  refine ⟨w, g, hw0, hw1, ?_, ?_⟩
  · intro σ hσ
    constructor
    · intro r1 r2 h12
      obtain ⟨c1, h1, _⟩ := hpos σ hσ r1
      obtain ⟨c2, h2, _⟩ := hpos σ hσ r2
      simp only [g, h1, h2, Sum.elim_inr, id] at h12
      subst h12
      have := σ.injective (h1.trans h2.symm)
      exact Sum.inl_injective this
    · intro r
      obtain ⟨c1, h1, hc1⟩ := hpos σ hσ r
      simp only [g, h1, Sum.elim_inr, id]; exact hc1
  · intro r c
    rw [show W r c = padMat W (Sum.inl r) (Sum.inr c) from rfl, ← hentry]
    apply Finset.sum_congr rfl
    intro σ _
    rcases (hw0 σ).lt_or_eq with hσ | hσ
    · obtain ⟨c1, h1, _⟩ := hpos σ hσ r
      simp only [g, h1, Sum.elim_inr, id, Sum.inr.injEq]
    · rw [← hσ]; simp
end Bip

/-! ### Laws from finite weights -/

lemma law_of_weights {n m : ℕ} {ι : Type} [Fintype ι] (w : ι → ℝ) (hw0 : ∀ k, 0 ≤ w k)
    (hw1 : ∑ k, w k = 1) (f : ι → Allocation n m) :
    ∃ p : Law n m, (∀ A, p A ≠ 0 → ∃ k, 0 < w k ∧ f k = A) ∧
      ∀ φ : Allocation n m → ℝ, ∑ A, (p A).toReal * φ A = ∑ k, w k * φ (f k) := by
  have hsum : ∑ k, ENNReal.ofReal (w k) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hw0 k), hw1, ENNReal.ofReal_one]
  let q : PMF ι := PMF.ofFintype (fun k => ENNReal.ofReal (w k)) hsum
  refine ⟨q.map f, ?_, ?_⟩
  · intro A hA
    rw [PMF.map_apply, tsum_fintype] at hA
    obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hA
    split_ifs at hk with hAk
    · refine ⟨k, ?_, hAk.symm⟩
      simp only [q, PMF.ofFintype_apply, ne_eq, ENNReal.ofReal_eq_zero, not_le] at hk
      exact hk
    · exact absurd rfl hk
  · intro φ
    have hp : ∀ A, ((q.map f) A).toReal = ∑ k, if A = f k then w k else 0 := by
      intro A
      rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
      · apply Finset.sum_congr rfl; intro k _
        split_ifs
        · simp [q, ENNReal.toReal_ofReal (hw0 k)]
        · simp
      · intro k _; split_ifs <;> simp [q]
    simp_rw [hp, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    simp [ite_mul, Finset.sum_ite_eq']

/-! ### Interval overlaps -/

def ov (a b s u : ℝ) : ℝ := max 0 (min b u - max a s)

lemma ov_comm (a b s u : ℝ) : ov a b s u = ov s u a b := by
  simp [ov, min_comm, max_comm]

lemma ov_add (a b s u v : ℝ) (hab : a ≤ b) (hsu : s ≤ u) (huv : u ≤ v) :
    ov a b s u + ov a b u v = ov a b s v := by
  simp only [ov, max_def, min_def]
  split_ifs <;> linarith

lemma ov_nonneg (a b s u : ℝ) : 0 ≤ ov a b s u := le_max_left _ _

lemma ov_le (a b s u : ℝ) (hsu : s ≤ u) : ov a b s u ≤ u - s := by
  simp only [ov]
  apply max_le (by linarith)
  have := min_le_right b u; have := le_max_right a s; linarith

lemma ov_pos {a b s u : ℝ} (h : 0 < ov a b s u) : s < b ∧ a < b := by
  simp only [ov] at h
  have h' : 0 < min b u - max a s := by
    by_contra hc; push Not at hc; rw [max_eq_left hc] at h; linarith
  have := min_le_left b u; have := le_max_left a s; have := le_max_right a s
  constructor <;> linarith

lemma ov_sum_range (a b : ℝ) (hab : a ≤ b) (N : ℕ) :
    ∑ t ∈ range N, ov a b t (t + 1) = ov a b 0 N := by
  induction N with
  | zero => simp [ov]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have := ov_add a b 0 N (N + 1) hab (by positivity) (by linarith)
    push_cast; linarith

lemma ov_full (a b N : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ N) : ov a b 0 N = b - a := by
  simp only [ov, min_eq_left hb, max_eq_left ha]; exact max_eq_right (by linarith)

lemma ov_telescope (P : ℕ → ℝ) (hP : Monotone P) (s u : ℝ) (hsu : s ≤ u) (N : ℕ) :
    ∑ k ∈ range N, ov (P k) (P (k+1)) s u = ov (P 0) (P N) s u := by
  induction N with
  | zero => simp [ov]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, ov_comm (P 0), ov_comm (P N), ov_comm (P 0)]
    exact ov_add s u (P 0) (P N) (P (N+1)) hsu (hP (Nat.zero_le _)) (hP (Nat.le_succ _))

end ChoresTIE197.Main.Sol

-- ===== part D =====


namespace ChoresTIE197.Main.Sol
open ChoresTIE197.Main

variable {m : ℕ}

/-- Slot compatibility of a bundle with a fractional row. -/
def SlotOK (ci : Fin m → ℝ≥0) (xi : Fin m → ℝ) (B : Finset (Fin m)) : Prop :=
  (∀ e ∈ B, 0 < xi e) ∧
    ∀ r, ((B.filter (fun e => rank ci e < r)).card : ℝ) < 1 + ∑ e ∈ top ci r, xi e

/-- start of the interval of chore e for agent row ci. -/
def Fst (ci : Fin m → ℝ≥0) (xi : Fin m → ℝ) (e : Fin m) : ℝ :=
  ∑ f ∈ univ.filter (fun f => rank ci f < rank ci e), xi f

lemma Fst_nonneg (ci : Fin m → ℝ≥0) (xi : Fin m → ℝ) (hx : ∀ e, 0 ≤ xi e) (e : Fin m) :
    0 ≤ Fst ci xi e := Finset.sum_nonneg (fun f _ => hx f)

lemma Fst_add_le (ci : Fin m → ℝ≥0) (xi : Fin m → ℝ) (hx : ∀ e, 0 ≤ xi e) (e : Fin m) {r : ℕ}
    (hr : rank ci e < r) : Fst ci xi e + xi e ≤ ∑ f ∈ top ci r, xi f := by
  unfold Fst
  have hnot : e ∉ univ.filter (fun f => rank ci f < rank ci e) := by simp
  rw [add_comm, ← Finset.sum_insert hnot]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro f hf
    rw [Finset.mem_insert, Finset.mem_filter] at hf
    rw [mem_top]
    rcases hf with rfl | ⟨_, hf⟩
    · exact hr
    · omega
  · intro f _ _; exact hx f

lemma Fst_sq (ci : Fin m → ℝ≥0) (xi : Fin m → ℝ) (k : ℕ) (hk : k < m) :
    Fst ci xi ((rankEquiv ci).symm ⟨k, hk⟩) = ∑ j ∈ range k, sq ci xi j := by
  unfold Fst
  rw [rank_symm, ← sum_top_eq_sq ci xi hk.le]
  rfl

theorem rounding {n : ℕ} [NeZero n] (c : Profile n m) (x : Fraction n m) (hx : Feasible x) :
    ∃ p : Law n m, (∀ i e, marginal p i e = x i e) ∧
      ∀ A, p A ≠ 0 → ∀ i, SlotOK (c i) (x i) (bundle A i) := by
  have hx0 : ∀ i e, 0 ≤ x i e := hx.1
  have hx1 : ∀ i e, x i e ≤ 1 := by
    intro i e
    rw [← hx.2 e]
    exact Finset.single_le_sum (f := fun j => x j e) (fun j _ => hx0 j e) (mem_univ i)
  let W : Fin m → Fin n × Fin m → ℝ := fun e it =>
    ov (Fst (c it.1) (x it.1) e) (Fst (c it.1) (x it.1) e + x it.1 e) (it.2 : ℝ) ((it.2 : ℝ) + 1)
  have hW0 : ∀ e it, 0 ≤ W e it := fun _ _ => ov_nonneg _ _ _ _
  have hrowi : ∀ i e, ∑ t : Fin m, ov (Fst (c i) (x i) e) (Fst (c i) (x i) e + x i e)
      (t : ℝ) ((t : ℝ) + 1) = x i e := by
    intro i e
    rw [Fin.sum_univ_eq_sum_range (fun t => ov (Fst (c i) (x i) e) (Fst (c i) (x i) e + x i e)
      (t : ℝ) ((t : ℝ) + 1)), ov_sum_range _ _ (by linarith [hx0 i e])]
    rw [ov_full _ _ _ (Fst_nonneg _ _ (hx0 i) e) (by linarith [hx0 i e])]
    · ring
    · calc Fst (c i) (x i) e + x i e ≤ ∑ f ∈ top (c i) m, x i f :=
            Fst_add_le _ _ (hx0 i) e (rank_lt_m _ e)
        _ ≤ ∑ f ∈ top (c i) m, (1 : ℝ) := Finset.sum_le_sum (fun f _ => hx1 i f)
        _ ≤ m := by rw [Finset.sum_const, card_top]; simp
  have hrow : ∀ e, ∑ it, W e it = 1 := by
    intro e
    rw [Fintype.sum_prod_type]
    simp only [W]
    rw [Finset.sum_congr rfl (fun i _ => hrowi i e)]
    exact hx.2 e
  have hcol : ∀ it, ∑ e, W e it ≤ 1 := by
    rintro ⟨i, t⟩
    simp only [W]
    rw [sum_eq_sq (c i)]
    set P : ℕ → ℝ := fun k => ∑ j ∈ range k, sq (c i) (x i) j
    have hPm : Monotone P := by
      apply monotone_nat_of_le_succ
      intro k; simp only [P, Finset.sum_range_succ]
      have : 0 ≤ sq (c i) (x i) k := by unfold sq; split_ifs <;> simp [hx0]
      linarith
    have : ∑ k ∈ range m, sq (c i) (fun e => ov (Fst (c i) (x i) e) (Fst (c i) (x i) e + x i e)
        (t : ℝ) ((t : ℝ) + 1)) k = ∑ k ∈ range m, ov (P k) (P (k+1)) (t : ℝ) ((t : ℝ) + 1) := by
      apply Finset.sum_congr rfl; intro k hk
      rw [Finset.mem_range] at hk
      simp only [sq, dif_pos hk, P, Finset.sum_range_succ, Fst_sq _ _ k hk]
    rw [this, ov_telescope P hPm _ _ (by linarith)]
    have := ov_le (P 0) (P m) (t : ℝ) ((t : ℝ) + 1) (by linarith)
    linarith
  obtain ⟨w, g, hw0, hw1, hsupp, hmarg⟩ := bip_round W hW0 hrow hcol
  let alloc : Equiv.Perm (Fin m ⊕ (Fin n × Fin m)) → Allocation n m := fun σ e => (g σ e).1
  obtain ⟨p, hp_supp, hp_exp⟩ := law_of_weights w hw0 hw1 alloc
  refine ⟨p, ?_, ?_⟩
  · intro i e
    have h1 : marginal p i e = ∑ A, (p A).toReal * (if A e = i then 1 else 0) := by
      unfold marginal; apply Finset.sum_congr rfl; intro A _; split_ifs <;> simp
    rw [h1, hp_exp]
    simp only [alloc, mul_ite, mul_one, mul_zero]
    have h2 : ∀ σ, (if (g σ e).1 = i then w σ else 0) =
        ∑ t : Fin m, (if g σ e = (i, t) then w σ else 0) := by
      intro σ
      rcases hge : g σ e with ⟨i', t'⟩
      simp only [Prod.mk.injEq]
      by_cases hii : i' = i
      · subst hii; simp [Finset.sum_ite_eq]
      · simp [hii]
    rw [Finset.sum_congr rfl (fun σ _ => h2 σ), Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun t _ => hmarg e (i, t))]
    exact hrowi i e
  · intro A hA i
    obtain ⟨σ, hσ, rfl⟩ := hp_supp A hA
    obtain ⟨hinj, hWpos⟩ := hsupp σ hσ
    have hbund : ∀ e, e ∈ bundle (alloc σ) i ↔ (g σ e).1 = i := by
      intro e; simp [bundle, alloc]
    have hkey : ∀ e, (g σ e).1 = i →
        ((g σ e).2 : ℝ) < Fst (c i) (x i) e + x i e ∧ Fst (c i) (x i) e < Fst (c i) (x i) e + x i e := by
      intro e he
      have := hWpos e
      simp only [W] at this
      rw [he] at this
      exact ov_pos this
    constructor
    · intro e he
      rw [hbund] at he
      have := (hkey e he).2; linarith
    · intro r
      set X := ∑ e ∈ top (c i) r, x i e
      have hX0 : 0 ≤ X := Finset.sum_nonneg (fun e _ => hx0 i e)
      have hcard : ((bundle (alloc σ) i).filter (fun e => rank (c i) e < r)).card ≤ ⌈X⌉₊ := by
        rw [← Finset.card_range ⌈X⌉₊]
        apply Finset.card_le_card_of_injOn (fun e => ((g σ e).2 : ℕ))
        · intro e he
          rw [Finset.mem_coe, Finset.mem_filter, hbund] at he
          rw [Finset.mem_coe, Finset.mem_range, Nat.lt_ceil]
          have h1 := (hkey e he.1).1
          have h2 := Fst_add_le (c i) (x i) (hx0 i) e he.2
          exact lt_of_lt_of_le h1 h2
        · intro e1 he1 e2 he2 h12
          rw [Finset.mem_coe, Finset.mem_filter, hbund] at he1 he2
          apply hinj
          ext
          · rw [he1.1, he2.1]
          · exact h12
      calc (((bundle (alloc σ) i).filter (fun e => rank (c i) e < r)).card : ℝ) ≤ ⌈X⌉₊ := by
            exact_mod_cast hcard
        _ < X + 1 := Nat.ceil_lt_add_one hX0
        _ = 1 + X := by ring

end ChoresTIE197.Main.Sol

-- ===== part E =====


namespace ChoresTIE197.Main.Sol
open ChoresTIE197.Main

variable {m : ℕ}

/-! ### Equal marginals give TIE and EF -/

lemma expectedCost_eq {n : ℕ} (p : Law n m) (ci : Fin m → ℝ≥0) (j : Fin n) :
    expectedCost p ci j = ∑ e, (ci e : ℝ) * marginal p j e := by
  unfold expectedCost marginal cost bundle
  simp_rw [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro e _
  apply Finset.sum_congr rfl; intro A _
  split_ifs <;> ring

lemma expectedCost_equal {n : ℕ} (p : Law n m) (hp : ∀ i e, marginal p i e = 1 / (n : ℝ))
    (ci : Fin m → ℝ≥0) (j : Fin n) : expectedCost p ci j = ∑ e, (ci e : ℝ) * (1 / n) := by
  rw [expectedCost_eq]; simp_rw [hp]

theorem main_of_laws {n : ℕ} (hn : 0 < n)
    (H : ∀ c : Profile n m, ∃ p : Law n m, (∀ i e, marginal p i e = 1 / (n : ℝ)) ∧
      ∀ A, p A ≠ 0 → ∀ i, cost (c i) (bundle A i) ≤ 197/100 * mms (c i) n univ) :
    ∃ F : Mechanism n m, TIEOn (fun _ => True) F ∧ EFOn (fun _ => True) F ∧
      MMSOn (fun _ => True) (197/100:ℝ) F := by
  choose F hF1 hF2 using H
  refine ⟨F, ?_, ?_, ?_⟩
  · intro c _ i r _
    rw [expectedCost_equal _ (hF1 c), expectedCost_equal _ (hF1 _)]
  · intro c _ i j
    rw [expectedCost_equal _ (hF1 c), expectedCost_equal _ (hF1 c)]
  · intro c _ A hA i
    exact hF2 c A hA i

/-! ### Mixtures of rounded fractional allocations -/

theorem mix {n : ℕ} [NeZero n] (c : Profile n m) {ι : Type} [Fintype ι] [Nonempty ι]
    (x : ι → Fraction n m) (hfeas : ∀ s, Feasible (x s))
    (havg : ∀ i e, ∑ s, x s i e = (Fintype.card ι : ℝ) / n)
    (Good : Allocation n m → Prop)
    (hgood : ∀ s A, (∀ i, SlotOK (c i) (x s i) (bundle A i)) → Good A) :
    ∃ p : Law n m, (∀ i e, marginal p i e = 1 / (n : ℝ)) ∧ ∀ A, p A ≠ 0 → Good A := by
  have hR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  choose P hPm hPs using fun s => rounding c (x s) (hfeas s)
  let w : ι × Allocation n m → ℝ := fun z => (P z.1 z.2).toReal / Fintype.card ι
  have hw0 : ∀ z, 0 ≤ w z := fun z => div_nonneg ENNReal.toReal_nonneg hR.le
  have hPsum : ∀ s, ∑ A, (P s A).toReal = 1 := by
    intro s
    rw [← ENNReal.toReal_sum (fun A _ => PMF.apply_ne_top _ _)]
    have : ∑ A, P s A = 1 := by
      have := (P s).tsum_coe; rwa [tsum_fintype] at this
    rw [this]; simp
  have hw1 : ∑ z, w z = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [w, ← Finset.sum_div, hPsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
    field_simp
  obtain ⟨p, hps, hpe⟩ := law_of_weights w hw0 hw1 (fun z => z.2)
  refine ⟨p, ?_, ?_⟩
  · intro i e
    have h1 : marginal p i e = ∑ A, (p A).toReal * (if A e = i then 1 else 0) := by
      unfold marginal; apply Finset.sum_congr rfl; intro A _; split_ifs <;> simp
    rw [h1, hpe, Fintype.sum_prod_type]
    have h2 : ∀ s, ∑ A, w (s, A) * (if A e = i then 1 else 0) = x s i e / Fintype.card ι := by
      intro s
      rw [← hPm s i e]
      unfold marginal
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl; intro A _
      simp only [w]; split_ifs <;> simp
    simp only [h2, ← Finset.sum_div, havg]
    field_simp
  · intro A hA
    obtain ⟨⟨s, A'⟩, hpos, rfl⟩ := hps A hA
    apply hgood s
    apply hPs s
    intro h0
    simp only [w, h0, ENNReal.toReal_zero, zero_div, lt_irrefl] at hpos

/-! ### Cost bounds from slot compatibility -/

lemma sum_top_indicator_rank (ci : Fin m → ℝ≥0) (k r : ℕ) :
    ∑ e ∈ top ci r, (if rank ci e = k then (1 : ℝ) else 0) = if k < r ∧ k < m then 1 else 0 := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  split_ifs with h
  · have : (top ci r).filter (fun e => rank ci e = k) = {(rankEquiv ci).symm ⟨k, h.2⟩} := by
      ext e
      simp only [Finset.mem_filter, mem_top, Finset.mem_singleton]
      constructor
      · rintro ⟨_, he⟩; rw [Equiv.eq_symm_apply]; ext; simp [he]
      · rintro rfl; rw [rank_symm]; exact ⟨h.1, rfl⟩
    rw [this]; simp
  · have : (top ci r).filter (fun e => rank ci e = k) = ∅ := by
      ext e
      simp only [Finset.mem_filter, mem_top, Finset.notMem_empty, iff_false, not_and]
      intro h1 h2; exact h ⟨h2 ▸ h1, h2 ▸ rank_lt_m ci e⟩
    rw [this]; simp

lemma sum_indicator_rank_mul (ci : Fin m → ℝ≥0) (k : ℕ) :
    ∑ e, (if rank ci e = k then (1 : ℝ) else 0) * ci e = sc ci k := by
  by_cases hk : k < m
  · rw [Finset.sum_eq_single ((rankEquiv ci).symm ⟨k, hk⟩)]
    · rw [rank_symm]; simp [sc, hk]
    · intro e _ he
      rw [if_neg]; · simp
      intro hek; apply he; rw [Equiv.eq_symm_apply]; ext; simp [hek]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [sc, hk]
    · intro e _; rw [if_neg]; · simp
      intro h; exact hk (h ▸ rank_lt_m ci e)

/-- General bound (Lemma 4.2, first part). -/
lemma bound_general (ci : Fin m → ℝ≥0) (xi : Fin m → ℝ) (hx : ∀ e, 0 ≤ xi e) (B : Finset (Fin m))
    (hB : SlotOK ci xi B) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ e, 0 < xi e → (ci e : ℝ) ≤ K) :
    cost ci B ≤ K + ∑ e, xi e * ci e := by
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · subst hBe
    have : 0 ≤ ∑ e, xi e * ci e := Finset.sum_nonneg (fun e _ => mul_nonneg (hx e) (by positivity))
    simp [cost]; linarith
  · obtain ⟨e0, he0B, he0min⟩ := B.exists_min_image (rank ci) hBne
    have hle := master_abel ci (fun e => xi e + if e = e0 then 1 else 0) B (by
      intro r
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
      by_cases hr : rank ci e0 < r
      · rw [if_pos ((mem_top _ _ _).mpr hr)]
        exact (hB.2 r).le.trans (by linarith)
      · rw [if_neg (by rw [mem_top]; exact hr)]
        have : B.filter (fun e => rank ci e < r) = ∅ := by
          ext e; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro he hlt; have := he0min e he; omega
        rw [this]; simp; exact Finset.sum_nonneg (fun e _ => hx e))
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq'] at hle
    simp only [Finset.mem_univ, if_true] at hle
    have := hK e0 (hB.1 e0 he0B)
    linarith

/-- Strengthened bound (Lemma 4.2, second part), with the hypothesis weakened to `≤ 1`. -/
lemma bound_strong (n : ℕ) (ci : Fin m → ℝ≥0) (xi : Fin m → ℝ) (hx : ∀ e, 0 ≤ xi e)
    (B : Finset (Fin m)) (hB : SlotOK ci xi B) (hXn : ∑ e ∈ top ci n, xi e ≤ 1) :
    cost ci B ≤ sc ci 0 + sc ci n + ∑ e ∈ univ \ top ci n, xi e * ci e := by
  set y : Fin m → ℝ := fun e => (if rank ci e = 0 then 1 else 0) + (if rank ci e = n then 1 else 0)
    + (if rank ci e < n then 0 else xi e)
  have hle := master_abel ci y B (by
    intro r
    simp only [y, Finset.sum_add_distrib, sum_top_indicator_rank]
    have htail : ∑ e ∈ top ci r, (if rank ci e < n then 0 else xi e) =
        ∑ e ∈ top ci r, xi e - ∑ e ∈ top ci (min r n), xi e := by
      have hA : ∑ e ∈ top ci r, (if rank ci e < n then 0 else xi e) = ∑ e ∈ top ci r, xi e -
          ∑ e ∈ top ci r, (if rank ci e < n then xi e else 0) := by
        rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro e _; split_ifs <;> ring
      have hB' : ∑ e ∈ top ci r, (if rank ci e < n then xi e else 0) =
          ∑ e ∈ top ci (min r n), xi e := by
        rw [← Finset.sum_filter]; congr 1; ext e; simp [mem_top]
      rw [hA, hB']
    rw [htail]
    have hcnt := hB.2 r
    have hmono : ∑ e ∈ top ci (min r n), xi e ≤ ∑ e ∈ top ci n, xi e :=
      Finset.sum_le_sum_of_subset_of_nonneg (by intro e; simp only [mem_top]; omega)
        (fun e _ _ => hx e)
    by_cases hr0 : r = 0
    · subst hr0
      have : B.filter (fun e => rank ci e < 0) = ∅ := by ext e; simp
      rw [this]; simp
    by_cases hm0 : m = 0
    · subst hm0
      have : B = ∅ := by ext e; exact Fin.elim0 e
      subst this; simp
      have : ∀ s : Finset (Fin 0), s = ∅ := fun s => by ext e; exact Fin.elim0 e
      simp [this (top ci r), this (top ci (min r n))]
    have h0 : (if 0 < r ∧ 0 < m then (1:ℝ) else 0) = 1 := by rw [if_pos ⟨by omega, by omega⟩]
    rw [h0]
    by_cases hrn : r ≤ n
    · rw [min_eq_left hrn, sub_self, add_zero]
      have : ((B.filter (fun e => rank ci e < r)).card : ℝ) < 2 := by
        have : ∑ e ∈ top ci r, xi e ≤ 1 := by rw [min_eq_left hrn] at hmono; linarith
        linarith
      have hc : (B.filter (fun e => rank ci e < r)).card ≤ 1 := by
        have : ((B.filter (fun e => rank ci e < r)).card : ℝ) < ((2 : ℕ) : ℝ) := by
          simpa using this
        have := Nat.cast_lt.mp this; omega
      have : 0 ≤ (if n < r ∧ n < m then (1:ℝ) else 0) := by split_ifs <;> norm_num
      have : ((B.filter (fun e => rank ci e < r)).card : ℝ) ≤ 1 := by exact_mod_cast hc
      linarith
    · push Not at hrn
      rw [min_eq_right hrn.le]
      by_cases hnm : n < m
      · rw [if_pos ⟨hrn, hnm⟩]; linarith
      · rw [if_neg (by omega)]
        have hsame : ∑ e ∈ top ci r, xi e = ∑ e ∈ top ci n, xi e := by
          rw [sum_top_of_le ci xi (by omega), sum_top_of_le ci xi (by omega)]
        rw [hsame] at hcnt ⊢
        have hc : (B.filter (fun e => rank ci e < r)).card ≤ 1 := by
          have : ((B.filter (fun e => rank ci e < r)).card : ℝ) < ((2 : ℕ) : ℝ) := by
            push_cast; linarith
          have := Nat.cast_lt.mp this; omega
        have : ((B.filter (fun e => rank ci e < r)).card : ℝ) ≤ 1 := by exact_mod_cast hc
        linarith)
  simp only [y, add_mul, Finset.sum_add_distrib, sum_indicator_rank_mul] at hle
  have : ∑ e, (if rank ci e < n then 0 else xi e) * ci e = ∑ e ∈ univ \ top ci n, xi e * ci e := by
    rw [← Finset.sum_sdiff (Finset.subset_univ (top ci n))]
    rw [Finset.sum_eq_zero (s := top ci n) (fun e he => by rw [mem_top] at he; simp [he])]
    rw [add_zero]
    apply Finset.sum_congr rfl; intro e he
    simp only [Finset.mem_sdiff, mem_top, Finset.mem_univ, true_and] at he
    simp [he]
  linarith

/-- Uniform bound (Lemma 3.1). -/
lemma bound_uniform (n : ℕ) (hn : 0 < n) (ci : Fin m → ℝ≥0) (B : Finset (Fin m))
    (hB : SlotOK ci (fun _ => 1 / (n : ℝ)) B) :
    cost ci B ≤ sc ci 0 + (cost ci univ - sc ci 0) / n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set y : Fin m → ℝ := fun e => (if rank ci e = 0 then 1 - 1 / (n : ℝ) else 0) + 1 / n
  have hle := master_abel ci y B (by
    intro r
    simp only [y, Finset.sum_add_distrib, Finset.sum_const, card_top, nsmul_eq_mul]
    have hind : ∑ e ∈ top ci r, (if rank ci e = 0 then 1 - 1 / (n : ℝ) else 0) =
        (1 - 1 / n) * (if 0 < r ∧ 0 < m then 1 else 0) := by
      rw [← sum_top_indicator_rank, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro e _; split_ifs <;> simp
    rw [hind]
    have hcnt := hB.2 r
    simp only [Finset.sum_const, card_top, nsmul_eq_mul] at hcnt
    set k := (B.filter (fun e => rank ci e < r)).card
    have hk_le : k ≤ min r m := by
      calc k ≤ (top ci r).card := by
            apply Finset.card_le_card; intro e; simp [mem_top]
        _ = min r m := card_top ci r
    by_cases hz : 0 < r ∧ 0 < m
    · rw [if_pos hz]
      -- integer argument: n (k - 1) < min r m  ⇒  n (k-1) ≤ min r m - 1
      have h1 : ((k : ℝ) - 1) * n < (min r m : ℕ) := by
        calc ((k:ℝ) - 1) * n < (((min r m : ℕ) : ℝ) * (1 / n)) * n :=
              mul_lt_mul_of_pos_right (by linarith) hnr
          _ = (min r m : ℕ) := by field_simp
      have h2 : (k : ℤ) * n < (min r m : ℕ) + n := by
        have : ((k : ℝ)) * n < (min r m : ℕ) + n := by linarith
        exact_mod_cast this
      have h3 : (k : ℤ) * n ≤ (min r m : ℕ) + n - 1 := by omega
      have h4 : (k : ℝ) * n ≤ (min r m : ℕ) + n - 1 := by exact_mod_cast h3
      rw [← mul_le_mul_iff_of_pos_right hnr]
      have : ((1 - 1 / (n:ℝ)) * 1 + ((min r m : ℕ) : ℝ) * (1 / n)) * n = n - 1 + (min r m : ℕ) := by
        field_simp
      rw [this]; linarith
    · rw [if_neg hz, mul_zero, zero_add]
      have : min r m = 0 := by omega
      rw [this] at hk_le
      have : k = 0 := by omega
      rw [this]; push_cast; positivity)
  simp only [y, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul] at hle
  have h1 : ∑ e, (if rank ci e = 0 then (1 - 1 / (n:ℝ)) * ci e else 0) = (1 - 1 / n) * sc ci 0 := by
    rw [← sum_indicator_rank_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro e _; split_ifs <;> simp
  have h2 : ∑ e, 1 / (n:ℝ) * ci e = cost ci univ / n := by
    unfold cost; rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro e _; ring
  rw [h1, h2] at hle
  have : sc ci 0 + (cost ci univ - sc ci 0) / n = (1 - 1 / n) * sc ci 0 + cost ci univ / n := by
    field_simp; ring
  linarith

end ChoresTIE197.Main.Sol

-- ===== part F =====


namespace ChoresTIE197.Main.Sol
open ChoresTIE197.Main

variable {m : ℕ}

def Gam (ci : Fin m → ℝ≥0) (n : ℕ) : ℝ := sc ci 0 + sc ci n + cost ci (univ \ top ci n) / n
def Eex (ci : Fin m → ℝ≥0) (n : ℕ) : ℝ := ∑ e, max 0 ((ci e : ℝ) - sc ci n)
def Hard (ci : Fin m → ℝ≥0) (n : ℕ) : Prop := 195/100 * Lb ci n < Gam ci n

lemma Eex_nonneg (ci : Fin m → ℝ≥0) (n : ℕ) : 0 ≤ Eex ci n :=
  Finset.sum_nonneg (fun e _ => le_max_left _ _)

lemma tot_eq (ci : Fin m → ℝ≥0) (n : ℕ) :
    cost ci univ = Eex ci n + n * sc ci n + cost ci (univ \ top ci n) := by
  have hpt : ∀ e, (ci e : ℝ) = max 0 ((ci e : ℝ) - sc ci n) + min (ci e : ℝ) (sc ci n) := by
    intro e
    rcases le_total (sc ci n) (ci e : ℝ) with h | h
    · rw [max_eq_right (by linarith), min_eq_right h]; ring
    · rw [max_eq_left (by linarith), min_eq_left h]; ring
  have hmin : ∑ e, min (ci e : ℝ) (sc ci n) = n * sc ci n + cost ci (univ \ top ci n) := by
    rw [← Finset.sum_sdiff (Finset.subset_univ (top ci n))]
    rw [add_comm]
    congr 1
    · rw [Finset.sum_congr rfl (fun e he => min_eq_right (sc_le_of_rank_le ci
        (le_of_lt ((mem_top _ _ _).mp he))))]
      rw [Finset.sum_const, card_top, nsmul_eq_mul]
      by_cases hnm : n < m
      · rw [min_eq_left hnm.le]
      · have : sc ci n = 0 := by simp [sc, hnm]
        rw [this]; simp
    · unfold cost
      apply Finset.sum_congr rfl; intro e he
      simp only [Finset.mem_sdiff, mem_top, Finset.mem_univ, true_and, not_lt] at he
      exact min_eq_left (le_sc_of_le_rank ci he)
  unfold cost Eex
  rw [Finset.sum_congr rfl (fun e _ => hpt e), Finset.sum_add_distrib, hmin]
  unfold cost; ring

lemma Gam_eq (ci : Fin m → ℝ≥0) {n : ℕ} (hn : 0 < n) :
    Gam ci n = sc ci 0 + (cost ci univ - Eex ci n) / n := by
  unfold Gam
  rw [tot_eq ci n]
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp; ring

lemma set_bound (ci : Fin m → ℝ≥0) (n : ℕ) (S : Finset (Fin m)) :
    cost ci S ≤ S.card * sc ci n + Eex ci n := by
  have h1 : cost ci S ≤ ∑ e ∈ S, (sc ci n + max 0 ((ci e : ℝ) - sc ci n)) := by
    unfold cost
    apply Finset.sum_le_sum; intro e _
    have := le_max_right 0 ((ci e : ℝ) - sc ci n); linarith
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ∑ e ∈ S, max 0 ((ci e : ℝ) - sc ci n) ≤ Eex ci n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun e _ _ => le_max_left _ _)
  linarith

lemma Gam_le (ci : Fin m → ℝ≥0) {n : ℕ} (hn : 0 < n) : Gam ci n ≤ 2 * Lb ci n := by
  rw [Gam_eq ci hn]
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have h1 := sc0_le_Lb ci n
  have h2 := tot_le_Lb hn ci
  have h3 := Eex_nonneg ci n
  have : (cost ci univ - Eex ci n) / n ≤ Lb ci n := by
    rw [div_le_iff₀ hnr]; linarith
  linarith

lemma hard_facts (ci : Fin m → ℝ≥0) {n : ℕ} (hn : 0 < n) (h : Hard ci n) :
    0 < Lb ci n ∧ n < m ∧ Eex ci n < n * (sc ci 0 - 95/100 * Lb ci n) ∧
      95/100 * n * Lb ci n + Eex ci n < cost ci univ ∧ 95/100 * Lb ci n < sc ci 0 := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  unfold Hard at h
  have hG := Gam_le ci hn
  have hL0 := Lb_nonneg ci n
  have hLpos : 0 < Lb ci n := by
    by_contra hc; push Not at hc
    have : Lb ci n = 0 := le_antisymm hc hL0
    rw [this] at h hG; linarith
  have h1 := sc0_le_Lb ci n
  have h2 := tot_le_Lb hn ci
  have h3 := Eex_nonneg ci n
  rw [Gam_eq ci hn] at h
  have key : 195/100 * Lb ci n - sc ci 0 < (cost ci univ - Eex ci n) / n := by linarith
  rw [lt_div_iff₀ hnr] at key
  have hE : Eex ci n < n * (sc ci 0 - 95/100 * Lb ci n) := by nlinarith
  have hs1 : 95/100 * Lb ci n < sc ci 0 := by
    by_contra hc; push Not at hc
    have : n * (sc ci 0 - 95/100 * Lb ci n) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hnr.le (by linarith)
    linarith
  refine ⟨hLpos, ?_, hE, ?_, hs1⟩
  · by_contra hnm; push Not at hnm
    have htop : top ci n = univ := top_of_le ci hnm
    have hsn : sc ci n = 0 := by simp [sc]; omega
    unfold Hard Gam at *
    have : 195/100 * Lb ci n < Gam ci n := by rw [Gam_eq ci hn]; linarith
    unfold Gam at this
    rw [htop, hsn, Finset.sdiff_self] at this
    simp [cost] at this
    linarith
  · nlinarith

lemma easy_uniform (ci : Fin m → ℝ≥0) {n : ℕ} (hn : 0 < n) (B : Finset (Fin m))
    (hB : SlotOK ci (fun _ => 1 / (n : ℝ)) B) : cost ci B ≤ Gam ci n := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have := bound_strong n ci (fun _ => 1 / (n : ℝ)) (fun _ => by positivity) B hB (by
    rw [Finset.sum_const, card_top, nsmul_eq_mul, mul_one_div, div_le_one hnr]
    exact_mod_cast min_le_left n m)
  unfold Gam
  have h2 : ∑ e ∈ univ \ top ci n, 1 / (n : ℝ) * ci e = cost ci (univ \ top ci n) / n := by
    unfold cost; rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro e _; ring
  linarith

/-- Small n: uniform rounding is (2 - 1/n)-MMS. -/
theorem small_case {n : ℕ} [NeZero n] (hn33 : n ≤ 33) (c : Profile n m) :
    ∃ p : Law n m, (∀ i e, marginal p i e = 1 / (n : ℝ)) ∧
      ∀ A, p A ≠ 0 → ∀ i, cost (c i) (bundle A i) ≤ 197/100 * mms (c i) n univ := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨p, hp1, hp2⟩ := mix c (ι := Unit) (fun _ _ _ => 1 / (n : ℝ))
    (fun _ => ⟨fun _ _ => by positivity, fun e => by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp⟩)
    (fun i e => by simp)
    (fun A => ∀ i, cost (c i) (bundle A i) ≤ 197/100 * mms (c i) n univ)
    (by
      intro s A hA i
      have h1 := bound_uniform n hn (c i) (bundle A i) (hA i)
      have h2 := sc0_le_Lb (c i) n
      have h3 := tot_le_Lb hn (c i)
      have h4 := Lb_le_mms hn (c i)
      have h5 := Lb_nonneg (c i) n
      have h6 : sc (c i) 0 + (cost (c i) univ - sc (c i) 0) / n ≤ (2 - 1 / n) * Lb (c i) n := by
        rw [show sc (c i) 0 + (cost (c i) univ - sc (c i) 0) / n =
          (1 - 1 / n) * sc (c i) 0 + cost (c i) univ / n by field_simp; ring]
        have : cost (c i) univ / n ≤ Lb (c i) n := by rw [div_le_iff₀ hnr]; linarith
        have : (1 - 1 / (n:ℝ)) * sc (c i) 0 ≤ (1 - 1 / n) * Lb (c i) n := by
          apply mul_le_mul_of_nonneg_left h2
          rw [sub_nonneg, div_le_one hnr]; exact_mod_cast hn
        linarith
      have h7 : (2 - 1 / (n:ℝ)) ≤ 197 / 100 := by
        have : (1:ℝ) / 33 ≤ 1 / n := by
          apply one_div_le_one_div_of_le hnr; exact_mod_cast hn33
        linarith
      calc cost (c i) (bundle A i) ≤ (2 - 1 / n) * Lb (c i) n := h1.trans h6
        _ ≤ 197 / 100 * Lb (c i) n := mul_le_mul_of_nonneg_right h7 h5
        _ ≤ 197 / 100 * mms (c i) n univ := by linarith)
  exact ⟨p, hp1, hp2⟩

end ChoresTIE197.Main.Sol

-- ===== part G =====


namespace ChoresTIE197.Main.Sol
open ChoresTIE197.Main

variable {m : ℕ}

def ind (S : Finset (Fin m)) (e : Fin m) : ℝ := if e ∈ S then 1 else 0

lemma sum_ind_mul (S' S : Finset (Fin m)) (c : Fin m → ℝ≥0) :
    ∑ e ∈ S', ind S e * c e = cost c (S' ∩ S) := by
  unfold cost ind
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]

lemma sum_ind (S' S : Finset (Fin m)) : ∑ e ∈ S', ind S e = ((S' ∩ S).card : ℝ) := by
  unfold ind
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.filter_mem_eq_inter]

lemma sum_univ_ind_mul (S : Finset (Fin m)) (c : Fin m → ℝ≥0) :
    ∑ e, ind S e * c e = cost c S := by
  rw [sum_ind_mul]; simp

section OneHard
variable {n : ℕ}

def Tset (c : Profile n m) (h : Fin n) : Finset (Fin m) :=
  univ.filter (fun e => 94/100 * Lb (c h) n < (c h e : ℝ))
def aj (c : Profile n m) (h j : Fin n) : ℝ :=
  ((Tset c h ∩ top (c j) n).card : ℝ) / ((top (c j) n \ Tset c h).card : ℝ)
def restj (c : Profile n m) (h j : Fin n) : ℝ := cost (c h) (univ \ (top (c j) n ∪ Tset c h))
def numj (c : Profile n m) (h j : Fin n) : ℝ :=
  cost (c h) (Tset c h) - aj c h j * cost (c h) (top (c j) n \ Tset c h) + 3/100 * n * Lb (c h) n
def bpar (c : Profile n m) (h : Fin n) : ℝ :=
  (∑ j ∈ univ.erase h, numj c h j) / (∑ j ∈ univ.erase h, restj c h j)
def Dl (n : ℕ) : ℝ := 1 / (n * (n - 1))
def dl (c : Profile n m) (h j : Fin n) (e : Fin m) : ℝ :=
  Dl n * ind (Tset c h) e - aj c h j * Dl n * ind (top (c j) n \ Tset c h) e
    - bpar c h * Dl n * ind (univ \ (top (c j) n ∪ Tset c h)) e
def X1 (c : Profile n m) (h : Fin n) (s : Bool) : Fraction n m := fun i e =>
  1 / n + (if s then 1 else -1) * (if i = h then ∑ j ∈ univ.erase h, dl c h j e else -dl c h i e)

lemma oh_Dl (hn : 19 ≤ n) : 0 < Dl n ∧ Dl n ≤ 1 / n ∧ ((n:ℝ) - 1) * Dl n = 1 / n ∧ n * Dl n ≤ 1 / 18 := by
  have hnr : (19:ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (0:ℝ) < n - 1 := by linarith
  unfold Dl
  refine ⟨by positivity, ?_, by field_simp, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  · rw [show (n:ℝ) * (1 / (n * (n - 1))) = 1 / (n - 1) by field_simp]
    rw [div_le_div_iff₀ h1 (by norm_num)]; linarith

variable (c : Profile n m) (h : Fin n) (hn : 19 ≤ n) (hh : Hard (c h) n)
include hn hh

lemma oh_basic : 0 < Lb (c h) n ∧ n < m ∧ Eex (c h) n < 5/100 * n * Lb (c h) n ∧
    95/100 * n * Lb (c h) n + Eex (c h) n < cost (c h) univ := by
  have hn0 : 0 < n := by omega
  obtain ⟨h1, h2, h3, h4, _⟩ := hard_facts (c h) hn0 hh
  have := sc0_le_Lb (c h) n
  have hnr : (0:ℝ) < n := by exact_mod_cast hn0
  refine ⟨h1, h2, ?_, h4⟩
  nlinarith

lemma oh_T : 44/100 * (Tset c h).card * Lb (c h) n ≤ Eex (c h) n ∧
    44 * ((Tset c h).card : ℝ) < 5 * n ∧
    cost (c h) (Tset c h) ≤ (Tset c h).card * (Lb (c h) n / 2) + Eex (c h) n := by
  obtain ⟨hL, _, hE, _⟩ := oh_basic c h hn hh
  have hsn := scn_le_Lb (c h) n
  have h1 : 44/100 * (Tset c h).card * Lb (c h) n ≤ Eex (c h) n := by
    unfold Eex
    calc 44/100 * ((Tset c h).card : ℝ) * Lb (c h) n
        = ∑ e ∈ Tset c h, 44/100 * Lb (c h) n := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ e ∈ Tset c h, max 0 ((c h e : ℝ) - sc (c h) n) := by
          apply Finset.sum_le_sum; intro e he
          simp only [Tset, Finset.mem_filter, Finset.mem_univ, true_and] at he
          have := le_max_right 0 ((c h e : ℝ) - sc (c h) n)
          linarith
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun e _ _ => le_max_left _ _)
  refine ⟨h1, ?_, ?_⟩
  · nlinarith
  · have := set_bound (c h) n (Tset c h)
    have h0 : (0:ℝ) ≤ (Tset c h).card := by positivity
    nlinarith

lemma oh_top_card (j : Fin n) : (top (c j) n).card = n := by
  rw [card_top]; exact min_eq_left (oh_basic c h hn hh).2.1.le

lemma oh_split (j : Fin n) : ((top (c j) n \ Tset c h).card : ℝ) +
    ((Tset c h ∩ top (c j) n).card : ℝ) = n := by
  have := Finset.card_sdiff_add_card_inter (top (c j) n) (Tset c h)
  rw [oh_top_card c h hn hh j, Finset.inter_comm] at this
  exact_mod_cast this

lemma oh_inter_le (j : Fin n) : ((Tset c h ∩ top (c j) n).card : ℝ) ≤ (Tset c h).card := by
  exact_mod_cast Finset.card_le_card Finset.inter_subset_left

lemma oh_sdiff_pos (j : Fin n) : (39:ℝ) / 44 * n < ((top (c j) n \ Tset c h).card : ℝ) := by
  have := oh_split c h hn hh j
  have := oh_inter_le c h hn hh j
  have := (oh_T c h hn hh).2.1
  linarith

lemma oh_aj (j : Fin n) : 0 ≤ aj c h j ∧ aj c h j ≤ 1 ∧
    aj c h j * ((top (c j) n \ Tset c h).card : ℝ) = ((Tset c h ∩ top (c j) n).card : ℝ) := by
  have hpos := oh_sdiff_pos c h hn hh j
  have hnr : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : (0:ℝ) < ((top (c j) n \ Tset c h).card : ℝ) := by nlinarith
  unfold aj
  refine ⟨by positivity, ?_, by field_simp⟩
  rw [div_le_one hd]
  have := oh_inter_le c h hn hh j
  have := (oh_T c h hn hh).2.1
  nlinarith

lemma oh_rest (j : Fin n) : 173/440 * n * Lb (c h) n < restj c h j := by
  obtain ⟨hL, _, hE, htot⟩ := oh_basic c h hn hh
  obtain ⟨hT1, hT2, _⟩ := oh_T c h hn hh
  have hsn := scn_le_Lb (c h) n
  unfold restj
  have hsplit : cost (c h) univ = cost (c h) (univ \ (top (c j) n ∪ Tset c h)) +
      cost (c h) (top (c j) n ∪ Tset c h) := by
    unfold cost; rw [Finset.sum_sdiff (Finset.subset_univ _)]
  have hU := set_bound (c h) n (top (c j) n ∪ Tset c h)
  have hcard : ((top (c j) n ∪ Tset c h).card : ℝ) ≤ n + (Tset c h).card := by
    have := Finset.card_union_le (top (c j) n) (Tset c h)
    rw [oh_top_card c h hn hh j] at this; exact_mod_cast this
  have hsn0 := sc_nonneg (c h) n
  have : ((top (c j) n ∪ Tset c h).card : ℝ) * sc (c h) n ≤
      (n + (Tset c h).card) * (Lb (c h) n / 2) := by
    apply mul_le_mul hcard (by linarith) hsn0 (by positivity)
  nlinarith

lemma oh_num (j : Fin n) : 3/100 * n * Lb (c h) n ≤ numj c h j ∧
    numj c h j < 35/100 * restj c h j := by
  obtain ⟨hL, _, hE, _⟩ := oh_basic c h hn hh
  obtain ⟨hT1, hT2, hT3⟩ := oh_T c h hn hh
  obtain ⟨ha0, ha1, ha2⟩ := oh_aj c h hn hh j
  have hrest := oh_rest c h hn hh j
  have hcHT : cost (c h) (top (c j) n \ Tset c h) ≤
      94/100 * Lb (c h) n * ((top (c j) n \ Tset c h).card : ℝ) := by
    unfold cost
    calc ∑ e ∈ top (c j) n \ Tset c h, (c h e : ℝ) ≤ ∑ e ∈ top (c j) n \ Tset c h,
        94/100 * Lb (c h) n := by
          apply Finset.sum_le_sum; intro e he
          simp only [Finset.mem_sdiff, Tset, Finset.mem_filter, Finset.mem_univ, true_and,
            not_lt] at he
          exact he.2
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hcTH : 94/100 * Lb (c h) n * ((Tset c h ∩ top (c j) n).card : ℝ) ≤ cost (c h) (Tset c h) := by
    calc 94/100 * Lb (c h) n * ((Tset c h ∩ top (c j) n).card : ℝ)
        = ∑ e ∈ Tset c h ∩ top (c j) n, 94/100 * Lb (c h) n := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ cost (c h) (Tset c h ∩ top (c j) n) := by
          unfold cost
          apply Finset.sum_le_sum; intro e he
          simp only [Finset.mem_inter, Tset, Finset.mem_filter, Finset.mem_univ, true_and] at he
          exact he.1.le
      _ ≤ cost (c h) (Tset c h) := cost_mono _ Finset.inter_subset_left
  have hprod : aj c h j * cost (c h) (top (c j) n \ Tset c h) ≤ cost (c h) (Tset c h) := by
    calc aj c h j * cost (c h) (top (c j) n \ Tset c h)
        ≤ aj c h j * (94/100 * Lb (c h) n * ((top (c j) n \ Tset c h).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hcHT ha0
      _ = 94/100 * Lb (c h) n * ((Tset c h ∩ top (c j) n).card : ℝ) := by rw [← ha2]; ring
      _ ≤ _ := hcTH
  have hprod0 : 0 ≤ aj c h j * cost (c h) (top (c j) n \ Tset c h) :=
    mul_nonneg ha0 (cost_nonneg _ _)
  unfold numj
  constructor
  · linarith
  · nlinarith

lemma oh_card_erase : ((univ.erase h).card : ℝ) = n - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ h), Finset.card_univ, Fintype.card_fin]
  have : 1 ≤ n := by omega
  push_cast [this]; ring

lemma oh_b : 0 < ∑ j ∈ univ.erase h, restj c h j ∧ 0 ≤ bpar c h ∧ bpar c h ≤ 35/100 ∧
    bpar c h * (∑ j ∈ univ.erase h, restj c h j) = ∑ j ∈ univ.erase h, numj c h j := by
  obtain ⟨hL, _, _, _⟩ := oh_basic c h hn hh
  have hnr : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hne : (univ.erase h).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ h)]; simp; omega
  have hden : 0 < ∑ j ∈ univ.erase h, restj c h j := by
    apply Finset.sum_pos _ hne
    intro j _
    have := oh_rest c h hn hh j
    have : 0 < 173/440 * n * Lb (c h) n := by positivity
    linarith
  have hnum0 : 0 ≤ ∑ j ∈ univ.erase h, numj c h j := by
    apply Finset.sum_nonneg; intro j _
    have := (oh_num c h hn hh j).1
    have : 0 ≤ 3/100 * n * Lb (c h) n := by positivity
    linarith
  have hnum1 : ∑ j ∈ univ.erase h, numj c h j ≤ 35/100 * ∑ j ∈ univ.erase h, restj c h j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => (oh_num c h hn hh j).2.le)
  unfold bpar
  refine ⟨hden, div_nonneg hnum0 hden.le, ?_, ?_⟩
  · rw [div_le_iff₀ hden]; exact hnum1
  · field_simp

lemma oh_dl_cases (j : Fin n) (e : Fin m) :
    (e ∈ Tset c h → dl c h j e = Dl n) ∧ (e ∉ Tset c h → -Dl n ≤ dl c h j e ∧ dl c h j e ≤ 0) := by
  obtain ⟨ha0, ha1, _⟩ := oh_aj c h hn hh j
  obtain ⟨_, hb0, hb1, _⟩ := oh_b c h hn hh
  obtain ⟨hD, _, _, _⟩ := oh_Dl (n := n) hn
  unfold dl ind
  constructor
  · intro he
    simp [he]
  · intro he
    by_cases h2 : e ∈ top (c j) n
    · simp only [he, h2, if_false, Finset.mem_sdiff, not_false_eq_true, and_self, if_true,
        Finset.mem_union, or_false, Finset.mem_univ, true_and, not_true_eq_false]
      constructor <;> nlinarith
    · simp only [he, h2, if_false, Finset.mem_sdiff, false_and, Finset.mem_union, or_self,
        not_false_eq_true, and_self, if_true, Finset.mem_univ]
      constructor <;> nlinarith

lemma oh_dl_abs (j : Fin n) (e : Fin m) : -Dl n ≤ dl c h j e ∧ dl c h j e ≤ Dl n := by
  have hD := (oh_Dl (n := n) hn).1
  by_cases he : e ∈ Tset c h
  · rw [(oh_dl_cases c h hn hh j e).1 he]; constructor <;> linarith
  · have := (oh_dl_cases c h hn hh j e).2 he; constructor <;> linarith

lemma oh_S (e : Fin m) :
    (e ∈ Tset c h → ∑ j ∈ univ.erase h, dl c h j e = 1 / n) ∧
    (e ∉ Tset c h → -(1 / (n:ℝ)) ≤ ∑ j ∈ univ.erase h, dl c h j e ∧
      ∑ j ∈ univ.erase h, dl c h j e ≤ 0) := by
  obtain ⟨_, _, hD3, _⟩ := oh_Dl (n := n) hn
  have hcard := oh_card_erase c h hn hh
  constructor
  · intro he
    rw [Finset.sum_congr rfl (fun j _ => (oh_dl_cases c h hn hh j e).1 he), Finset.sum_const,
      nsmul_eq_mul, hcard, hD3]
  · intro he
    constructor
    · calc -(1 / (n:ℝ)) = ∑ j ∈ univ.erase h, -Dl n := by
            rw [Finset.sum_const, nsmul_eq_mul, hcard, ← hD3]; ring
        _ ≤ _ := Finset.sum_le_sum (fun j _ => ((oh_dl_cases c h hn hh j e).2 he).1)
    · exact Finset.sum_nonpos (fun j _ => ((oh_dl_cases c h hn hh j e).2 he).2)

lemma oh_feasible (s : Bool) : Feasible (X1 c h s) := by
  have hnr : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨_, hD2, _, _⟩ := oh_Dl (n := n) hn
  constructor
  · intro i e
    unfold X1
    by_cases hi : i = h
    · rw [if_pos hi]
      by_cases he : e ∈ Tset c h
      · rw [(oh_S c h hn hh e).1 he]
        cases s
        · simp only [Bool.false_eq_true, if_false]; linarith
        · simp only [if_true]; positivity
      · have := (oh_S c h hn hh e).2 he
        have h1n : (0:ℝ) ≤ 1 / n := by positivity
        cases s
        · simp only [Bool.false_eq_true, if_false]; linarith
        · simp only [if_true]; linarith
    · rw [if_neg hi]
      have := oh_dl_abs c h hn hh i e
      cases s
      · simp only [Bool.false_eq_true, if_false]; linarith
      · simp only [if_true]; linarith
  · intro e
    unfold X1
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ h)]
    rw [if_pos rfl, Finset.sum_congr rfl (fun i hi => if_neg (Finset.ne_of_mem_erase hi))]
    rw [Finset.sum_neg_distrib]
    field_simp
    ring

lemma oh_avg (i : Fin n) (e : Fin m) : ∑ s : Bool, X1 c h s i e = (Fintype.card Bool : ℝ) / n := by
  unfold X1
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_true, if_false, Fintype.card_bool]
  push_cast; ring

lemma oh_cost_h (s : Bool) :
    ∑ e, X1 c h s h e * c h e = cost (c h) univ / n -
      (if s then 1 else -1) * (3/100 * Lb (c h) n) := by
  obtain ⟨hden, _, _, hbd⟩ := oh_b c h hn hh
  obtain ⟨_, _, hD3, _⟩ := oh_Dl (n := n) hn
  have hcard := oh_card_erase c h hn hh
  have hnr : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hinner : ∀ j, ∑ e, dl c h j e * c h e = Dl n * cost (c h) (Tset c h)
      - aj c h j * Dl n * cost (c h) (top (c j) n \ Tset c h) - bpar c h * Dl n * restj c h j := by
    intro j
    unfold dl restj
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, sum_univ_ind_mul]
  have hsum : ∑ e, (∑ j ∈ univ.erase h, dl c h j e) * c h e = -(3/100 * Lb (c h) n) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun j _ => hinner j)]
    set A := ∑ j ∈ univ.erase h, (cost (c h) (Tset c h) - aj c h j * cost (c h) (top (c j) n \ Tset c h))
    have hA1 : ∑ j ∈ univ.erase h, (Dl n * cost (c h) (Tset c h)
        - aj c h j * Dl n * cost (c h) (top (c j) n \ Tset c h) - bpar c h * Dl n * restj c h j)
        = Dl n * A - Dl n * (bpar c h * ∑ j ∈ univ.erase h, restj c h j) := by
      simp only [A, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    have hA2 : ∑ j ∈ univ.erase h, numj c h j = A + (n - 1) * (3/100 * n * Lb (c h) n) := by
      unfold numj
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    rw [hA1, hbd, hA2]
    have : Dl n * ((n:ℝ) - 1) = 1 / n := by rw [mul_comm]; exact hD3
    have hn0 : (n:ℝ) ≠ 0 := hnr.ne'
    calc Dl n * A - Dl n * (A + (↑n - 1) * (3 / 100 * ↑n * Lb (c h) n))
        = -((Dl n * ((n:ℝ) - 1)) * n * (3/100 * Lb (c h) n)) := by ring
      _ = -(3 / 100 * Lb (c h) n) := by rw [this]; field_simp
  have hx : ∀ e, X1 c h s h e * c h e = 1 / n * c h e +
      (if s then 1 else -1) * ((∑ j ∈ univ.erase h, dl c h j e) * c h e) := by
    intro e; unfold X1; rw [if_pos rfl]; ring
  have hsum2 : ∑ e, (if s then (1:ℝ) else -1) * ((∑ j ∈ univ.erase h, dl c h j e) * c h e) =
      (if s then (1:ℝ) else -1) * -(3 / 100 * Lb (c h) n) := by rw [← Finset.mul_sum, hsum]
  rw [Finset.sum_congr rfl (fun e _ => hx e), Finset.sum_add_distrib, hsum2]
  rw [show ∑ e, 1 / (n:ℝ) * c h e = cost (c h) univ / n by
    unfold cost; rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro e _; ring]
  ring

lemma oh_good_h (s : Bool) (B : Finset (Fin m)) (hB : SlotOK (c h) (X1 c h s h) B) :
    cost (c h) B ≤ 197/100 * Lb (c h) n := by
  obtain ⟨hL, _, _, _⟩ := oh_basic c h hn hh
  have hnr : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfeas := oh_feasible c h hn hh s
  have htot : cost (c h) univ / n ≤ Lb (c h) n := by
    rw [div_le_iff₀ hnr]; have := tot_le_Lb (show 0 < n by omega) (c h); linarith
  have hcost := oh_cost_h c h hn hh s
  cases s
  · -- s = false: no chore of T has positive fraction
    have := bound_general (c h) _ (hfeas.1 h) B hB (94/100 * Lb (c h) n) (by positivity) (by
      intro e he
      by_contra hc
      push Not at hc
      have heT : e ∈ Tset c h := by simp [Tset]; exact hc
      have := (oh_S c h hn hh e).1 heT
      simp only [X1, if_pos rfl, this] at he
      simp at he)
    simp at hcost
    linarith
  · have := bound_general (c h) _ (hfeas.1 h) B hB (sc (c h) 0) (sc_nonneg _ _)
      (fun e _ => le_sc_zero _ e)
    have := sc0_le_Lb (c h) n
    simp at hcost
    linarith

lemma oh_good_j (s : Bool) (j : Fin n) (hj : j ≠ h) (hje : ¬ Hard (c j) n) (B : Finset (Fin m))
    (hB : SlotOK (c j) (X1 c h s j) B) : cost (c j) B ≤ 197/100 * Lb (c j) n := by
  have hn0 : 0 < n := by omega
  have hnr : (0:ℝ) < n := by exact_mod_cast hn0
  have hfeas := oh_feasible c h hn hh s
  obtain ⟨_, hb0, hb1, _⟩ := oh_b c h hn hh
  obtain ⟨hD, _, _, hD4⟩ := oh_Dl (n := n) hn
  obtain ⟨_, _, ha2⟩ := oh_aj c h hn hh j
  have hT2 := (oh_T c h hn hh).2.1
  set H := top (c j) n
  set T := Tset c h
  have hXj : ∀ e, X1 c h s j e = 1 / n - (if s then 1 else -1) * dl c h j e := by
    intro e; unfold X1; rw [if_neg hj]; ring
  -- top-n mass is exactly 1
  have hdlH : ∑ e ∈ H, dl c h j e = 0 := by
    unfold dl
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_ind]
    have h1 : H ∩ (H \ T) = H \ T := by ext e; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, Finset.notMem_empty, iff_false, false_iff]; tauto
    have h2 : H ∩ (univ \ (H ∪ T)) = ∅ := by ext e; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, Finset.notMem_empty, iff_false, false_iff]; tauto
    rw [h1, h2, Finset.inter_comm]
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero]
    rw [mul_comm (aj c h j) (Dl n), mul_assoc, ha2]; ring
  have hmass : ∑ e ∈ H, X1 c h s j e ≤ 1 := by
    simp_rw [hXj]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hdlH, Finset.sum_const, oh_top_card c h hn hh j]
    simp; field_simp; rfl
  have hbnd := bound_strong n (c j) (X1 c h s j) (hfeas.1 j) B hB hmass
  -- the tail sum
  have htail : ∑ e ∈ univ \ H, X1 c h s j e * c j e = cost (c j) (univ \ H) / n -
      (if s then 1 else -1) * (Dl n * cost (c j) (T \ H)
        - bpar c h * Dl n * cost (c j) (univ \ (H ∪ T))) := by
    simp_rw [hXj, sub_mul, Finset.sum_sub_distrib]
    congr 1
    · unfold cost; rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro e _; ring
    · simp only [mul_assoc, ← Finset.mul_sum]
      congr 1
      unfold dl
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, sum_ind_mul]
      have h1 : (univ \ H) ∩ T = T \ H := by ext e; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, Finset.notMem_empty, iff_false, false_iff]; tauto
      have h2 : (univ \ H) ∩ (H \ T) = ∅ := by ext e; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, Finset.notMem_empty, iff_false, false_iff]; tauto
      have h3 : (univ \ H) ∩ (univ \ (H ∪ T)) = univ \ (H ∪ T) := by ext e; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, Finset.notMem_empty, iff_false, false_iff]; tauto
      rw [h1, h2, h3]; simp [cost]
  have hG : Gam (c j) n ≤ 195/100 * Lb (c j) n := by unfold Hard at hje; push Not at hje; exact hje
  have hLj := Lb_nonneg (c j) n
  have htotj := tot_le_Lb hn0 (c j)
  have hsnj := scn_le_Lb (c j) n
  have hrest_le : cost (c j) (univ \ (H ∪ T)) ≤ cost (c j) univ := cost_mono _ (Finset.subset_univ _)
  have hTH : cost (c j) (T \ H) ≤ T.card * (Lb (c j) n / 2) := by
    calc cost (c j) (T \ H) ≤ ∑ e ∈ T \ H, sc (c j) n := by
          unfold cost; apply Finset.sum_le_sum; intro e he
          rw [Finset.mem_sdiff] at he
          have h2 : ¬ rank (c j) e < n := fun hh' => he.2 ((mem_top _ _ _).mpr hh')
          exact le_sc_of_le_rank _ (not_lt.mp h2)
      _ = (T \ H).card * sc (c j) n := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ T.card * (Lb (c j) n / 2) := by
          apply mul_le_mul _ (by linarith) (sc_nonneg _ _) (Nat.cast_nonneg _)
          exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  have hTH0 : 0 ≤ cost (c j) (T \ H) := cost_nonneg _ _
  have hrest0 : 0 ≤ cost (c j) (univ \ (H ∪ T)) := cost_nonneg _ _
  rw [htail] at hbnd
  have hGam : Gam (c j) n = sc (c j) 0 + sc (c j) n + cost (c j) (univ \ H) / n := rfl
  cases s
  · simp at hbnd
    -- extra ≤ Dl * |T| * L/2
    have : Dl n * cost (c j) (T \ H) ≤ 2 / 100 * Lb (c j) n := by
      have h1 : Dl n * cost (c j) (T \ H) ≤ Dl n * (T.card * (Lb (c j) n / 2)) :=
        mul_le_mul_of_nonneg_left hTH hD.le
      have h2 : Dl n * (T.card * (Lb (c j) n / 2)) ≤ 2 / 100 * Lb (c j) n := by
        have : Dl n * T.card ≤ 5 / 44 * (n * Dl n) := by nlinarith
        nlinarith
      linarith
    have : 0 ≤ bpar c h * Dl n * cost (c j) (univ \ (H ∪ T)) := by positivity
    linarith
  · simp at hbnd
    have : bpar c h * Dl n * cost (c j) (univ \ (H ∪ T)) ≤ 2 / 100 * Lb (c j) n := by
      have h1 : bpar c h * Dl n * cost (c j) (univ \ (H ∪ T)) ≤ 35/100 * Dl n * (n * Lb (c j) n) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hb1 hD.le) (by linarith) hrest0 (by positivity)
      nlinarith
    have : 0 ≤ Dl n * cost (c j) (T \ H) := by positivity
    linarith

theorem one_hard_case [NeZero n] (heasy : ∀ j, j ≠ h → ¬ Hard (c j) n) :
    ∃ p : Law n m, (∀ i e, marginal p i e = 1 / (n : ℝ)) ∧
      ∀ A, p A ≠ 0 → ∀ i, cost (c i) (bundle A i) ≤ 197/100 * Lb (c i) n := by
  obtain ⟨p, hp1, hp2⟩ := mix c (ι := Bool) (X1 c h) (oh_feasible c h hn hh)
    (oh_avg c h hn hh) (fun A => ∀ i, cost (c i) (bundle A i) ≤ 197/100 * Lb (c i) n) (by
      intro s A hA i
      by_cases hi : i = h
      · subst hi; exact oh_good_h c i hn hh s _ (hA i)
      · exact oh_good_j c h hn hh s i hi (heasy i hi) _ (hA i))
  exact ⟨p, hp1, hp2⟩

end OneHard

end ChoresTIE197.Main.Sol

-- ===== part H =====


namespace ChoresTIE197.Main.Sol
open ChoresTIE197.Main

variable {m n : ℕ}

/-! ### Grouping hard agents into pairs and triples -/

def IsGrouping (Q : Finset (Fin n)) (G : Fin n → Finset (Fin n)) : Prop :=
  ∀ i ∈ Q, i ∈ G i ∧ G i ⊆ Q ∧ ((G i).card = 2 ∨ (G i).card = 3) ∧ ∀ j ∈ G i, G j = G i

lemma exists_grouping : ∀ (k : ℕ) (Q : Finset (Fin n)), Q.card = k → 2 ≤ k →
    ∃ G, IsGrouping Q G := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro Q hk h2
  by_cases h3 : k ≤ 3
  · refine ⟨fun _ => Q, fun i hi => ⟨hi, subset_refl _, by show Q.card = 2 ∨ Q.card = 3; omega, fun j _ => rfl⟩⟩
  · have hne : Q.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨a, ha⟩ := hne
    have hne' : (Q.erase a).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem ha]; omega
    obtain ⟨b, hb⟩ := hne'
    have hab : b ≠ a := Finset.ne_of_mem_erase hb
    have hbQ : b ∈ Q := Finset.mem_of_mem_erase hb
    set Q' := (Q.erase a).erase b
    have hQ' : Q'.card = k - 2 := by
      rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]; omega
    obtain ⟨G', hG'⟩ := ih (k - 2) (by omega) Q' hQ' (by omega)
    refine ⟨fun i => if i = a ∨ i = b then {a, b} else G' i, ?_⟩
    intro i hi
    by_cases hiab : i = a ∨ i = b
    · simp only [if_pos hiab]
      refine ⟨by rcases hiab with rfl | rfl <;> simp, ?_, ?_, ?_⟩
      · intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
      · left; rw [Finset.card_pair hab.symm]
      · intro j hj; simp at hj; rw [if_pos hj]
    · simp only [if_neg hiab]
      push Not at hiab
      have hiQ' : i ∈ Q' := by simp [Q', hi, hiab.1, hiab.2]
      obtain ⟨h1, h2, h3, h4⟩ := hG' i hiQ'
      refine ⟨h1, h2.trans (fun x hx => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)), h3, ?_⟩
      intro j hj
      have hjQ' := h2 hj
      have hja : ¬ (j = a ∨ j = b) := by
        simp only [Q', Finset.mem_erase] at hjQ'
        push Not; exact ⟨hjQ'.2.1, hjQ'.1⟩
      rw [if_neg hja]; exact h4 j hj

lemma grouping_double_count (Q : Finset (Fin n)) (G : Fin n → Finset (Fin n))
    (hG : IsGrouping Q G) (F : Fin n → ℝ) :
    ∑ i ∈ Q, F i = ∑ i ∈ Q, (1 / ((G i).card : ℝ)) * ∑ j ∈ G i, F j := by
  have hfib : ∀ j ∈ Q, Q.filter (fun i => j ∈ G i) = G j := by
    intro j hj
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, hji⟩
      rw [(hG i hi).2.2.2 j hji]; exact (hG i hi).1
    · intro hij
      have hiQ := (hG j hj).2.1 hij
      refine ⟨hiQ, ?_⟩
      rw [(hG j hj).2.2.2 i hij]; exact (hG j hj).1
  have rhs : ∑ i ∈ Q, (1 / ((G i).card : ℝ)) * ∑ j ∈ G i, F j =
      ∑ i ∈ Q, ∑ j ∈ Q, (if j ∈ G i then F j / (G i).card else 0) := by
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.mul_sum, ← Finset.sum_subset (hG i hi).2.1]
    · apply Finset.sum_congr rfl; intro j hj; rw [if_pos hj]; ring
    · intro j _ hj; rw [if_neg hj]
  rw [rhs, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j hj
  rw [← Finset.sum_filter, hfib j hj]
  rw [Finset.sum_congr rfl (fun i hi => by rw [(hG j hj).2.2.2 i hi])]
  rw [Finset.sum_const, nsmul_eq_mul]
  have : (0:ℝ) < (G j).card := by
    have := (hG j hj).2.2.1; rcases this with h | h <;> rw [h] <;> norm_num
  field_simp

/-- selected member of a group at time t. -/
def sel [NeZero n] (G : Finset (Fin n)) (t : Fin 6) : Fin n :=
  if h2 : G.card = 2 then G.orderEmbOfFin h2 ⟨t.val % 2, Nat.mod_lt _ (by norm_num)⟩
  else if h3 : G.card = 3 then G.orderEmbOfFin h3 ⟨t.val % 3, Nat.mod_lt _ (by norm_num)⟩
  else 0

lemma sel_mem [NeZero n] (G : Finset (Fin n)) (hG : G.card = 2 ∨ G.card = 3) (t : Fin 6) :
    sel G t ∈ G := by
  unfold sel
  rcases hG with h | h
  · rw [dif_pos h]; exact Finset.orderEmbOfFin_mem _ _ _
  · rw [dif_neg (by omega), dif_pos h]; exact Finset.orderEmbOfFin_mem _ _ _

lemma sum_sel [NeZero n] (G : Finset (Fin n)) (hG : G.card = 2 ∨ G.card = 3) (f : Fin n → ℝ) :
    ∑ t : Fin 6, f (sel G t) = (6 / (G.card : ℝ)) * ∑ l ∈ G, f l := by
  rcases hG with h | h
  · have hs : ∑ l ∈ G, f l = ∑ k : Fin 2, f (G.orderEmbOfFin h k) := by
      conv_lhs => rw [← Finset.map_orderEmbOfFin_univ G h]
      rw [Finset.sum_map]; rfl
    rw [hs, h, Fin.sum_univ_two, Fin.sum_univ_six]
    simp only [sel, dif_pos h]
    norm_num
    ring_nf
  · have hs : ∑ l ∈ G, f l = ∑ k : Fin 3, f (G.orderEmbOfFin h k) := by
      conv_lhs => rw [← Finset.map_orderEmbOfFin_univ G h]
      rw [Finset.sum_map]; rfl
    rw [hs, h, Fin.sum_univ_three, Fin.sum_univ_six]
    simp only [sel, dif_neg (show ¬ G.card = 2 by omega), dif_pos h]
    norm_num
    ring_nf
    rfl


/-! ### Group fractions -/

def gS (c : Profile n m) (q : ℕ) (G : Finset (Fin n)) (i : Fin n) (e : Fin m) : ℝ :=
  ∑ l ∈ G.erase i, ind (top (c i) q ∪ top (c l) q) e

def gfrac (c : Profile n m) (q : ℕ) (G : Finset (Fin n)) (sl i : Fin n) (e : Fin m) : ℝ :=
  if i = sl then
    (if G.card = 2 then 1 / (2 * n) * (1 + 3 * gS c q G i e) else 3 / (2 * n) * gS c q G i e)
  else 3 / (2 * n) * (1 - ind (top (c i) q ∪ top (c sl) q) e)

lemma ind_nonneg (S : Finset (Fin m)) (e : Fin m) : 0 ≤ ind S e := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one (S : Finset (Fin m)) (e : Fin m) : ind S e ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

lemma gS_nonneg (c : Profile n m) (q : ℕ) (G : Finset (Fin n)) (i : Fin n) (e : Fin m) :
    0 ≤ gS c q G i e := Finset.sum_nonneg (fun _ _ => ind_nonneg _ _)

lemma gfrac_nonneg (c : Profile n m) (q : ℕ) (G : Finset (Fin n)) (sl i : Fin n) (e : Fin m) :
    0 ≤ gfrac c q G sl i e := by
  unfold gfrac
  have := gS_nonneg c q G i e
  have := ind_le_one (top (c i) q ∪ top (c sl) q) e
  split_ifs <;> [positivity; positivity; exact mul_nonneg (by positivity) (by linarith)]

lemma gS_comm (c : Profile n m) (q : ℕ) (G : Finset (Fin n)) (sl : Fin n) (e : Fin m) :
    ∑ i ∈ G.erase sl, ind (top (c i) q ∪ top (c sl) q) e = gS c q G sl e := by
  unfold gS; apply Finset.sum_congr rfl; intro i _; rw [Finset.union_comm]

lemma g_algebra (n : ℕ) (hn : 0 < n) (G : Finset (Fin n)) (hG : G.card = 2 ∨ G.card = 3)
    (i : Fin n) (hi : i ∈ G) (S : ℝ) :
    (if G.card = 2 then 1 / (2 * (n:ℝ)) * (1 + 3 * S) else 3 / (2 * n) * S) +
      3 / (2 * n) * (((G.erase i).card : ℝ) - S) = G.card / n := by
  have hnr : (n:ℝ) ≠ 0 := by positivity
  rw [Finset.card_erase_of_mem hi]
  rcases hG with h | h
  · rw [if_pos h, h]; push_cast; field_simp; ring
  · rw [if_neg (by omega), h]; push_cast; field_simp; ring

lemma gsum (c : Profile n m) (q : ℕ) (hn : 0 < n) (G : Finset (Fin n))
    (hG : G.card = 2 ∨ G.card = 3) (sl : Fin n) (hsl : sl ∈ G) (e : Fin m) :
    ∑ i ∈ G, gfrac c q G sl i e = G.card / n := by
  rw [← Finset.add_sum_erase G _ hsl]
  rw [Finset.sum_congr rfl (fun i hi => by
    unfold gfrac; rw [if_neg (Finset.ne_of_mem_erase hi)])]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    gS_comm]
  unfold gfrac; rw [if_pos rfl]
  exact g_algebra n hn G hG sl hsl _

lemma gavg (c : Profile n m) (q : ℕ) (hn : 0 < n) (G : Finset (Fin n))
    (hG : G.card = 2 ∨ G.card = 3) (i : Fin n) (hi : i ∈ G) (e : Fin m) :
    ∑ l ∈ G, gfrac c q G l i e = G.card / n := by
  rw [← Finset.add_sum_erase G _ hi]
  rw [Finset.sum_congr rfl (fun l hl => by
    unfold gfrac; rw [if_neg (Finset.ne_of_mem_erase hl).symm])]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  unfold gfrac; rw [if_pos rfl]
  exact g_algebra n hn G hG i hi _

def X2 [NeZero n] (c : Profile n m) (q : ℕ) (Q : Finset (Fin n)) (G : Fin n → Finset (Fin n))
    (t : Fin 6) : Fraction n m := fun i e =>
  if i ∈ Q then gfrac c q (G i) (sel (G i) t) i e else 1 / n

lemma X2_feasible [NeZero n] (c : Profile n m) (q : ℕ) (Q : Finset (Fin n))
    (G : Fin n → Finset (Fin n)) (hG : IsGrouping Q G) (t : Fin 6) : Feasible (X2 c q Q G t) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  constructor
  · intro i e; unfold X2; split_ifs
    · exact gfrac_nonneg _ _ _ _ _ _
    · positivity
  · intro e
    unfold X2
    rw [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [grouping_double_count Q G hG]
    have : ∀ i ∈ Q, (1 / ((G i).card : ℝ)) * ∑ j ∈ G i, gfrac c q (G j) (sel (G j) t) j e
        = 1 / n := by
      intro i hi
      obtain ⟨_, _, hcard, hsame⟩ := hG i hi
      rw [Finset.sum_congr rfl (fun j hj => by rw [hsame j hj])]
      rw [gsum c q hn (G i) hcard _ (sel_mem _ hcard t) e]
      have : (0:ℝ) < (G i).card := by rcases hcard with h | h <;> rw [h] <;> norm_num
      field_simp
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      ← add_mul]
    have hc := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun x => x ∈ Q)
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at hc
    rw [show ((Q.card : ℝ) + ((univ.filter (fun x => x ∉ Q)).card : ℝ)) = n by exact_mod_cast hc]
    field_simp

lemma X2_avg [NeZero n] (c : Profile n m) (q : ℕ) (Q : Finset (Fin n))
    (G : Fin n → Finset (Fin n)) (hG : IsGrouping Q G) (i : Fin n) (e : Fin m) :
    ∑ t : Fin 6, X2 c q Q G t i e = (Fintype.card (Fin 6) : ℝ) / n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  unfold X2
  by_cases hi : i ∈ Q
  · simp only [if_pos hi]
    obtain ⟨hii, _, hcard, _⟩ := hG i hi
    rw [sum_sel (G i) hcard (fun l => gfrac c q (G i) l i e), gavg c q hn (G i) hcard i hii e]
    have : (0:ℝ) < (G i).card := by rcases hcard with h | h <;> rw [h] <;> norm_num
    simp; field_simp
  · simp only [if_neg hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
    ring

end ChoresTIE197.Main.Sol

-- ===== part I =====


namespace ChoresTIE197.Main.Sol
open ChoresTIE197.Main

variable {m n : ℕ}

lemma poly_ineq (n q : ℝ) (hq : 1 ≤ q) (h1 : 4 * q ≤ n) (h2 : n ≤ 4 * q + 3) :
    (2 * n - 3 * q) * (q / 2 + n / 20 - 1 / 2) ≤ 94 / 100 * n * q := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ q) (by linarith : (0:ℝ) ≤ 4 * q + 3 - n),
    mul_nonneg (by linarith : (0:ℝ) ≤ n - 4 * q) (by linarith : (0:ℝ) ≤ 4 * q + 3 - n),
    mul_nonneg (by linarith : (0:ℝ) ≤ n - 4 * q) (by linarith : (0:ℝ) ≤ 4 * q + 13 - n)]

lemma ineq_ns (n q y L tot : ℝ) (hq : 1 ≤ q) (h1 : 4 * q ≤ n) (h2 : n ≤ 4 * q + 3)
    (hy : 0 ≤ y) (hL : 0 ≤ L) (htot : tot ≤ n * L) (hqy : q * y ≤ (q / 2 + n / 20 - 1 / 2) * L) :
    y + 3 / (2 * n) * (tot - q * y) ≤ 197 / 100 * L := by
  have hn : 0 < n := by linarith
  have hk : 0 ≤ 2 * n - 3 * q := by linarith
  -- y (2n - 3q) ≤ 0.94 n L
  have hA : q * (y * (2 * n - 3 * q)) ≤ q * (94 / 100 * n * L) := by
    calc q * (y * (2 * n - 3 * q)) = (q * y) * (2 * n - 3 * q) := by ring
      _ ≤ ((q / 2 + n / 20 - 1 / 2) * L) * (2 * n - 3 * q) := mul_le_mul_of_nonneg_right hqy hk
      _ = ((2 * n - 3 * q) * (q / 2 + n / 20 - 1 / 2)) * L := by ring
      _ ≤ (94 / 100 * n * q) * L := mul_le_mul_of_nonneg_right (poly_ineq n q hq h1 h2) hL
      _ = q * (94 / 100 * n * L) := by ring
  have hB : y * (2 * n - 3 * q) ≤ 94 / 100 * n * L := le_of_mul_le_mul_left hA (by linarith)
  rw [show y + 3 / (2 * n) * (tot - q * y) = (2 * n * y + 3 * (tot - q * y)) / (2 * n) by
    field_simp]
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma hard_q (ci : Fin m → ℝ≥0) (hn : 19 ≤ n) (hh : Hard ci n) :
    ((n / 4 : ℕ) : ℝ) * sc ci (n / 4) ≤ (((n / 4 : ℕ) : ℝ) / 2 + n / 20 - 1 / 2) * Lb ci n ∧
    ((n / 4 : ℕ) : ℝ) * sc ci (n / 4) ≤ cost ci (top ci (n / 4)) := by
  have hn0 : 0 < n := by omega
  obtain ⟨hL, hnm, hE, _, _⟩ := hard_facts ci hn0 hh
  set q := n / 4
  have hq : q < m := by omega
  have hqn : q ≤ n := by omega
  set y := sc ci q
  have hs1 := sc0_le_Lb ci n
  have hsn := scn_le_Lb ci n
  have hcardq : (top ci q).card = q := by rw [card_top]; omega
  have hcardq1 : (top ci (q+1)).card = q + 1 := by rw [card_top]; omega
  -- c(top (q+1)) ≥ s1 + q y
  have hc1 : sc ci 0 + q * y ≤ cost ci (top ci (q + 1)) := by
    have hpt : ∀ e ∈ top ci (q+1), y + (if rank ci e = 0 then (1:ℝ) else 0) * (sc ci 0 - y)
        ≤ ci e := by
      intro e he
      rw [mem_top] at he
      have hye : y ≤ ci e := sc_le_of_rank_le ci (by omega)
      split_ifs with h0
      · have := sc_rank ci e; rw [h0] at this; rw [this]; linarith
      · linarith
    have := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcardq1, ← Finset.sum_mul,
      sum_top_indicator_rank, if_pos ⟨by omega, by omega⟩] at this
    unfold cost; push_cast at this; linarith
  have hE1 : sc ci 0 + q * y - (q + 1) * sc ci n ≤ Eex ci n := by
    have : cost ci (top ci (q+1)) - (q + 1) * sc ci n ≤ Eex ci n := by
      unfold Eex
      calc cost ci (top ci (q+1)) - (q + 1) * sc ci n
          = ∑ e ∈ top ci (q+1), ((ci e : ℝ) - sc ci n) := by
            unfold cost; rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcardq1]
            push_cast; ring
        _ ≤ ∑ e ∈ top ci (q+1), max 0 ((ci e : ℝ) - sc ci n) :=
            Finset.sum_le_sum (fun e _ => le_max_right _ _)
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun e _ _ => le_max_left _ _)
    linarith
  have hnr : (19:ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · -- q y ≤ (q+1) sn + n s1 - 0.95 n L - s1
    have h1 : (q:ℝ) * y < (q + 1) * sc ci n + n * sc ci 0 - 95/100 * n * Lb ci n - sc ci 0 := by
      nlinarith
    have h2 : ((q:ℝ) + 1) * sc ci n ≤ ((q:ℝ) + 1) * (Lb ci n / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 : ((n:ℝ) - 1) * sc ci 0 ≤ ((n:ℝ) - 1) * Lb ci n :=
      mul_le_mul_of_nonneg_left hs1 (by linarith)
    nlinarith
  · calc (q : ℝ) * y = ∑ e ∈ top ci q, y := by rw [Finset.sum_const, nsmul_eq_mul, hcardq]
      _ ≤ cost ci (top ci q) := by
          unfold cost; apply Finset.sum_le_sum; intro e he
          rw [mem_top] at he
          exact sc_le_of_rank_le ci he.le

lemma cost_union_top (c : Profile n m) (q : ℕ) (i l : Fin n) :
    cost (c i) (top (c i) q ∪ top (c l) q) ≤ q * Lb (c i) n + Eex (c i) n := by
  have h1 := set_bound (c i) n (top (c i) q ∪ top (c l) q)
  have hcard : ((top (c i) q ∪ top (c l) q).card : ℝ) ≤ 2 * q := by
    have := Finset.card_union_le (top (c i) q) (top (c l) q)
    rw [card_top, card_top] at this
    have : (top (c i) q ∪ top (c l) q).card ≤ 2 * q := by omega
    exact_mod_cast this
  have hsn := scn_le_Lb (c i) n
  have hsn0 := sc_nonneg (c i) n
  nlinarith

lemma group_good [NeZero n] (c : Profile n m) (hn : 19 ≤ n) (G : Finset (Fin n))
    (hG : G.card = 2 ∨ G.card = 3) (i sl : Fin n) (hi : i ∈ G) (hh : Hard (c i) n)
    (B : Finset (Fin m)) (hB : SlotOK (c i) (gfrac c (n / 4) G sl i) B) :
    cost (c i) B ≤ 197/100 * Lb (c i) n := by
  have hn0 : 0 < n := by omega
  have hnr : (19:ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hL, hnm, hE, htot', hs1'⟩ := hard_facts (c i) hn0 hh
  set q := n / 4
  have hq4 : (4:ℝ) * q ≤ n := by
    have : 4 * q ≤ n := by omega
    exact_mod_cast this
  have hq4' : (n:ℝ) ≤ 4 * q + 3 := by
    have : n ≤ 4 * q + 3 := by omega
    exact_mod_cast this
  have hq1 : (1:ℝ) ≤ q := by
    have : 1 ≤ q := by omega
    exact_mod_cast this
  have hs1 := sc0_le_Lb (c i) n
  have htot := tot_le_Lb hn0 (c i)
  have hE5 : Eex (c i) n ≤ 5/100 * n * Lb (c i) n := by nlinarith
  have hnonneg : ∀ e, 0 ≤ gfrac c q G sl i e := fun e => gfrac_nonneg _ _ _ _ _ _
  by_cases hsel : i = sl
  · subst hsel
    have hsumS : ∑ e, gS c q G i e * c i e =
        ∑ l ∈ G.erase i, cost (c i) (top (c i) q ∪ top (c l) q) := by
      unfold gS
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro l _; exact sum_univ_ind_mul _ _
    have hSb : ∑ l ∈ G.erase i, cost (c i) (top (c i) q ∪ top (c l) q) ≤
        ((G.card : ℝ) - 1) * (q * Lb (c i) n + Eex (c i) n) := by
      calc _ ≤ ∑ l ∈ G.erase i, (q * Lb (c i) n + Eex (c i) n) :=
            Finset.sum_le_sum (fun l _ => cost_union_top c q i l)
        _ = _ := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hi]
            have : 1 ≤ G.card := by omega
            push_cast [this]; ring
    have hfrac : ∑ e, gfrac c q G i i e * c i e ≤ 95/100 * Lb (c i) n := by
      have hg : ∀ e, gfrac c q G i i e = (if G.card = 2 then 1 / (2 * (n:ℝ)) * (1 + 3 * gS c q G i e)
          else 3 / (2 * n) * gS c q G i e) := fun e => by unfold gfrac; rw [if_pos rfl]
      simp_rw [hg]
      rcases hG with h2 | h3
      · simp only [if_pos h2]
        rw [h2] at hSb
        have : ∑ e, 1 / (2 * (n:ℝ)) * (1 + 3 * gS c q G i e) * c i e =
            1 / (2 * n) * cost (c i) univ + 3 / (2 * n) * ∑ e, gS c q G i e * c i e := by
          unfold cost
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro e _; ring
        rw [this, hsumS]
        have hnpos : (0:ℝ) < n := by linarith
        rw [show 1 / (2 * (n:ℝ)) * cost (c i) univ + 3 / (2 * n) *
            ∑ l ∈ G.erase i, cost (c i) (top (c i) q ∪ top (c l) q) =
            (cost (c i) univ + 3 * ∑ l ∈ G.erase i, cost (c i) (top (c i) q ∪ top (c l) q)) / (2 * n)
            by field_simp]
        rw [div_le_iff₀ (by positivity)]
        norm_num at hSb
        nlinarith
      · simp only [if_neg (show ¬ G.card = 2 by omega)]
        rw [h3] at hSb
        have : ∑ e, 3 / (2 * (n:ℝ)) * gS c q G i e * c i e =
            3 / (2 * n) * ∑ e, gS c q G i e * c i e := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro e _; ring
        rw [this, hsumS]
        have hnpos : (0:ℝ) < n := by linarith
        rw [show 3 / (2 * (n:ℝ)) *
            ∑ l ∈ G.erase i, cost (c i) (top (c i) q ∪ top (c l) q) =
            (3 * ∑ l ∈ G.erase i, cost (c i) (top (c i) q ∪ top (c l) q)) / (2 * n)
            by field_simp]
        rw [div_le_iff₀ (by positivity)]
        norm_num at hSb
        nlinarith
    have := bound_general (c i) _ hnonneg B hB (sc (c i) 0) (sc_nonneg _ _)
      (fun e _ => le_sc_zero _ e)
    linarith
  · -- non-selected member
    have hxle : ∀ e, gfrac c q G sl i e ≤ 3 / (2 * n) * (1 - ind (top (c i) q) e) := by
      intro e
      unfold gfrac; rw [if_neg hsel]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      unfold ind
      split_ifs with h1 h2 <;> simp_all
    have hK : ∀ e, 0 < gfrac c q G sl i e → (c i e : ℝ) ≤ sc (c i) q := by
      intro e he
      have := hxle e
      have hnot : e ∉ top (c i) q := by
        intro hin
        have h1 : ind (top (c i) q) e = 1 := by simp [ind, hin]
        have h2 := hxle e
        rw [h1, sub_self, mul_zero] at h2
        linarith
      rw [mem_top, not_lt] at hnot
      exact le_sc_of_le_rank _ hnot
    have hbg := bound_general (c i) _ hnonneg B hB (sc (c i) q) (sc_nonneg _ _) hK
    have hfr : ∑ e, gfrac c q G sl i e * c i e ≤
        3 / (2 * n) * (cost (c i) univ - cost (c i) (top (c i) q)) := by
      calc ∑ e, gfrac c q G sl i e * c i e ≤ ∑ e, 3 / (2 * n) * (1 - ind (top (c i) q) e) * c i e :=
            Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_right (hxle e) (by positivity))
        _ = _ := by
            have hh' : ∀ e, 3 / (2 * (n:ℝ)) * (1 - ind (top (c i) q) e) * c i e =
                3 / (2 * n) * c i e - 3 / (2 * n) * (ind (top (c i) q) e * c i e) := by
              intro e; ring
            rw [Finset.sum_congr rfl (fun e _ => hh' e), Finset.sum_sub_distrib, ← Finset.mul_sum,
              ← Finset.mul_sum, sum_univ_ind_mul]
            unfold cost; ring
    obtain ⟨hqy, hcq⟩ := hard_q (c i) hn hh
    have hy0 := sc_nonneg (c i) q
    have hnpos : (0:ℝ) < n := by linarith
    have : 3 / (2 * (n:ℝ)) * (cost (c i) univ - cost (c i) (top (c i) q)) ≤
        3 / (2 * n) * (cost (c i) univ - q * sc (c i) q) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have := ineq_ns n q (sc (c i) q) (Lb (c i) n) (cost (c i) univ) hq1 hq4 hq4' hy0 hL.le htot hqy
    linarith

theorem groups_case [NeZero n] (c : Profile n m) (hn : 19 ≤ n)
    (hQ : 2 ≤ (univ.filter (fun i => Hard (c i) n)).card) :
    ∃ p : Law n m, (∀ i e, marginal p i e = 1 / (n : ℝ)) ∧
      ∀ A, p A ≠ 0 → ∀ i, cost (c i) (bundle A i) ≤ 197/100 * Lb (c i) n := by
  have hn0 : 0 < n := by omega
  set Q := univ.filter (fun i => Hard (c i) n)
  obtain ⟨G, hG⟩ := exists_grouping _ Q rfl hQ
  obtain ⟨p, hp1, hp2⟩ := mix c (ι := Fin 6) (X2 c (n / 4) Q G) (X2_feasible c _ Q G hG)
    (X2_avg c _ Q G hG) (fun A => ∀ i, cost (c i) (bundle A i) ≤ 197/100 * Lb (c i) n) (by
      intro t A hA i
      have hB := hA i
      by_cases hi : i ∈ Q
      · have hh : Hard (c i) n := (Finset.mem_filter.mp hi).2
        obtain ⟨hii, _, hcard, _⟩ := hG i hi
        have : X2 c (n / 4) Q G t i = gfrac c (n / 4) (G i) (sel (G i) t) i := by
          funext e; simp [X2, hi]
        rw [this] at hB
        exact group_good c hn (G i) hcard i _ hii hh _ hB
      · have hnh : ¬ Hard (c i) n := fun h => hi (Finset.mem_filter.mpr ⟨mem_univ _, h⟩)
        have : X2 c (n / 4) Q G t i = fun _ => 1 / (n : ℝ) := by
          funext e; simp [X2, hi]
        rw [this] at hB
        have h1 := easy_uniform (c i) hn0 _ hB
        unfold Hard at hnh; push Not at hnh
        have := Lb_nonneg (c i) n
        linarith)
  exact ⟨p, hp1, hp2⟩

theorem large_case [NeZero n] (c : Profile n m) (hn : 19 ≤ n) :
    ∃ p : Law n m, (∀ i e, marginal p i e = 1 / (n : ℝ)) ∧
      ∀ A, p A ≠ 0 → ∀ i, cost (c i) (bundle A i) ≤ 197/100 * Lb (c i) n := by
  have hn0 : 0 < n := by omega
  set Q := univ.filter (fun i => Hard (c i) n) with hQdef
  rcases Nat.lt_or_ge Q.card 2 with hlt | hge
  · rcases Nat.lt_or_ge Q.card 1 with h0 | h1
    · -- no hard agents
      have hQ0 : Q = ∅ := Finset.card_eq_zero.mp (by omega)
      have heasy : ∀ i, ¬ Hard (c i) n := by
        intro i h
        have : i ∈ Q := Finset.mem_filter.mpr ⟨mem_univ _, h⟩
        rw [hQ0] at this; simp at this
      obtain ⟨p, hp1, hp2⟩ := mix c (ι := Unit) (fun _ _ _ => 1 / (n : ℝ))
        (fun _ => ⟨fun _ _ => by positivity, fun e => by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp⟩)
        (fun i e => by simp)
        (fun A => ∀ i, cost (c i) (bundle A i) ≤ 197/100 * Lb (c i) n) (by
          intro s A hA i
          have h1 := easy_uniform (c i) hn0 _ (hA i)
          have hnh := heasy i
          unfold Hard at hnh; push Not at hnh
          have := Lb_nonneg (c i) n
          linarith)
      exact ⟨p, hp1, hp2⟩
    · -- exactly one hard agent
      obtain ⟨h, hQh⟩ := Finset.card_eq_one.mp (show Q.card = 1 by omega)
      have hh : Hard (c h) n := by
        have : h ∈ Q := by rw [hQh]; simp
        exact (Finset.mem_filter.mp this).2
      apply one_hard_case c h hn hh
      intro j hj hjh
      have : j ∈ Q := Finset.mem_filter.mpr ⟨mem_univ _, hjh⟩
      rw [hQh] at this; simp at this; exact hj this
  · exact groups_case c hn hge

end ChoresTIE197.Main.Sol

open ChoresTIE197.Main ChoresTIE197.Main.Sol in
theorem solution (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    ∃ F : Mechanism n m,
      TIEOn (fun _ => True) F ∧ EFOn (fun _ => True) F ∧
      MMSOn (fun _ => True) (197/100:ℝ) F := by
  haveI : NeZero n := ⟨by omega⟩
  apply main_of_laws (by omega)
  intro c
  by_cases hsmall : n ≤ 33
  · exact small_case hsmall c
  · obtain ⟨p, hp1, hp2⟩ := large_case c (by omega)
    refine ⟨p, hp1, fun A hA i => ?_⟩
    have := hp2 A hA i
    have := Lb_le_mms (by omega : 0 < n) (c i)
    linarith
