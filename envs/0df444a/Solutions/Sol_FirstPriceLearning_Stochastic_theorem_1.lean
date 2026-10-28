-- Prove2me | solution 1 for FirstPriceLearning.Stochastic.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T11:37:46.074101+00:00
-- url     : https://prove2.me/submissions/85cee12b-a7bc-42a0-9a5d-37b13ed23853

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Policy

-- ===== part Alg =====

open MeasureTheory
open scoped Classical

namespace FPA1

/-! ## The epoch-based elimination algorithm (deterministic part) -/

/-- epoch index of round `t` (rounds `2^e - 1 ≤ t < 2^(e+1) - 1` form epoch `e`). -/
noncomputable def ep (t : ℕ) : ℕ := Nat.log 2 (t + 1)

/-- the rounds of epoch `e`. -/
def epoch (e : ℕ) : Finset ℕ := Finset.Ico (2 ^ e - 1) (2 ^ (e + 1) - 1)

lemma ep_of_mem {e s : ℕ} (h : s ∈ epoch e) : ep s = e := by
  simp only [epoch, Finset.mem_Ico] at h
  unfold ep
  rw [Nat.log_eq_iff (by right; exact ⟨by norm_num, by omega⟩)]
  have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (e + 1) := Nat.one_le_two_pow
  constructor <;> omega

lemma epoch_lt {e s : ℕ} (h : s ∈ epoch e) : s < 2 ^ (e + 1) - 1 := by
  simp only [epoch, Finset.mem_Ico] at h; exact h.2

lemma epoch_ge {e s : ℕ} (h : s ∈ epoch e) : 2 ^ e - 1 ≤ s := by
  simp only [epoch, Finset.mem_Ico] at h; exact h.1

lemma card_epoch (e : ℕ) : (epoch e).card = 2 ^ e := by
  simp only [epoch, Nat.card_Ico]
  have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  rw [pow_succ]; omega

/-- the bid grid: `gb K j = (min j (K-1) + 1)/K`. -/
noncomputable def gb (K j : ℕ) : ℝ := (((min j (K - 1) : ℕ) : ℝ) + 1) / K

/-- the value grid point `i / M`. -/
noncomputable def gv (M i : ℕ) : ℝ := (i : ℝ) / M

/-- value quantization. -/
noncomputable def qv (M : ℕ) (v : ℝ) : ℕ := min ⌊v * M⌋₊ (M - 1)

/-- confidence width. -/
noncomputable def wd (c : ℝ) (n : ℕ) : ℝ := if n = 0 then 1 else min 1 (Real.sqrt (c / n))

/-- running maximum of a threshold function. -/
def tbar (θ : ℕ → ℕ) (i : ℕ) : ℕ := (Finset.range (i + 1)).sup θ

/-- samples of epoch `e` usable at bid index `j`. -/
def samp (e : ℕ) (tb : ℕ → ℕ) (vq : ℕ → ℕ) (j : ℕ) : Finset ℕ :=
  (epoch e).filter (fun s => tb (vq s) ≤ j)

/-- empirical frequency of `y s ≤ gb K j` over the sample set `S`. -/
noncomputable def ghat (K : ℕ) (S : Finset ℕ) (y : ℕ → ℝ) (j : ℕ) : ℝ :=
  ((S.filter (fun s => y s ≤ gb K j)).card : ℝ) / S.card

noncomputable def ucb (K M : ℕ) (c : ℝ) (e : ℕ) (tb vq : ℕ → ℕ) (y : ℕ → ℝ) (i j : ℕ) : ℝ :=
  (gv M i - gb K j) * ghat K (samp e tb vq j) y j + wd c (samp e tb vq j).card

noncomputable def lcb (K M : ℕ) (c : ℝ) (e : ℕ) (tb vq : ℕ → ℕ) (y : ℕ → ℝ) (i j : ℕ) : ℝ :=
  (gv M i - gb K j) * ghat K (samp e tb vq j) y j - wd c (samp e tb vq j).card

/-- `j` is a plausible bid index for value index `i`. -/
def pred (K M : ℕ) (c : ℝ) (e : ℕ) (tb vq : ℕ → ℕ) (y : ℕ → ℝ) (i j : ℕ) : Prop :=
  tb i ≤ j ∧ ∀ j' < K, tb i ≤ j' → lcb K M c e tb vq y i j' ≤ ucb K M c e tb vq y i j

/-- the next threshold: least plausible bid index. -/
noncomputable def nextθ (K M : ℕ) (c : ℝ) (e : ℕ) (θ : ℕ → ℕ) (vq : ℕ → ℕ) (y : ℕ → ℝ)
    (i : ℕ) : ℕ :=
  min (K - 1) ((Finset.range K).filter
    (fun j => ∀ j'' ≤ j, ¬ pred K M c e (tbar θ) vq y i j'')).card

/-- the thresholds of all epochs. -/
noncomputable def theta (K M : ℕ) (c : ℝ) (vq : ℕ → ℕ) (y : ℕ → ℝ) : ℕ → ℕ → ℕ
  | 0 => fun _ => 0
  | e + 1 => nextθ K M c e (theta K M c vq y e) vq y

/-- the bid of round `t`. -/
noncomputable def algBid (K M : ℕ) (c : ℝ) (vq : ℕ → ℕ) (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  gb K (theta K M c vq y (ep t) (vq t))

/-! ### basic facts -/

lemma gb_pos {K : ℕ} (hK : 1 ≤ K) (j : ℕ) : 0 < gb K j := by
  unfold gb; positivity

lemma gb_le_one {K : ℕ} (hK : 1 ≤ K) (j : ℕ) : gb K j ≤ 1 := by
  unfold gb
  rw [div_le_one (by exact_mod_cast hK)]
  have : min j (K - 1) + 1 ≤ K := by have := min_le_right j (K - 1); omega
  exact_mod_cast this

lemma gb_mono (K : ℕ) : Monotone (gb K) := by
  intro a b hab
  unfold gb
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have : min a (K - 1) ≤ min b (K - 1) := min_le_min_right _ hab
  have : ((min a (K - 1) : ℕ) : ℝ) ≤ ((min b (K - 1) : ℕ) : ℝ) := by exact_mod_cast this
  linarith

lemma gv_mono (M : ℕ) : Monotone (gv M) := by
  intro a b hab
  unfold gv
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hab

lemma gv_nonneg (M i : ℕ) : 0 ≤ gv M i := by unfold gv; positivity

lemma gv_lt_one {M i : ℕ} (hi : i < M) : gv M i < 1 := by
  unfold gv
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  rw [div_lt_one hM]; exact_mod_cast hi

lemma qv_lt {M : ℕ} (hM : 1 ≤ M) (v : ℝ) : qv M v < M := by
  unfold qv; have := min_le_right ⌊v * M⌋₊ (M - 1); omega

lemma qv_mono (M : ℕ) : Monotone (qv M) := by
  intro a b hab
  unfold qv
  apply min_le_min_right
  apply Nat.floor_le_floor
  exact mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg _)

lemma gv_qv_le {M : ℕ} (hM : 1 ≤ M) {v : ℝ} (hv : 0 ≤ v) : gv M (qv M v) ≤ v := by
  unfold gv qv
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  rw [div_le_iff₀ hMr]
  have h1 : ((min ⌊v * M⌋₊ (M - 1) : ℕ) : ℝ) ≤ (⌊v * M⌋₊ : ℝ) := by
    exact_mod_cast min_le_left _ _
  have h2 : (⌊v * M⌋₊ : ℝ) ≤ v * M := Nat.floor_le (by positivity)
  linarith

lemma v_le_gv_qv {M : ℕ} (hM : 1 ≤ M) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    v ≤ gv M (qv M v) + 1 / M := by
  unfold gv qv
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  rw [← add_div, le_div_iff₀ hMr]
  rcases le_total ⌊v * M⌋₊ (M - 1) with h | h
  · rw [min_eq_left h]
    have := Nat.lt_floor_add_one (v * M)
    linarith
  · rw [min_eq_right h]
    have : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by rw [Nat.cast_sub hM]; simp
    rw [this]
    nlinarith

lemma wd_le_one (c : ℝ) (n : ℕ) : wd c n ≤ 1 := by
  unfold wd; split_ifs
  · exact le_refl _
  · exact min_le_left _ _

lemma wd_nonneg (c : ℝ) (n : ℕ) : 0 ≤ wd c n := by
  unfold wd; split_ifs
  · norm_num
  · exact le_min (by norm_num) (Real.sqrt_nonneg _)

lemma wd_anti {c : ℝ} (hc : 0 ≤ c) {n n' : ℕ} (h : n ≤ n') : wd c n' ≤ wd c n := by
  unfold wd
  by_cases hn : n = 0
  · simp only [hn, if_true]
    split_ifs
    · exact le_refl _
    · exact min_le_left _ _
  · have hn' : n' ≠ 0 := by omega
    simp only [hn, hn', if_false]
    apply min_le_min_left
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_left hc
    · exact_mod_cast (Nat.pos_of_ne_zero hn)
    · exact_mod_cast h

lemma tbar_mono (θ : ℕ → ℕ) : Monotone (tbar θ) := by
  intro a b hab
  unfold tbar
  apply Finset.sup_mono
  intro x; simp only [Finset.mem_range]; omega

lemma le_tbar (θ : ℕ → ℕ) (i : ℕ) : θ i ≤ tbar θ i := by
  unfold tbar
  exact Finset.le_sup (f := θ) (Finset.mem_range.mpr (by omega))

lemma tbar_le_iff (θ : ℕ → ℕ) (i j : ℕ) : tbar θ i ≤ j ↔ ∀ i' ≤ i, θ i' ≤ j := by
  unfold tbar
  rw [Finset.sup_le_iff]
  simp only [Finset.mem_range]
  constructor
  · intro h i' hi'; exact h i' (by omega)
  · intro h i' hi'; exact h i' (by omega)

/-! ### the least plausible index -/

lemma nextθ_spec (K M : ℕ) (c : ℝ) (e : ℕ) (θ : ℕ → ℕ) (vq : ℕ → ℕ) (y : ℕ → ℝ) (i J : ℕ)
    (hJ : J < K) (hP : pred K M c e (tbar θ) vq y i J) :
    nextθ K M c e θ vq y i ≤ J ∧ pred K M c e (tbar θ) vq y i (nextθ K M c e θ vq y i) := by
  have hex : ∃ j, pred K M c e (tbar θ) vq y i j := ⟨J, hP⟩
  set n0 := Nat.find hex with hn0
  have hn0J : n0 ≤ J := Nat.find_min' hex hP
  have hfilt : (Finset.range K).filter
      (fun j => ∀ j'' ≤ j, ¬ pred K M c e (tbar θ) vq y i j'') = Finset.range n0 := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, h⟩
      by_contra hc
      push_neg at hc
      exact h n0 hc (Nat.find_spec hex)
    · intro hj
      refine ⟨by omega, fun j'' hj'' => ?_⟩
      exact Nat.find_min hex (by omega)
  have hval : nextθ K M c e θ vq y i = n0 := by
    unfold nextθ
    rw [hfilt, Finset.card_range]
    omega
  rw [hval]
  exact ⟨hn0J, Nat.find_spec hex⟩

/-! ### the largest grid maximiser -/

/-- largest maximiser of `R` over `{0, …, K-1}`. -/
noncomputable def Jmax (K : ℕ) (R : ℕ → ℝ) : ℕ :=
  ((Finset.range K).filter (fun j => ∀ j' < K, R j' ≤ R j)).sup id

lemma Jmax_spec {K : ℕ} (hK : 1 ≤ K) (R : ℕ → ℝ) :
    Jmax K R < K ∧ ∀ j' < K, R j' ≤ R (Jmax K R) := by
  set S := (Finset.range K).filter (fun j => ∀ j' < K, R j' ≤ R j) with hS
  have hne : S.Nonempty := by
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range K) R
      ⟨0, Finset.mem_range.mpr (by omega)⟩
    refine ⟨j, Finset.mem_filter.mpr ⟨hj, fun j' hj' => hmax j' (Finset.mem_range.mpr hj')⟩⟩
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup S hne id
  have : Jmax K R = j := hjeq
  rw [this]
  rw [hS, Finset.mem_filter, Finset.mem_range] at hj
  exact hj

lemma le_Jmax {K : ℕ} (R : ℕ → ℝ) {j : ℕ} (hj : j < K) (hmax : ∀ j' < K, R j' ≤ R j) :
    j ≤ Jmax K R := by
  unfold Jmax
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hmax⟩)

/-- the quantized expected reward. -/
noncomputable def Rq (K M : ℕ) (g : ℝ → ℝ) (i j : ℕ) : ℝ := (gv M i - gb K j) * g (gb K j)

noncomputable def Jst (K M : ℕ) (g : ℝ → ℝ) (i : ℕ) : ℕ := Jmax K (Rq K M g i)

lemma Jst_mono {K M : ℕ} (hK : 1 ≤ K) {g : ℝ → ℝ} (hg : Monotone g) :
    Monotone (Jst K M g) := by
  intro i i' hii'
  obtain ⟨hJ1, hJ2⟩ := Jmax_spec hK (Rq K M g i)
  obtain ⟨hJ1', hJ2'⟩ := Jmax_spec hK (Rq K M g i')
  unfold Jst
  set j := Jmax K (Rq K M g i)
  set j' := Jmax K (Rq K M g i')
  by_contra hcon
  push_neg at hcon
  have hgv : gv M i ≤ gv M i' := gv_mono M hii'
  have hgg : g (gb K j') ≤ g (gb K j) := hg (gb_mono K hcon.le)
  have hmaxj : ∀ k < K, Rq K M g i' k ≤ Rq K M g i' j := by
    intro k hk
    have h1 := hJ2' k hk
    have h2 := hJ2 j' hJ1'
    unfold Rq at *
    nlinarith
  have := le_Jmax (Rq K M g i') hJ1 hmaxj
  omega

/-! ### the good event and the invariant -/

/-- the down-set of epoch `e` below the value index of round `r`. -/
def dset (e : ℕ) (vq : ℕ → ℕ) (r : ℕ) : Finset ℕ := (epoch e).filter (fun s => vq s ≤ vq r)

def GoodE (K : ℕ) (c : ℝ) (g : ℝ → ℝ) (vq : ℕ → ℕ) (m : ℕ → ℝ) (e : ℕ) : Prop :=
  ∀ r ∈ epoch e, ∀ j < K, |ghat K (dset e vq r) m j - g (gb K j)| ≤ wd c (dset e vq r).card

lemma samp_eq_dset (e : ℕ) {tb : ℕ → ℕ} (htb : Monotone tb) (vq : ℕ → ℕ) (j : ℕ)
    (hne : (samp e tb vq j).Nonempty) : ∃ r ∈ epoch e, samp e tb vq j = dset e vq r := by
  obtain ⟨r, hr, hmax⟩ := Finset.exists_max_image (samp e tb vq j) vq hne
  have hr' := hr
  simp only [samp, Finset.mem_filter] at hr'
  refine ⟨r, hr'.1, ?_⟩
  ext s
  simp only [samp, dset, Finset.mem_filter]
  constructor
  · rintro ⟨hs, hsj⟩
    exact ⟨hs, hmax s (by simp only [samp, Finset.mem_filter]; exact ⟨hs, hsj⟩)⟩
  · rintro ⟨hs, hsr⟩
    exact ⟨hs, (htb hsr).trans hr'.2⟩

lemma est_samp {K : ℕ} {c : ℝ} {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    {vq : ℕ → ℕ} {m : ℕ → ℝ} {e : ℕ} (hG : GoodE K c g vq m e) {tb : ℕ → ℕ} (htb : Monotone tb)
    {j : ℕ} (hj : j < K) :
    |ghat K (samp e tb vq j) m j - g (gb K j)| ≤ wd c (samp e tb vq j).card := by
  rcases (samp e tb vq j).eq_empty_or_nonempty with h | h
  · rw [h]
    simp only [ghat, Finset.filter_empty, Finset.card_empty, Nat.cast_zero, div_zero, zero_sub,
      abs_neg]
    unfold wd; simp only [if_true]
    rw [abs_of_nonneg (hg0 _)]; exact hg1 _
  · obtain ⟨r, hr, hEq⟩ := samp_eq_dset e htb vq j h
    rw [hEq]; exact hG r hr j hj

lemma abs_gv_gb_le {K M : ℕ} (hK : 1 ≤ K) {i : ℕ} (hi : i < M) (j : ℕ) :
    |gv M i - gb K j| ≤ 1 := by
  have h1 := gv_nonneg M i
  have h2 := gv_lt_one hi
  have h3 := gb_pos hK j
  have h4 := gb_le_one hK j
  rw [abs_le]; constructor <;> linarith

lemma ucb_bounds {K M : ℕ} {c : ℝ} {g : ℝ → ℝ} (hK : 1 ≤ K) {e : ℕ} {tb vq : ℕ → ℕ}
    {m : ℕ → ℝ} {i j : ℕ} (hi : i < M)
    (hest : |ghat K (samp e tb vq j) m j - g (gb K j)| ≤ wd c (samp e tb vq j).card) :
    Rq K M g i j ≤ ucb K M c e tb vq m i j ∧
      ucb K M c e tb vq m i j ≤ Rq K M g i j + 2 * wd c (samp e tb vq j).card ∧
      lcb K M c e tb vq m i j ≤ Rq K M g i j ∧
      Rq K M g i j - 2 * wd c (samp e tb vq j).card ≤ lcb K M c e tb vq m i j := by
  have hab := abs_gv_gb_le hK hi j
  set w := wd c (samp e tb vq j).card
  set G := ghat K (samp e tb vq j) m j
  have key : |(gv M i - gb K j) * G - (gv M i - gb K j) * g (gb K j)| ≤ w := by
    rw [← mul_sub, abs_mul]
    calc |gv M i - gb K j| * |G - g (gb K j)| ≤ 1 * w := by
          apply mul_le_mul hab hest (abs_nonneg _) (by norm_num)
      _ = w := one_mul w
  rw [abs_le] at key
  unfold ucb lcb Rq
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [key.1, key.2]

/-- the invariant: thresholds stay below the largest maximiser. -/
theorem theta_le_Jst {K M : ℕ} {c : ℝ} {g : ℝ → ℝ} (hK : 1 ≤ K) (hg : Monotone g)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) {vq : ℕ → ℕ} {m : ℕ → ℝ} :
    ∀ e, (∀ e' < e, GoodE K c g vq m e') → ∀ i < M, theta K M c vq m e i ≤ Jst K M g i := by
  intro e
  induction e with
  | zero => intro _ i _; simp [theta]
  | succ e ih =>
    intro hG i hi
    have hGe : GoodE K c g vq m e := hG e (by omega)
    have ih' := ih (fun e' he' => hG e' (by omega))
    set θ := theta K M c vq m e with hθ
    have htb : tbar θ i ≤ Jst K M g i := by
      rw [tbar_le_iff]
      intro i' hi'
      exact (ih' i' (by omega)).trans (Jst_mono hK hg hi')
    obtain ⟨hJK, hJmax⟩ := Jmax_spec hK (Rq K M g i)
    have hP : pred K M c e (tbar θ) vq m i (Jst K M g i) := by
      refine ⟨htb, fun j' hj' _ => ?_⟩
      have b1 := ucb_bounds (M := M) hK hi
        (est_samp hg0 hg1 hGe (tbar_mono θ) (j := Jst K M g i) hJK)
      have b2 := ucb_bounds (M := M) hK hi
        (est_samp hg0 hg1 hGe (tbar_mono θ) (j := j') hj')
      have := hJmax j' hj'
      unfold Jst at *
      linarith [b1.1, b2.2.2.1]
    show nextθ K M c e θ vq m i ≤ Jst K M g i
    exact (nextθ_spec K M c e θ vq m i _ hJK hP).1

/-- the per-round regret bound in the quantized problem. -/
theorem step_regret {K M : ℕ} {c : ℝ} {g : ℝ → ℝ} (hK : 1 ≤ K) (hc : 0 ≤ c) (hg : Monotone g)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) {vq : ℕ → ℕ} {m : ℕ → ℝ} {e : ℕ}
    (hGe : GoodE K c g vq m e) (hinv : ∀ i < M, theta K M c vq m e i ≤ Jst K M g i)
    {i : ℕ} (hi : i < M) :
    Rq K M g i (Jst K M g i) - Rq K M g i (theta K M c vq m (e + 1) i) ≤
      4 * wd c ((epoch e).filter (fun s => vq s ≤ i)).card := by
  set θ := theta K M c vq m e with hθ
  have htb : tbar θ i ≤ Jst K M g i := by
    rw [tbar_le_iff]
    intro i' hi'
    exact (hinv i' (by omega)).trans (Jst_mono hK hg hi')
  obtain ⟨hJK, hJmax⟩ := Jmax_spec hK (Rq K M g i)
  have hP : pred K M c e (tbar θ) vq m i (Jst K M g i) := by
    refine ⟨htb, fun j' hj' _ => ?_⟩
    have b1 := ucb_bounds (M := M) hK hi
      (est_samp hg0 hg1 hGe (tbar_mono θ) (j := Jst K M g i) hJK)
    have b2 := ucb_bounds (M := M) hK hi
      (est_samp hg0 hg1 hGe (tbar_mono θ) (j := j') hj')
    have := hJmax j' hj'
    unfold Jst at *
    linarith [b1.1, b2.2.2.1]
  obtain ⟨hbJ, hPb⟩ := nextθ_spec K M c e θ vq m i _ hJK hP
  set b := nextθ K M c e θ vq m i with hb
  have hbK : b < K := lt_of_le_of_lt hbJ hJK
  have hθb : theta K M c vq m (e + 1) i = b := rfl
  rw [hθb]
  -- sample sizes
  set N := ((epoch e).filter (fun s => vq s ≤ i)).card
  have hsub : ∀ j, tbar θ i ≤ j → N ≤ (samp e (tbar θ) vq j).card := by
    intro j hj
    apply Finset.card_le_card
    intro s hs
    simp only [Finset.mem_filter] at hs
    simp only [samp, Finset.mem_filter]
    exact ⟨hs.1, (tbar_mono θ hs.2).trans hj⟩
  have wJ := wd_anti hc (hsub _ htb)
  have wb := wd_anti hc (hsub _ hPb.1)
  have b1 := ucb_bounds (M := M) hK hi
    (est_samp hg0 hg1 hGe (tbar_mono θ) (j := Jst K M g i) hJK)
  have b2 := ucb_bounds (M := M) hK hi (est_samp hg0 hg1 hGe (tbar_mono θ) (j := b) hbK)
  have hcmp := hPb.2 (Jst K M g i) hJK htb
  linarith [b1.2.2.2, b2.2.1]

end FPA1

-- ===== part Pol =====

open MeasureTheory
open scoped Classical
open FirstPriceLearning.Stochastic

namespace FPA1

/-! ## congruence / locality of the thresholds -/

lemma nextθ_congr {K M : ℕ} {c : ℝ} {e : ℕ} {θ : ℕ → ℕ} {vq vq' : ℕ → ℕ} {y y' : ℕ → ℝ}
    (hv : ∀ s ∈ epoch e, vq s = vq' s)
    (hy : ∀ j, ∀ s ∈ samp e (tbar θ) vq j, (y s ≤ gb K j ↔ y' s ≤ gb K j)) :
    nextθ K M c e θ vq y = nextθ K M c e θ vq' y' := by
  have hs : ∀ j, samp e (tbar θ) vq j = samp e (tbar θ) vq' j := by
    intro j
    unfold samp
    apply Finset.filter_congr
    intro s hs; rw [hv s hs]
  have hg : ∀ j, ghat K (samp e (tbar θ) vq' j) y j = ghat K (samp e (tbar θ) vq' j) y' j := by
    intro j
    unfold ghat
    congr 3
    apply Finset.filter_congr
    intro s hs'
    rw [← hs j] at hs'
    exact hy j s hs'
  funext i
  unfold nextθ
  apply congrArg (min (K - 1))
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j _
  simp only [pred, ucb, lcb, hs, hg]

lemma theta_local (K M : ℕ) (c : ℝ) {vq vq' : ℕ → ℕ} {y y' : ℕ → ℝ} :
    ∀ e, (∀ s < 2 ^ e - 1, vq s = vq' s ∧ y s = y' s) →
      theta K M c vq y e = theta K M c vq' y' e := by
  intro e
  induction e with
  | zero => intro _; rfl
  | succ e ih =>
    intro h
    have hle : 2 ^ e - 1 ≤ 2 ^ (e + 1) - 1 := by
      have : 2 ^ e ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have ih' := ih (fun s hs => h s (by omega))
    show nextθ K M c e (theta K M c vq y e) vq y = nextθ K M c e (theta K M c vq' y' e) vq' y'
    rw [ih']
    apply nextθ_congr
    · intro s hs; exact (h s (epoch_lt hs)).1
    · intro j s hs
      have hs' : s ∈ epoch e := (Finset.mem_filter.mp hs).1
      rw [(h s (epoch_lt hs')).2]

/-- feedback-consistent observation sequences give the same thresholds as the raw HOBs. -/
lemma theta_obs_eq (K M : ℕ) (c : ℝ) (vq : ℕ → ℕ) {Y m : ℕ → ℝ} :
    ∀ e, (∀ s < 2 ^ e - 1, Y s = max (algBid K M c vq Y s) (m s)) →
      theta K M c vq Y e = theta K M c vq m e := by
  intro e
  induction e with
  | zero => intro _; rfl
  | succ e ih =>
    intro h
    have hle : 2 ^ e - 1 ≤ 2 ^ (e + 1) - 1 := by
      have : 2 ^ e ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have ih' := ih (fun s hs => h s (by omega))
    show nextθ K M c e (theta K M c vq Y e) vq Y = nextθ K M c e (theta K M c vq m e) vq m
    rw [ih']
    apply nextθ_congr (fun _ _ => rfl)
    intro j s hs
    obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
    have hYs := h s (epoch_lt hs1)
    unfold algBid at hYs
    rw [ep_of_mem hs1, ih'] at hYs
    have hb : gb K (theta K M c vq m e (vq s)) ≤ gb K j :=
      gb_mono K ((le_tbar _ _).trans hs2)
    rw [hYs, max_le_iff]
    constructor
    · intro h'; exact h'.2
    · intro h'; exact ⟨hb, h'⟩

/-! ## the policy -/

/-- extension of a finite sequence by zeros. -/
noncomputable def extV {t : ℕ} (vs : Fin t → ℝ) : ℕ → ℝ :=
  fun s => if h : s < t then vs ⟨s, h⟩ else 0

/-- parameters -/
noncomputable def cT (T : ℕ) : ℝ := 2 * Real.log T

noncomputable def pol (T : ℕ) : Policy T where
  U := Unit
  μU := Measure.dirac ()
  bid t _ vs ys := algBid T T (cT T) (fun s => qv T (extV vs s)) (extV ys) t
  bid_mem t _ vs ys := by
    have hT : 1 ≤ T := by have := t.isLt; omega
    exact ⟨(gb_pos hT _).le, gb_le_one hT _⟩

lemma feedback_apply {T : ℕ} (π : Policy T) (u : π.U) (v m : Fin T → ℝ) :
    ∀ n, (hn : n ≤ T) → ∀ i : Fin n,
      π.feedback u v m n i = max (π.bids u v m ⟨i.val, by omega⟩) (m ⟨i.val, by omega⟩) := by
  intro n
  induction n with
  | zero => intro _ i; exact i.elim0
  | succ n ih =>
    intro hn i
    by_cases hi : i.val < n
    · have hieq : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
      rw [hieq]
      simp only [Policy.feedback, Fin.snoc_castSucc]
      exact ih (by omega) ⟨i.val, hi⟩
    · have hieq : i = Fin.last n := Fin.ext (by simp; omega)
      subst hieq
      have hnT : n < T := by omega
      simp only [Policy.feedback, Fin.snoc_last, dif_pos hnT]
      rfl

lemma ep_le (t : ℕ) : 2 ^ ep t - 1 ≤ t := by
  have := Nat.pow_log_le_self 2 (show t + 1 ≠ 0 by omega)
  unfold ep; omega

/-- the bids of the policy, expressed through the raw HOBs. -/
theorem pol_bids {T : ℕ} (v m : Fin T → ℝ) (t : Fin T) :
    (pol T).bids () v m t = algBid T T (cT T) (fun s => qv T (extV v s)) (extV m) t := by
  set vq : ℕ → ℕ := fun s => qv T (extV v s) with hvq
  set Y : ℕ → ℝ := fun s => if h : s < T then max ((pol T).bids () v m ⟨s, h⟩) (m ⟨s, h⟩)
    else 0 with hY
  -- step 1: every bid is the algorithm's bid on `(vq, Y)`
  have h1 : ∀ t : Fin T, (pol T).bids () v m t = algBid T T (cT T) vq Y t := by
    intro t
    show algBid T T (cT T) (fun s => qv T (extV (fun i : Fin (t.val + 1) =>
        v ⟨i.val, by have := i.isLt; have := t.isLt; omega⟩) s))
      (extV ((pol T).feedback () v m t.val)) t = _
    unfold algBid
    have hloc := theta_local T T (cT T)
      (vq := fun s => qv T (extV (fun i : Fin (t.val + 1) =>
        v ⟨i.val, by have := i.isLt; have := t.isLt; omega⟩) s))
      (vq' := vq) (y := extV ((pol T).feedback () v m t.val)) (y' := Y) (ep t) (by
        intro s hs
        have hst : s < t.val := lt_of_lt_of_le hs (ep_le t)
        have hsT : s < T := by omega
        constructor
        · simp only [hvq, extV, dif_pos (show s < t.val + 1 by omega), dif_pos hsT]
        · simp only [hY, extV, dif_pos hst, dif_pos hsT]
          rw [feedback_apply (pol T) () v m t.val (by omega) ⟨s, hst⟩])
    rw [hloc]
    congr 2
    simp only [hvq, extV, dif_pos (show t.val < t.val + 1 by omega), dif_pos t.isLt]
  -- step 2: the observations are consistent, so thresholds agree with the raw-HOB ones
  have h2 := theta_obs_eq T T (cT T) vq (Y := Y) (m := extV m) (ep t) (by
    intro s hs
    have hsT : s < T := lt_of_lt_of_le hs ((ep_le t).trans (by omega))
    simp only [hY, extV, dif_pos hsT]
    rw [h1 ⟨s, hsT⟩])
  rw [h1 t]
  unfold algBid
  rw [h2]

/-! ## the oracle and the quantized regret -/

lemma cdf_nonneg (μG : Measure ℝ) (x : ℝ) : 0 ≤ cdf μG x := ENNReal.toReal_nonneg

lemma cdf_le_one (μG : Measure ℝ) [IsProbabilityMeasure μG] (x : ℝ) : cdf μG x ≤ 1 := by
  unfold cdf
  have : μG (Set.Iic x) ≤ 1 := prob_le_one
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)

lemma cdf_mono (μG : Measure ℝ) [IsProbabilityMeasure μG] : Monotone (cdf μG) := by
  intro a b hab
  unfold cdf
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.mpr hab))

lemma expReward_bdd (μG : Measure ℝ) [IsProbabilityMeasure μG] (v : ℝ) :
    BddAbove (Set.range fun b : Set.Icc (0 : ℝ) 1 => expReward μG v b) := by
  refine ⟨|v| + 1, ?_⟩
  rintro _ ⟨b, rfl⟩
  unfold expReward
  have h0 := cdf_nonneg μG b
  have h1 := cdf_le_one μG b
  have hb := b.2
  have : (v - b) * cdf μG b ≤ |v - b| * 1 := by
    calc (v - b) * cdf μG b ≤ |v - b| * cdf μG b :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ |v - b| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have h3 : |v - b| ≤ |v| + 1 := by
    rw [abs_le]; constructor
    · linarith [neg_abs_le v, hb.1, hb.2]
    · linarith [le_abs_self v, hb.1, hb.2]
  linarith

lemma le_oracle (μG : Measure ℝ) [IsProbabilityMeasure μG] (v b : ℝ) (hb : b ∈ Set.Icc (0:ℝ) 1) :
    expReward μG v b ≤ oracle μG v :=
  le_ciSup (f := fun b : Set.Icc (0 : ℝ) 1 => expReward μG v b) (expReward_bdd μG v) ⟨b, hb⟩

lemma oracle_le_one (μG : Measure ℝ) [IsProbabilityMeasure μG] {v : ℝ} (hv : v ≤ 1) :
    oracle μG v ≤ 1 := by
  unfold oracle
  apply ciSup_le
  intro b
  unfold expReward
  have h0 := cdf_nonneg μG b
  have h1 := cdf_le_one μG b
  have hb := b.2
  rcases le_total 0 (v - b) with h | h
  · nlinarith [hb.1]
  · nlinarith

lemma expReward_ge (μG : Measure ℝ) [IsProbabilityMeasure μG] {v b : ℝ} (hv : 0 ≤ v)
    (hb : b ≤ 1) : -1 ≤ expReward μG v b := by
  unfold expReward
  have h0 := cdf_nonneg μG b
  have h1 := cdf_le_one μG b
  rcases le_total 0 (v - b) with h | h
  · nlinarith
  · nlinarith

lemma oracle_mono (μG : Measure ℝ) [IsProbabilityMeasure μG] : Monotone (oracle μG) := by
  intro a b hab
  unfold oracle
  apply ciSup_mono (expReward_bdd μG b)
  intro x
  unfold expReward
  exact mul_le_mul_of_nonneg_right (by linarith) (cdf_nonneg μG x)

/-- quantization lemma: the true per-round regret is at most `1/K + 1/M` plus the quantized one. -/
theorem round_regret_le {K M : ℕ} (hK : 1 ≤ K) (hM : 1 ≤ M) (μG : Measure ℝ)
    [IsProbabilityMeasure μG] {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (j : ℕ) :
    oracle μG v - expReward μG v (gb K j) ≤
      1 / K + 1 / M + (Rq K M (cdf μG) (qv M v) (Jst K M (cdf μG) (qv M v)) -
        Rq K M (cdf μG) (qv M v) j) := by
  set i := qv M v
  have hg0 := cdf_nonneg μG
  have hg1 := cdf_le_one μG
  have hgm := cdf_mono μG
  have hgv1 := gv_qv_le hM hv0
  have hgv2 := v_le_gv_qv hM hv0 hv1
  obtain ⟨hJK, hJmax⟩ := Jmax_spec hK (Rq K M (cdf μG) i)
  have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  -- grid expected reward vs quantized reward
  have hgrid : ∀ j' < K, expReward μG v (gb K j') ≤ Rq K M (cdf μG) i (Jst K M (cdf μG) i) + 1 / M := by
    intro j' hj'
    have h1 : Rq K M (cdf μG) i j' ≤ Rq K M (cdf μG) i (Jst K M (cdf μG) i) := hJmax j' hj'
    have h2 : expReward μG v (gb K j') ≤ Rq K M (cdf μG) i j' + 1 / M := by
      unfold expReward Rq
      have a1 : 0 ≤ cdf μG (gb K j') := hg0 _
      have a2 : cdf μG (gb K j') ≤ 1 := hg1 _
      have : (v - gv M i) * cdf μG (gb K j') ≤ 1 / M := by
        calc (v - gv M i) * cdf μG (gb K j') ≤ (1 / M) * 1 :=
              mul_le_mul (by linarith) a2 a1 (by positivity)
          _ = 1 / M := mul_one _
      nlinarith
    linarith
  have horacle : oracle μG v ≤ Rq K M (cdf μG) i (Jst K M (cdf μG) i) + 1 / M + 1 / K := by
    unfold oracle
    apply ciSup_le
    rintro ⟨b, hb0, hb1⟩
    simp only
    -- choose the grid point just above `b`
    set j0 := ⌈b * K⌉₊ - 1 with hj0
    have hj0K : j0 < K := by
      have : ⌈b * K⌉₊ ≤ K := by
        rw [Nat.ceil_le]; nlinarith
      omega
    have hgbj0 : gb K j0 = ((j0 : ℝ) + 1) / K := by
      unfold gb; rw [min_eq_left (by omega)]
    have hup : b ≤ gb K j0 := by
      rw [hgbj0, le_div_iff₀ hKr]
      have := Nat.le_ceil (b * K)
      have : (⌈b * K⌉₊ : ℝ) ≤ (j0 : ℝ) + 1 := by
        have : ⌈b * K⌉₊ ≤ j0 + 1 := by omega
        exact_mod_cast this
      linarith
    have hlo : gb K j0 ≤ b + 1 / K := by
      rw [hgbj0, div_le_iff₀ hKr, add_mul, div_mul_cancel₀ _ hKr.ne']
      by_cases hc : ⌈b * K⌉₊ = 0
      · have : j0 = 0 := by omega
        rw [this]; simp; nlinarith
      · have : (j0 : ℝ) + 1 = (⌈b * K⌉₊ : ℝ) := by
          have : j0 + 1 = ⌈b * K⌉₊ := by omega
          exact_mod_cast this
        rw [this]
        have := Nat.ceil_lt_add_one (show 0 ≤ b * K by positivity)
        linarith
    have hg_le := hgrid j0 hj0K
    unfold expReward at hg_le ⊢
    have hgb := hgm hup
    have := hg0 b; have := hg1 (gb K j0)
    rcases le_total b v with hbv | hbv
    · -- (v-b) (cdf μG)(b) ≤ (v-b) (cdf μG)(gb) = (v - gb) (cdf μG)(gb) + (gb - b) (cdf μG)(gb)
      have e1 : (v - b) * (cdf μG) b ≤ (v - b) * (cdf μG) (gb K j0) :=
        mul_le_mul_of_nonneg_left hgb (by linarith)
      have e2 : (gb K j0 - b) * (cdf μG) (gb K j0) ≤ 1 / K := by
        calc (gb K j0 - b) * (cdf μG) (gb K j0) ≤ (1 / K) * 1 := by
              apply mul_le_mul (by linarith) (hg1 _) (hg0 _) (by positivity)
          _ = 1 / K := mul_one _
      nlinarith
    · -- nonpositive reward; compare with grid point 0
      have h0 := hgrid 0 (by omega)
      unfold expReward at h0
      have hgb0 := gb_pos hK 0
      have hgb0' : gb K 0 = 1 / K := by unfold gb; simp
      have : -(1 / K) ≤ (v - gb K 0) * (cdf μG) (gb K 0) := by
        rw [hgb0']
        have := hg0 (1 / K); have := hg1 (1 / K)
        nlinarith
      have : (v - b) * (cdf μG) b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hg0 b)
      linarith
  have hlow : Rq K M (cdf μG) i j ≤ expReward μG v (gb K j) := by
    unfold Rq expReward
    exact mul_le_mul_of_nonneg_right (by linarith) (hg0 _)
  linarith

end FPA1

-- ===== part Meas =====

open MeasureTheory
open scoped Classical
open FirstPriceLearning.Stochastic

namespace FPA1

section Meas

variable {Ω : Type*} [MeasurableSpace Ω]

lemma meas_nat_comp {f : Ω → ℕ → ℕ} (hf : ∀ i, Measurable fun ω => f ω i) {k : Ω → ℕ}
    (hk : Measurable k) : Measurable fun ω => f ω (k ω) := by
  have h2 : Measurable fun p : Ω × ℕ => f p.1 p.2 :=
    measurable_from_prod_countable_left (fun n => hf n)
  exact h2.comp (measurable_id.prodMk hk)

lemma meas_nat_comp_real {f : Ω → ℕ → ℝ} (hf : ∀ i, Measurable fun ω => f ω i) {k : Ω → ℕ}
    (hk : Measurable k) : Measurable fun ω => f ω (k ω) := by
  have h2 : Measurable fun p : Ω × ℕ => f p.1 p.2 :=
    measurable_from_prod_countable_left (fun n => hf n)
  exact h2.comp (measurable_id.prodMk hk)

lemma meas_card_filter (s : Finset ℕ) {p : Ω → ℕ → Prop} [∀ ω, DecidablePred (p ω)]
    (hp : ∀ x, MeasurableSet {ω | p ω x}) : Measurable fun ω => (s.filter (p ω)).card := by
  simp_rw [Finset.card_filter]
  apply Finset.measurable_sum
  intro x _
  exact Measurable.ite (hp x) measurable_const measurable_const

lemma meas_tbar {θ : Ω → ℕ → ℕ} (hθ : ∀ i, Measurable fun ω => θ ω i) :
    ∀ i, Measurable fun ω => tbar (θ ω) i := by
  intro i
  induction i with
  | zero =>
    have : (fun ω => tbar (θ ω) 0) = fun ω => θ ω 0 := by
      funext ω; simp [tbar]
    rw [this]; exact hθ 0
  | succ i ih =>
    have : (fun ω => tbar (θ ω) (i + 1)) = fun ω => max (θ ω (i + 1)) (tbar (θ ω) i) := by
      funext ω
      simp only [tbar]
      rw [Finset.range_add_one, Finset.sup_insert]
    rw [this]; exact (hθ (i + 1)).max ih

variable {K M : ℕ} {c : ℝ} {vq : Ω → ℕ → ℕ} {y : Ω → ℕ → ℝ}

lemma meas_samp_card (e : ℕ) {tb : Ω → ℕ → ℕ} (htb : ∀ i, Measurable fun ω => tb ω i)
    (hvq : ∀ s, Measurable fun ω => vq ω s) (j : ℕ) :
    Measurable fun ω => (samp e (tb ω) (vq ω) j).card := by
  unfold samp
  apply meas_card_filter
  intro s
  exact measurableSet_le (meas_nat_comp htb (hvq s)) measurable_const

lemma meas_ghat (e : ℕ) {tb : Ω → ℕ → ℕ} (htb : ∀ i, Measurable fun ω => tb ω i)
    (hvq : ∀ s, Measurable fun ω => vq ω s) (hy : ∀ s, Measurable fun ω => y ω s) (j : ℕ) :
    Measurable fun ω => ghat K (samp e (tb ω) (vq ω) j) (y ω) j := by
  unfold ghat
  apply Measurable.div
  · apply (measurable_of_countable (Nat.cast : ℕ → ℝ)).comp
    unfold samp
    simp_rw [Finset.filter_filter]
    apply meas_card_filter
    intro s
    exact (measurableSet_le (meas_nat_comp htb (hvq s)) measurable_const).inter
      (measurableSet_le (hy s) measurable_const)
  · exact (measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (meas_samp_card e htb hvq j)

lemma meas_ucb (e : ℕ) {tb : Ω → ℕ → ℕ} (htb : ∀ i, Measurable fun ω => tb ω i)
    (hvq : ∀ s, Measurable fun ω => vq ω s) (hy : ∀ s, Measurable fun ω => y ω s) (i j : ℕ) :
    Measurable (fun ω => ucb K M c e (tb ω) (vq ω) (y ω) i j) ∧
      Measurable (fun ω => lcb K M c e (tb ω) (vq ω) (y ω) i j) := by
  have h1 := meas_ghat (K := K) e htb hvq hy j
  have h2 : Measurable fun ω => wd c (samp e (tb ω) (vq ω) j).card :=
    (measurable_of_countable (wd c)).comp (meas_samp_card e htb hvq j)
  unfold ucb lcb
  exact ⟨(measurable_const.mul h1).add h2, (measurable_const.mul h1).sub h2⟩

lemma meas_pred (e : ℕ) {tb : Ω → ℕ → ℕ} (htb : ∀ i, Measurable fun ω => tb ω i)
    (hvq : ∀ s, Measurable fun ω => vq ω s) (hy : ∀ s, Measurable fun ω => y ω s) (i j : ℕ) :
    MeasurableSet {ω | pred K M c e (tb ω) (vq ω) (y ω) i j} := by
  unfold pred
  rw [measurableSet_setOfPred]
  apply Measurable.and
  · exact measurableSet_setOfPred.mp (measurableSet_le (htb i) measurable_const)
  · apply Measurable.forall
    intro j'
    apply Measurable.imp measurable_const
    apply Measurable.imp
    · exact measurableSet_setOfPred.mp (measurableSet_le (htb i) measurable_const)
    · exact measurableSet_setOfPred.mp
        (measurableSet_le (meas_ucb (K := K) (M := M) (c := c) e htb hvq hy i j').2
          (meas_ucb (K := K) (M := M) (c := c) e htb hvq hy i j).1)

lemma meas_nextθ (e : ℕ) {θ : Ω → ℕ → ℕ} (hθ : ∀ i, Measurable fun ω => θ ω i)
    (hvq : ∀ s, Measurable fun ω => vq ω s) (hy : ∀ s, Measurable fun ω => y ω s) (i : ℕ) :
    Measurable fun ω => nextθ K M c e (θ ω) (vq ω) (y ω) i := by
  unfold nextθ
  apply (measurable_of_countable (fun n : ℕ => min (K - 1) n)).comp
  apply meas_card_filter
  intro j
  rw [measurableSet_setOfPred]
  apply Measurable.forall
  intro j''
  apply Measurable.imp measurable_const
  exact (measurableSet_setOfPred.mp (meas_pred (K := K) (M := M) (c := c) e (meas_tbar hθ)
    hvq hy i j'')).not

theorem meas_theta (hvq : ∀ s, Measurable fun ω => vq ω s) (hy : ∀ s, Measurable fun ω => y ω s) :
    ∀ e i, Measurable fun ω => theta K M c (vq ω) (y ω) e i := by
  intro e
  induction e with
  | zero => intro i; exact measurable_const
  | succ e ih =>
    intro i
    exact meas_nextθ e ih hvq hy i

theorem meas_algBid (hvq : ∀ s, Measurable fun ω => vq ω s)
    (hy : ∀ s, Measurable fun ω => y ω s) (t : ℕ) :
    Measurable fun ω => algBid K M c (vq ω) (y ω) t := by
  unfold algBid
  exact (measurable_of_countable (gb K)).comp
    (meas_nat_comp (meas_theta hvq hy (ep t)) (hvq t))

end Meas

lemma measurable_qv (M : ℕ) : Measurable (qv M) := by
  unfold qv
  exact (measurable_of_countable (fun n : ℕ => min n (M - 1))).comp
    (Nat.measurable_floor.comp (measurable_id.mul_const _))

lemma measurable_extV {T : ℕ} (s : ℕ) : Measurable fun x : Fin T → ℝ => extV x s := by
  unfold extV
  by_cases h : s < T
  · simp only [dif_pos h]; exact measurable_pi_apply _
  · simp only [dif_neg h]; exact measurable_const

lemma measurable_cdf (μG : Measure ℝ) [IsProbabilityMeasure μG] : Measurable (cdf μG) :=
  (cdf_mono μG).measurable

lemma measurable_oracle (μG : Measure ℝ) [IsProbabilityMeasure μG] : Measurable (oracle μG) :=
  (oracle_mono μG).measurable

end FPA1

-- ===== part Prob =====

open MeasureTheory
open scoped Classical
open FirstPriceLearning.Stochastic

namespace FPA1

/-! ## the rank function -/

noncomputable def hf (n : ℕ) : ℝ := Real.sqrt (2 / ((n : ℝ) + 1))

lemma hf_nonneg (n : ℕ) : 0 ≤ hf n := Real.sqrt_nonneg _

lemma hf_le (n : ℕ) : hf n ≤ Real.sqrt 2 := by
  unfold hf
  apply Real.sqrt_le_sqrt
  rw [div_le_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

lemma hf_anti : Antitone hf := by
  intro a b hab
  unfold hf
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  have : (a : ℝ) ≤ b := by exact_mod_cast hab
  linarith

lemma wd_le_hf {c : ℝ} (hc : 1 ≤ c) (n : ℕ) : wd c n ≤ Real.sqrt c * hf n := by
  unfold wd hf
  rw [← Real.sqrt_mul (by linarith)]
  split_ifs with h
  · subst h
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_le_sqrt
    simp; linarith
  · apply (min_le_right _ _).trans
    apply Real.sqrt_le_sqrt
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

lemma sum_inv_sqrt_le (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / Real.sqrt ((k : ℝ) + 1) ≤ 2 * Real.sqrt n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have ha := Real.sqrt_nonneg (n : ℝ)
    have hb : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hab2 : Real.sqrt ((n : ℝ) + 1) ^ 2 = Real.sqrt n ^ 2 + 1 := by
      rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    have key : 1 / Real.sqrt ((n : ℝ) + 1) ≤ 2 * Real.sqrt ((n : ℝ) + 1) - 2 * Real.sqrt n := by
      rw [div_le_iff₀ hb]
      nlinarith [sq_nonneg (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n)]
    push_cast
    linarith

lemma sum_hf_le (n : ℕ) : ∑ k ∈ Finset.range n, hf k ≤ 2 * Real.sqrt 2 * Real.sqrt n := by
  have : ∀ k : ℕ, hf k = Real.sqrt 2 * (1 / Real.sqrt ((k : ℝ) + 1)) := by
    intro k
    unfold hf
    rw [Real.sqrt_div' _ (by positivity)]
    ring
  simp_rw [this]
  rw [← Finset.mul_sum]
  have := sum_inv_sqrt_le n
  have h2 := Real.sqrt_nonneg 2
  nlinarith

/-! ## deterministic rank-sum bound -/

lemma rank_sum (E : Finset ℕ) (f : ℕ → ℕ) {h : ℕ → ℝ} (hh : Antitone h) :
    ∑ i ∈ E, h ((E.erase i).filter (fun s => f s ≤ f i)).card ≤
      ∑ k ∈ Finset.range E.card, h k := by
  induction E using Finset.induction_on_max_value (f := f) with
  | empty => simp
  | insert a s ha hmax ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Finset.sum_range_succ]
    have h1 : ((insert a s).erase a).filter (fun x => f x ≤ f a) = s := by
      rw [Finset.erase_insert ha]
      exact Finset.filter_true_of_mem (fun x hx => hmax x hx)
    rw [h1]
    have h2 : ∑ i ∈ s, h (((insert a s).erase i).filter (fun x => f x ≤ f i)).card ≤
        ∑ i ∈ s, h ((s.erase i).filter (fun x => f x ≤ f i)).card := by
      apply Finset.sum_le_sum
      intro i hi
      apply hh
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_insert] at hx ⊢
      exact ⟨⟨hx.1.1, Or.inr hx.1.2⟩, hx.2⟩
    linarith

lemma card_swap (E' : Finset ℕ) {i t : ℕ} (hi : i ∈ E') (ht : t ∈ E') (P : ℕ → Prop)
    [DecidablePred P] :
    ((E'.erase i).filter (fun s => P (Equiv.swap i t s))).card = ((E'.erase t).filter P).card := by
  apply Finset.card_bij' (fun s _ => Equiv.swap i t s) (fun s _ => Equiv.swap i t s)
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_erase] at hs ⊢
    refine ⟨⟨?_, ?_⟩, hs.2⟩
    · intro h; apply hs.1.1
      have := congrArg (Equiv.swap i t) h
      simpa using this
    · rw [Equiv.swap_apply_def]
      split_ifs <;> simp_all
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_erase] at hs ⊢
    refine ⟨⟨?_, ?_⟩, by simpa using hs.2⟩
    · intro h; apply hs.1.1
      have := congrArg (Equiv.swap i t) h
      simpa using this
    · rw [Equiv.swap_apply_def]
      split_ifs <;> simp_all
  · intro s _; simp
  · intro s _; simp

lemma fin_swap_val {T : ℕ} (a b x : Fin T) :
    ((Equiv.swap a b x : Fin T) : ℕ) = Equiv.swap (a : ℕ) (b : ℕ) (x : ℕ) := by
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff]

lemma extV_swap {T : ℕ} (x : Fin T → ℝ) (a b : Fin T) (s : ℕ) :
    extV (fun k => x (Equiv.swap a b k)) s = extV x (Equiv.swap (a : ℕ) (b : ℕ) s) := by
  unfold extV
  by_cases hs : s < T
  · have hs' : Equiv.swap (a : ℕ) (b : ℕ) s < T := by
      rw [Equiv.swap_apply_def]; split_ifs <;> simp [a.isLt, b.isLt, hs]
    rw [dif_pos hs, dif_pos hs']
    show x (Equiv.swap a b ⟨s, hs⟩) = x ⟨_, hs'⟩
    congr 1
    apply Fin.ext
    rw [fin_swap_val]
  · have h1 : s ≠ (a : ℕ) := by have := a.isLt; omega
    have h2 : s ≠ (b : ℕ) := by have := b.isLt; omega
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2, dif_neg hs, dif_neg hs]

/-- the expected rank bound (exchangeability argument). -/
theorem rank_exp {T : ℕ} (F : Measure ℝ) [IsProbabilityMeasure F] (q : ℝ → ℕ)
    (hq : Measurable q) (E : Finset ℕ) (hE : ∀ s ∈ E, s < T) (t : ℕ) (ht : t < T)
    (htE : t ∉ E) :
    ∫ x, hf ((E.filter (fun s => q (extV x s) ≤ q (extV x t))).card)
        ∂(Measure.pi fun _ : Fin T => F) ≤
      (∑ k ∈ Finset.range (E.card + 1), hf k) / (E.card + 1) := by
  set μ := Measure.pi fun _ : Fin T => F
  set E' := insert t E with hE'
  have hE'T : ∀ s ∈ E', s < T := by
    intro s hs
    rcases Finset.mem_insert.mp hs with h | h
    · rw [h]; exact ht
    · exact hE s h
  let R : ℕ → (Fin T → ℝ) → ℕ := fun i x =>
    ((E'.erase i).filter (fun s => q (extV x s) ≤ q (extV x i))).card
  have hRt : ∀ x, (E.filter (fun s => q (extV x s) ≤ q (extV x t))).card = R t x := by
    intro x
    simp only [R, hE', Finset.erase_insert htE]
  have hmeasR : ∀ i, Measurable (R i) := by
    intro i
    apply meas_card_filter
    intro s
    exact measurableSet_le ((hq.comp (measurable_extV s))) (hq.comp (measurable_extV i))
  have hint : ∀ i, Integrable (fun x => hf (R i x)) μ := by
    intro i
    apply Integrable.of_bound
      (((measurable_of_countable hf).comp (hmeasR i)).aestronglyMeasurable) (Real.sqrt 2)
    apply Filter.Eventually.of_forall
    intro x
    show |hf (R i x)| ≤ _
    rw [abs_of_nonneg (hf_nonneg _)]
    exact hf_le _
  -- exchangeability
  have hswap : ∀ i ∈ E', ∫ x, hf (R t x) ∂μ = ∫ x, hf (R i x) ∂μ := by
    intro i hi
    have hiT := hE'T i hi
    set σ : Fin T ≃ Fin T := Equiv.swap ⟨i, hiT⟩ ⟨t, ht⟩
    have hmp := measurePreserving_arrowCongr' (fun _ : Fin T => F) (fun _ : Fin T => F) σ
      (MeasurableEquiv.refl ℝ) (fun _ => MeasurePreserving.id F)
    rw [← hmp.integral_comp' (fun x => hf (R i x))]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    simp only
    congr 1
    have hΦ : (MeasurableEquiv.arrowCongr' σ (MeasurableEquiv.refl ℝ)) x =
        fun k => x (Equiv.swap (⟨i, hiT⟩ : Fin T) ⟨t, ht⟩ k) := by
      funext k
      simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', σ, Equiv.symm_swap]
    rw [hΦ]
    simp only [R]
    simp_rw [extV_swap]
    simp only [Equiv.swap_apply_left]
    have := card_swap E' hi (Finset.mem_insert_self t E)
      (fun s => q (extV x s) ≤ q (extV x t))
    rw [← this]
  have hsum : ∀ x, ∑ i ∈ E', hf (R i x) ≤ ∑ k ∈ Finset.range E'.card, hf k :=
    fun x => rank_sum E' (fun s => q (extV x s)) hf_anti
  have hcard : E'.card = E.card + 1 := Finset.card_insert_of_notMem htE
  have key : (E'.card : ℝ) * ∫ x, hf (R t x) ∂μ ≤ ∑ k ∈ Finset.range E'.card, hf k := by
    calc (E'.card : ℝ) * ∫ x, hf (R t x) ∂μ = ∑ i ∈ E', ∫ x, hf (R t x) ∂μ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ i ∈ E', ∫ x, hf (R i x) ∂μ := Finset.sum_congr rfl hswap
      _ = ∫ x, ∑ i ∈ E', hf (R i x) ∂μ := (integral_finsetSum _ (fun i _ => hint i)).symm
      _ ≤ ∫ x, (∑ k ∈ Finset.range E'.card, hf k) ∂μ := by
          apply integral_mono (integrable_finsetSum _ (fun i _ => hint i))
            (integrable_const _) hsum
      _ = ∑ k ∈ Finset.range E'.card, hf k := by simp
  simp_rw [hRt]
  rw [hcard] at key
  push_cast at key
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact key

end FPA1

-- ===== part Hoef =====

open MeasureTheory
open scoped Classical
open FirstPriceLearning.Stochastic

namespace FPA1

lemma hoeff_one {T : ℕ} (G : Measure ℝ) [IsProbabilityMeasure G] (D : Finset (Fin T))
    (φ : ℝ → ℝ) (hφ : Measurable φ) (lo : ℝ) (hφb : ∀ x, φ x ∈ Set.Icc lo (lo + 1))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin T => G).real {m | ε ≤ ∑ s ∈ D, (φ (m s) - ∫ x, φ x ∂G)} ≤
      Real.exp (-2 * ε ^ 2 / D.card) := by
  set μ := Measure.pi fun _ : Fin T => G
  have hind : ProbabilityTheory.iIndepFun
      (fun (i : Fin T) (m : Fin T → ℝ) => φ (m i) - ∫ x, φ x ∂G) μ :=
    ProbabilityTheory.iIndepFun_pi (X := fun _ x => φ x - ∫ x, φ x ∂G)
      (fun _ => (hφ.sub_const _).aemeasurable)
  have hint : ∀ i : Fin T, ∫ m, φ (m i) ∂μ = ∫ x, φ x ∂G := by
    intro i
    have hmp := measurePreserving_eval (fun _ : Fin T => G) i
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hφ.aestronglyMeasurable]
  have hsub : ∀ i ∈ D, ProbabilityTheory.HasSubgaussianMGF
      (fun m : Fin T → ℝ => φ (m i) - ∫ x, φ x ∂G) ((‖(lo + 1) - lo‖₊ / 2) ^ 2) μ := by
    intro i _
    have := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := fun m => φ (m i))
      (a := lo) (b := lo + 1) ((hφ.comp (measurable_pi_apply i)).aemeasurable)
      (Filter.Eventually.of_forall (fun m => hφb (m i)))
    rw [hint i] at this
    exact this
  have h := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub hε
  refine h.trans (le_of_eq ?_)
  congr 1
  have h1 : (‖(lo + 1) - lo‖₊ : NNReal) = 1 := by simp
  rw [h1]
  simp only [Finset.sum_const, nsmul_eq_mul]
  push_cast
  rcases Nat.eq_zero_or_pos D.card with h0 | h0
  · rw [h0]; simp
  · have : (0 : ℝ) < D.card := by exact_mod_cast h0
    field_simp

lemma hoeff_ind {T : ℕ} (G : Measure ℝ) [IsProbabilityMeasure G] (D : Finset (Fin T)) (a : ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin T => G).real
        {m | ε ≤ |∑ s ∈ D, ((Set.Iic a).indicator (fun _ => (1 : ℝ)) (m s) - cdf G a)|} ≤
      2 * Real.exp (-2 * ε ^ 2 / D.card) := by
  set ind : ℝ → ℝ := (Set.Iic a).indicator (fun _ => (1 : ℝ))
  have hindm : Measurable ind := (measurable_const.indicator measurableSet_Iic)
  have hint : ∫ x, ind x ∂G = cdf G a := by
    rw [integral_indicator_const _ measurableSet_Iic]
    simp [cdf, measureReal_def]
  have h1 := hoeff_one G D ind hindm 0 (by
    intro x; simp only [ind, Set.indicator_apply]; split_ifs <;> norm_num) hε
  have h2 := hoeff_one G D (fun x => - ind x) hindm.neg (-1) (by
    intro x; simp only [ind, Set.indicator_apply]; split_ifs <;> norm_num) hε
  rw [hint] at h1
  have hint2 : ∫ x, -ind x ∂G = - cdf G a := by rw [integral_neg, hint]
  rw [hint2] at h2
  calc (Measure.pi fun _ : Fin T => G).real
        {m | ε ≤ |∑ s ∈ D, (ind (m s) - cdf G a)|}
      ≤ (Measure.pi fun _ : Fin T => G).real
          ({m | ε ≤ ∑ s ∈ D, (ind (m s) - cdf G a)} ∪
            {m | ε ≤ ∑ s ∈ D, (-ind (m s) - -cdf G a)}) := by
        apply measureReal_mono _ (measure_ne_top _ _)
        intro m hm
        simp only [Set.mem_ofPred_eq, Set.mem_union] at hm ⊢
        rcases le_abs'.mp hm with h | h
        · right
          have : ∑ s ∈ D, (-ind (m s) - -cdf G a) = -∑ s ∈ D, (ind (m s) - cdf G a) := by
            rw [← Finset.sum_neg_distrib]; congr 1; funext s; ring
          rw [this]; linarith
        · left; exact h
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by linarith

lemma sum_extV {T : ℕ} (D : Finset ℕ) (hD : ∀ s ∈ D, s < T) (f : ℝ → ℝ) (m : Fin T → ℝ) :
    ∑ s ∈ (Finset.univ.filter (fun s : Fin T => (s : ℕ) ∈ D)), f (m s) =
      ∑ s ∈ D, f (extV m s) := by
  apply Finset.sum_bij (fun (s : Fin T) _ => (s : ℕ))
  · intro s hs; simpa using hs
  · intro a _ b _ h; exact Fin.ext h
  · intro b hb
    exact ⟨⟨b, hD b hb⟩, by simpa using hb, rfl⟩
  · intro s _
    simp [extV, s.isLt]

lemma card_extV {T : ℕ} (D : Finset ℕ) (hD : ∀ s ∈ D, s < T) :
    (Finset.univ.filter (fun s : Fin T => (s : ℕ) ∈ D)).card = D.card := by
  have := sum_extV D hD (fun _ => (1 : ℝ)) (fun _ => 0)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
  exact_mod_cast this

/-- one bad slice. -/
lemma bad_slice {T : ℕ} (G : Measure ℝ) [IsProbabilityMeasure G] (D : Finset ℕ)
    (hD : ∀ s ∈ D, s < T) (hne : D.Nonempty) (a : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (Measure.pi fun _ : Fin T => G)
        {m | wd c D.card < |((D.filter (fun s => extV m s ≤ a)).card : ℝ) / D.card - cdf G a|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * c)) := by
  set n := D.card with hn
  have hnpos : 0 < n := Finset.card_pos.mpr hne
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  set ind : ℝ → ℝ := (Set.Iic a).indicator (fun _ => (1 : ℝ))
  set D' := Finset.univ.filter (fun s : Fin T => (s : ℕ) ∈ D)
  have hcardD' : D'.card = n := card_extV D hD
  -- rewrite the empirical frequency
  have hfreq : ∀ m : Fin T → ℝ, ((D.filter (fun s => extV m s ≤ a)).card : ℝ) / n - cdf G a =
      (∑ s ∈ D', (ind (m s) - cdf G a)) / n := by
    intro m
    rw [sum_extV D hD (fun x => ind x - cdf G a) m, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, Finset.card_filter]
    push_cast
    have : ∑ s ∈ D, ind (extV m s) = ∑ s ∈ D, (if extV m s ≤ a then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro s _
      simp [ind, Set.indicator_apply]
    rw [this, hn]
    field_simp
  have hg0 := cdf_nonneg G a
  have hg1 := cdf_le_one G a
  by_cases hw : 1 ≤ Real.sqrt (c / n)
  · -- the width is `1`: the event is empty
    have hwd : wd c n = 1 := by
      unfold wd; rw [if_neg (by omega)]; exact min_eq_left hw
    have : {m : Fin T → ℝ | wd c D.card <
        |((D.filter (fun s => extV m s ≤ a)).card : ℝ) / D.card - cdf G a|} = ∅ := by
      ext m
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [← hn, hwd]
      have h1 : (0 : ℝ) ≤ ((D.filter (fun s => extV m s ≤ a)).card : ℝ) / n := by positivity
      have h2 : ((D.filter (fun s => extV m s ≤ a)).card : ℝ) / n ≤ 1 := by
        rw [div_le_one hnr]
        exact_mod_cast Finset.card_filter_le _ _
      rw [abs_le]; constructor <;> linarith
    rw [this, measure_empty]; exact zero_le
  · push Not at hw
    have hwd : wd c n = Real.sqrt (c / n) := by
      unfold wd; rw [if_neg (by omega)]; exact min_eq_right hw.le
    have hsub : {m : Fin T → ℝ | wd c D.card <
        |((D.filter (fun s => extV m s ≤ a)).card : ℝ) / D.card - cdf G a|} ⊆
        {m | Real.sqrt (c * n) ≤ |∑ s ∈ D', (ind (m s) - cdf G a)|} := by
      intro m hm
      simp only [Set.mem_ofPred_eq] at hm ⊢
      rw [← hn, hwd, hfreq m, abs_div, abs_of_pos hnr, lt_div_iff₀ hnr] at hm
      have : Real.sqrt (c / n) * n = Real.sqrt (c * n) := by
        rw [show c * n = (c / n) * n ^ 2 by field_simp, Real.sqrt_mul (by positivity),
          Real.sqrt_sq hnr.le]
      linarith
    have hh := hoeff_ind G D' a (ε := Real.sqrt (c * n)) (Real.sqrt_nonneg _)
    rw [hcardD', Real.sq_sqrt (by positivity)] at hh
    have : -2 * (c * n) / n = -2 * c := by field_simp
    rw [this] at hh
    calc (Measure.pi fun _ : Fin T => G) {m | wd c D.card <
          |((D.filter (fun s => extV m s ≤ a)).card : ℝ) / D.card - cdf G a|}
        ≤ (Measure.pi fun _ : Fin T => G)
            {m | Real.sqrt (c * n) ≤ |∑ s ∈ D', (ind (m s) - cdf G a)|} := measure_mono hsub
      _ = ENNReal.ofReal ((Measure.pi fun _ : Fin T => G).real
            {m | Real.sqrt (c * n) ≤ |∑ s ∈ D', (ind (m s) - cdf G a)|}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (2 * Real.exp (-2 * c)) := ENNReal.ofReal_le_ofReal hh

end FPA1

-- ===== part Main =====

open MeasureTheory
open scoped Classical
open FirstPriceLearning.Stochastic

namespace FPA1

/-! ## epoch arithmetic -/

lemma lt_pow_ep (r : ℕ) : r + 1 < 2 ^ (ep r + 1) := by
  unfold ep
  exact Nat.lt_pow_succ_log_self (by norm_num) _

lemma mem_epoch_ep (r : ℕ) : r ∈ epoch (ep r) := by
  simp only [epoch, Finset.mem_Ico]
  have h1 := ep_le r
  have h2 := lt_pow_ep r
  constructor <;> omega

lemma ep_pos {t : ℕ} (ht : 1 ≤ t) : 1 ≤ ep t := by
  unfold ep
  exact Nat.log_pos (by norm_num) (by omega)

/-! ## the analysed quantities -/

noncomputable def vqOf (T : ℕ) (x : Fin T → ℝ) (s : ℕ) : ℕ := qv T (extV x s)

noncomputable def Rg (T : ℕ) (μG : Measure ℝ) (p : (Fin T → ℝ) × (Fin T → ℝ)) : ℝ :=
  regret μG p.1 (fun t => algBid T T (cT T) (vqOf T p.1) (extV p.2) t)

noncomputable def Ncnt (T : ℕ) (x : Fin T → ℝ) (t : ℕ) : ℕ :=
  ((epoch (ep t - 1)).filter (fun s => vqOf T x s ≤ vqOf T x t)).card

def Good (T : ℕ) (μG : Measure ℝ) (x m : Fin T → ℝ) : Prop :=
  ∀ r < T, 2 ^ (ep r + 1) - 1 ≤ T → ∀ j < T,
    |ghat T (dset (ep r) (vqOf T x) r) (extV m) j - cdf μG (gb T j)| ≤
      wd (cT T) (dset (ep r) (vqOf T x) r).card

def Bset (T : ℕ) (μG : Measure ℝ) (r j : ℕ) : Set ((Fin T → ℝ) × (Fin T → ℝ)) :=
  {p | wd (cT T) (dset (ep r) (vqOf T p.1) r).card <
    |ghat T (dset (ep r) (vqOf T p.1) r) (extV p.2) j - cdf μG (gb T j)|}

def Sbad (T : ℕ) (μG : Measure ℝ) : Set ((Fin T → ℝ) × (Fin T → ℝ)) :=
  ⋃ r ∈ (Finset.range T).filter (fun r => 2 ^ (ep r + 1) - 1 ≤ T), ⋃ j ∈ Finset.range T,
    Bset T μG r j

lemma good_of_not_bad {T : ℕ} {μG : Measure ℝ} {p : (Fin T → ℝ) × (Fin T → ℝ)}
    (h : p ∉ Sbad T μG) : Good T μG p.1 p.2 := by
  intro r hr hc j hj
  by_contra hcon
  push Not at hcon
  apply h
  simp only [Sbad, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range]
  exact ⟨r, ⟨hr, hc⟩, j, hj, hcon⟩

lemma cT_ge_one {T : ℕ} (hT : 2 ≤ T) : 1 ≤ cT T := by
  unfold cT
  have h1 : Real.log 2 ≤ Real.log T :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  have := Real.log_two_gt_d9
  linarith

/-! ## the deterministic per-round bound -/

lemma round_bounds (μG : Measure ℝ) [IsProbabilityMeasure μG] {v b : ℝ}
    (hv : v ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ oracle μG v - expReward μG v b ∧ oracle μG v - expReward μG v b ≤ 2 := by
  have h1 := le_oracle μG v b hb
  have h2 := oracle_le_one μG hv.2
  have h3 := expReward_ge μG hv.1 hb.2
  constructor <;> linarith

theorem round_good {T : ℕ} (hT : 2 ≤ T) (μG : Measure ℝ) [IsProbabilityMeasure μG]
    (x m : Fin T → ℝ) (hx : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1) (hgood : Good T μG x m)
    (t : Fin T) (ht : 1 ≤ t.val) :
    oracle μG (x t) - expReward μG (x t) (algBid T T (cT T) (vqOf T x) (extV m) t) ≤
      2 / T + 4 * wd (cT T) (Ncnt T x t) := by
  have hK : 1 ≤ T := by omega
  have hc0 : 0 ≤ cT T := by have := cT_ge_one hT; linarith
  set e := ep t - 1 with he
  have hep : ep t = e + 1 := by have := ep_pos ht; omega
  have hle := ep_le t
  rw [hep] at hle
  have hGE : ∀ e' ≤ e, GoodE T (cT T) (cdf μG) (vqOf T x) (extV m) e' := by
    intro e' he' r hr j hj
    have hre : ep r = e' := ep_of_mem hr
    have hrlt : r < 2 ^ (e' + 1) - 1 := epoch_lt hr
    have h2 : 2 ^ (e' + 1) ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 := hgood r (by have := t.isLt; omega) (by rw [hre]; have := t.isLt; omega) j hj
    rw [hre] at h3
    exact h3
  have hinv := theta_le_Jst (K := T) (M := T) (c := cT T) (vq := vqOf T x) (m := extV m) hK
    (cdf_mono μG) (cdf_nonneg μG) (cdf_le_one μG) e (fun e' he' => hGE e' (by omega))
  have hvqt : vqOf T x t = qv T (x t) := by
    simp [vqOf, extV, t.isLt]
  have hi : vqOf T x t < T := by rw [hvqt]; exact qv_lt hK _
  have hstep := step_regret hK hc0 (cdf_mono μG) (cdf_nonneg μG) (cdf_le_one μG)
    (hGE e le_rfl) hinv hi
  have hround := round_regret_le hK hK μG (hx t).1 (hx t).2
    (theta T T (cT T) (vqOf T x) (extV m) (e + 1) (vqOf T x t))
  rw [← hvqt] at hround
  unfold algBid
  rw [hep]
  unfold Ncnt
  rw [← he]
  have : (1 : ℝ) / T + 1 / T = 2 / T := by ring
  linarith

/-- the pointwise bound on the regret. -/
theorem total_bound {T : ℕ} (hT : 2 ≤ T) (μG : Measure ℝ) [IsProbabilityMeasure μG]
    (p : (Fin T → ℝ) × (Fin T → ℝ)) (hx : ∀ t, p.1 t ∈ Set.Icc (0 : ℝ) 1) :
    Rg T μG p ≤ 4 + 4 * Real.sqrt (cT T) *
        ∑ t : Fin T, (if 1 ≤ t.val then hf (Ncnt T p.1 t) else 0) +
      2 * T * (Sbad T μG).indicator (fun _ => (1 : ℝ)) p := by
  have hK : 1 ≤ T := by omega
  have hc := cT_ge_one hT
  have hsq : 0 ≤ Real.sqrt (cT T) := Real.sqrt_nonneg _
  have hbmem : ∀ t : Fin T, algBid T T (cT T) (vqOf T p.1) (extV p.2) t ∈ Set.Icc (0 : ℝ) 1 :=
    fun t => ⟨(gb_pos hK _).le, gb_le_one hK _⟩
  have hsum_nonneg : 0 ≤ ∑ t : Fin T, (if 1 ≤ t.val then hf (Ncnt T p.1 t) else 0) := by
    apply Finset.sum_nonneg; intro t _; split_ifs
    · exact hf_nonneg _
    · exact le_refl _
  unfold Rg regret
  by_cases hbad : p ∈ Sbad T μG
  · rw [Set.indicator_of_mem hbad]
    have : ∑ t : Fin T, (oracle μG (p.1 t) -
        expReward μG (p.1 t) (algBid T T (cT T) (vqOf T p.1) (extV p.2) t)) ≤
        ∑ _t : Fin T, (2 : ℝ) :=
      Finset.sum_le_sum (fun t _ => (round_bounds μG (hx t) (hbmem t)).2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    nlinarith
  · rw [Set.indicator_of_notMem hbad]
    have hgood := good_of_not_bad hbad
    have hterm : ∀ t : Fin T, oracle μG (p.1 t) -
        expReward μG (p.1 t) (algBid T T (cT T) (vqOf T p.1) (extV p.2) t) ≤
        2 / T + (if t.val = 0 then (2 : ℝ) else 0) +
          4 * Real.sqrt (cT T) * (if 1 ≤ t.val then hf (Ncnt T p.1 t) else 0) := by
      intro t
      have hb := round_bounds μG (hx t) (hbmem t)
      by_cases ht : 1 ≤ t.val
      · rw [if_neg (by omega), if_pos ht]
        have := round_good hT μG p.1 p.2 hx hgood t ht
        have := wd_le_hf hc (Ncnt T p.1 t)
        have : (0 : ℝ) ≤ 2 / T := by positivity
        nlinarith
      · rw [if_pos (by omega), if_neg ht]
        have : (0 : ℝ) ≤ 2 / T := by positivity
        linarith [hb.2]
    have hs := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hterm t)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    have h1 : ∑ _t : Fin T, (2 : ℝ) / T = 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have h2 : ∑ t : Fin T, (if t.val = 0 then (2 : ℝ) else 0) ≤ 2 := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have : (Finset.univ.filter (fun t : Fin T => t.val = 0)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        simp only [Finset.mem_filter] at ha hb
        exact Fin.ext (by omega)
      have : ((Finset.univ.filter (fun t : Fin T => t.val = 0)).card : ℝ) ≤ 1 := by
        exact_mod_cast this
      linarith
    linarith

end FPA1

-- ===== part Fin =====

open MeasureTheory
open scoped Classical
open FirstPriceLearning.Stochastic

namespace FPA1

section Final

variable {T : ℕ}

lemma meas_vq2 (s : ℕ) : Measurable fun p : (Fin T → ℝ) × (Fin T → ℝ) => vqOf T p.1 s :=
  (measurable_qv T).comp ((measurable_extV s).comp measurable_fst)

lemma meas_y2 (s : ℕ) : Measurable fun p : (Fin T → ℝ) × (Fin T → ℝ) => extV p.2 s :=
  (measurable_extV s).comp measurable_snd

lemma meas_Rg (μG : Measure ℝ) [IsProbabilityMeasure μG] : Measurable (Rg T μG) := by
  unfold Rg regret
  apply Finset.measurable_sum
  intro t _
  have hv : Measurable fun p : (Fin T → ℝ) × (Fin T → ℝ) => p.1 t :=
    (measurable_pi_apply t).comp measurable_fst
  have hb := meas_algBid (K := T) (M := T) (c := cT T) (meas_vq2 (T := T)) (meas_y2 (T := T)) t
  apply ((measurable_oracle μG).comp hv).sub
  unfold expReward
  exact (hv.sub hb).mul ((measurable_cdf μG).comp hb)

lemma meas_Ncnt (t : ℕ) : Measurable fun x : Fin T → ℝ => Ncnt T x t := by
  unfold Ncnt
  apply meas_card_filter
  intro s
  exact measurableSet_le ((measurable_qv T).comp (measurable_extV s))
    ((measurable_qv T).comp (measurable_extV t))

lemma meas_Bset (μG : Measure ℝ) (r j : ℕ) : MeasurableSet (Bset T μG r j) := by
  unfold Bset
  have hcard : Measurable fun p : (Fin T → ℝ) × (Fin T → ℝ) =>
      (dset (ep r) (vqOf T p.1) r).card := by
    unfold dset
    apply meas_card_filter
    intro s
    exact measurableSet_le (meas_vq2 s) (meas_vq2 r)
  have hnum : Measurable fun p : (Fin T → ℝ) × (Fin T → ℝ) =>
      ((dset (ep r) (vqOf T p.1) r).filter (fun s => extV p.2 s ≤ gb T j)).card := by
    unfold dset
    simp_rw [Finset.filter_filter]
    apply meas_card_filter
    intro s
    exact (measurableSet_le (meas_vq2 s) (meas_vq2 r)).inter
      (measurableSet_le (meas_y2 s) measurable_const)
  apply measurableSet_lt ((measurable_of_countable (wd (cT T))).comp hcard)
  unfold ghat
  apply Measurable.abs
  apply Measurable.sub_const
  exact ((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp hnum).div
    ((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp hcard)

lemma meas_Sbad (μG : Measure ℝ) : MeasurableSet (Sbad T μG) := by
  unfold Sbad
  refine Finset.measurableSet_biUnion _ (fun r _ => ?_)
  exact Finset.measurableSet_biUnion _ (fun j _ => meas_Bset μG r j)

lemma bset_prob (F μG : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure μG]
    (hT : 2 ≤ T) (r j : ℕ) (hr : r < T) (hc : 2 ^ (ep r + 1) - 1 ≤ T) :
    ((Measure.pi fun _ : Fin T => F).prod (Measure.pi fun _ : Fin T => μG)) (Bset T μG r j) ≤
      ENNReal.ofReal (2 * Real.exp (-2 * cT T)) := by
  rw [Measure.prod_apply (meas_Bset μG r j)]
  calc ∫⁻ x, (Measure.pi fun _ : Fin T => μG) (Prod.mk x ⁻¹' Bset T μG r j)
        ∂(Measure.pi fun _ : Fin T => F)
      ≤ ∫⁻ _x, ENNReal.ofReal (2 * Real.exp (-2 * cT T)) ∂(Measure.pi fun _ : Fin T => F) := by
        apply lintegral_mono
        intro x
        have hD : ∀ s ∈ dset (ep r) (vqOf T x) r, s < T := by
          intro s hs
          have := epoch_lt (Finset.mem_filter.mp hs).1
          omega
        have hne : (dset (ep r) (vqOf T x) r).Nonempty :=
          ⟨r, Finset.mem_filter.mpr ⟨mem_epoch_ep r, le_refl _⟩⟩
        have hc0 : 0 ≤ cT T := by have := cT_ge_one hT; linarith
        exact bad_slice μG (dset (ep r) (vqOf T x) r) hD hne (gb T j) hc0
    _ = ENNReal.ofReal (2 * Real.exp (-2 * cT T)) := by simp

lemma ae_mem_Icc (F μG : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure μG]
    (hF : F (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    ∀ᵐ p ∂((Measure.pi fun _ : Fin T => F).prod (Measure.pi fun _ : Fin T => μG)),
      ∀ t, p.1 t ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro t
  rw [ae_iff]
  have : {p : (Fin T → ℝ) × (Fin T → ℝ) | ¬ p.1 t ∈ Set.Icc (0 : ℝ) 1} =
      (Function.eval t ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ) ×ˢ Set.univ := by
    ext p; simp
  rw [this, Measure.prod_prod]
  have hmp := measurePreserving_eval (fun _ : Fin T => F) t
  rw [hmp.measure_preimage (measurableSet_Icc.compl.nullMeasurableSet), hF, zero_mul]

end Final

end FPA1

-- ===== part Goal =====

open MeasureTheory
open scoped Classical
open FirstPriceLearning.Stochastic

namespace FPA1

lemma hf_avg_bound (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), hf k) / ((n : ℝ) + 1) ≤ 2 * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1) := by
  have h := sum_hf_le (n + 1)
  push_cast at h
  have hpos : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hsq : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
  rw [div_le_div_iff₀ (by positivity) hpos]
  calc (∑ k ∈ Finset.range (n + 1), hf k) * Real.sqrt ((n : ℝ) + 1)
      ≤ (2 * Real.sqrt 2 * Real.sqrt ((n : ℝ) + 1)) * Real.sqrt ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right h hpos.le
    _ = 2 * Real.sqrt 2 * ((n : ℝ) + 1) := by rw [mul_assoc, ← sq, hsq]

lemma rank_round {T : ℕ} (F : Measure ℝ) [IsProbabilityMeasure F] (t : ℕ) (htT : t < T)
    (ht : 1 ≤ t) :
    ∫ x, hf (Ncnt T x t) ∂(Measure.pi fun _ : Fin T => F) ≤
      4 * Real.sqrt 2 / Real.sqrt ((t : ℝ) + 1) := by
  set E := epoch (ep t - 1)
  have hep := ep_pos ht
  have hle := ep_le t
  have hlt := lt_pow_ep t
  have hE : ∀ s ∈ E, s < T := by
    intro s hs
    have := epoch_lt hs
    rw [show ep t - 1 + 1 = ep t by omega] at this
    omega
  have htE : t ∉ E := by
    intro hs
    have := epoch_lt hs
    rw [show ep t - 1 + 1 = ep t by omega] at this
    omega
  have h1 := rank_exp F (qv T) (measurable_qv T) E hE t htT htE
  have h2 := hf_avg_bound E.card
  have hcard : E.card = 2 ^ (ep t - 1) := card_epoch _
  -- t + 1 < 4 (|E| + 1)
  have h4 : (t : ℝ) + 1 ≤ 4 * ((E.card : ℝ) + 1) := by
    have : 2 ^ (ep t + 1) = 4 * 2 ^ (ep t - 1) := by
      rw [show ep t + 1 = (ep t - 1) + 2 by omega, pow_add]; ring
    have : t + 1 ≤ 4 * (E.card + 1) := by rw [hcard]; omega
    exact_mod_cast this
  have hsq : Real.sqrt ((t : ℝ) + 1) ≤ 2 * Real.sqrt ((E.card : ℝ) + 1) := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)], ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt h4
  have hp1 : 0 < Real.sqrt ((t : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hp2 : 0 < Real.sqrt ((E.card : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have h5 : 2 * Real.sqrt 2 / Real.sqrt ((E.card : ℝ) + 1) ≤
      4 * Real.sqrt 2 / Real.sqrt ((t : ℝ) + 1) := by
    rw [div_le_div_iff₀ hp2 hp1]
    have := Real.sqrt_nonneg 2
    nlinarith
  calc ∫ x, hf (Ncnt T x t) ∂(Measure.pi fun _ : Fin T => F)
      = ∫ x, hf ((E.filter (fun s => qv T (extV x s) ≤ qv T (extV x t))).card)
          ∂(Measure.pi fun _ : Fin T => F) := rfl
    _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := h5

lemma exp_cT {T : ℕ} (hT : 2 ≤ T) : Real.exp (-2 * cT T) * (T : ℝ) ^ 4 = 1 := by
  unfold cT
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  rw [show -2 * (2 * Real.log T) = -(4 * Real.log T) by ring, Real.exp_neg,
    show (4 : ℝ) * Real.log T = ((4 : ℕ) : ℝ) * Real.log T by norm_num, Real.exp_nat_mul,
    Real.exp_log hTpos]
  field_simp

theorem expected_bound {T : ℕ} (hT : 2 ≤ T) (F μG : Measure ℝ) [IsProbabilityMeasure F]
    [IsProbabilityMeasure μG] (hF : F (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    Integrable (Rg T μG) ((Measure.pi fun _ : Fin T => F).prod (Measure.pi fun _ : Fin T => μG)) ∧
      ∫ p, Rg T μG p ∂((Measure.pi fun _ : Fin T => F).prod (Measure.pi fun _ : Fin T => μG)) ≤
        6 + 64 * Real.sqrt (Real.log T) * Real.sqrt T := by
  set μ2 := (Measure.pi fun _ : Fin T => F).prod (Measure.pi fun _ : Fin T => μG) with hμ2
  have hK : 1 ≤ T := by omega
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hae := ae_mem_Icc (T := T) F μG hF
  have hRint : Integrable (Rg T μG) μ2 := by
    apply Integrable.of_bound (meas_Rg μG).aestronglyMeasurable (2 * T)
    filter_upwards [hae] with p hp
    unfold Rg regret
    have hb : ∀ t : Fin T, algBid T T (cT T) (vqOf T p.1) (extV p.2) t ∈ Set.Icc (0 : ℝ) 1 :=
      fun t => ⟨(gb_pos hK _).le, gb_le_one hK _⟩
    have h0 : 0 ≤ ∑ t : Fin T, (oracle μG (p.1 t) -
        expReward μG (p.1 t) (algBid T T (cT T) (vqOf T p.1) (extV p.2) t)) :=
      Finset.sum_nonneg (fun t _ => (round_bounds μG (hp t) (hb t)).1)
    have h2 : ∑ t : Fin T, (oracle μG (p.1 t) -
        expReward μG (p.1 t) (algBid T T (cT T) (vqOf T p.1) (extV p.2) t)) ≤
        ∑ _t : Fin T, (2 : ℝ) :=
      Finset.sum_le_sum (fun t _ => (round_bounds μG (hp t) (hb t)).2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    linarith
  refine ⟨hRint, ?_⟩
  -- the bounding function
  set f : Fin T → (Fin T → ℝ) × (Fin T → ℝ) → ℝ :=
    fun t p => if 1 ≤ t.val then hf (Ncnt T p.1 t) else 0 with hfdef
  have hfint : ∀ t, Integrable (f t) μ2 := by
    intro t
    apply Integrable.of_bound (C := Real.sqrt 2)
    · apply Measurable.aestronglyMeasurable
      by_cases ht : 1 ≤ t.val
      · simp only [hfdef, if_pos ht]
        exact (measurable_of_countable hf).comp ((meas_Ncnt (T := T) t).comp measurable_fst)
      · simp only [hfdef, if_neg ht]; exact measurable_const
    · apply Filter.Eventually.of_forall
      intro p
      simp only [hfdef]
      split_ifs
      · rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg _)]; exact hf_le _
      · simp
  have hfsum : Integrable (fun p => ∑ t : Fin T, f t p) μ2 :=
    integrable_finsetSum _ (fun t _ => hfint t)
  have hind : Integrable ((Sbad T μG).indicator (fun _ => (1 : ℝ))) μ2 :=
    (integrable_const (1 : ℝ)).indicator (meas_Sbad μG)
  have hbound : ∫ p, Rg T μG p ∂μ2 ≤
      ∫ p, (4 + 4 * Real.sqrt (cT T) * ∑ t : Fin T, f t p +
        2 * T * (Sbad T μG).indicator (fun _ => (1 : ℝ)) p) ∂μ2 := by
    apply integral_mono_ae hRint
    · exact ((integrable_const _).add (hfsum.const_mul _)).add (hind.const_mul _)
    · filter_upwards [hae] with p hp
      exact total_bound hT μG p hp
  have hA : Integrable (fun p => 4 + 4 * Real.sqrt (cT T) * ∑ t : Fin T, f t p) μ2 :=
    (integrable_const _).add (hfsum.const_mul _)
  have e1 : ∫ p, (4 + 4 * Real.sqrt (cT T) * ∑ t : Fin T, f t p +
      2 * T * (Sbad T μG).indicator (fun _ => (1 : ℝ)) p) ∂μ2 =
      (∫ p, (4 + 4 * Real.sqrt (cT T) * ∑ t : Fin T, f t p) ∂μ2) +
        ∫ p, 2 * T * (Sbad T μG).indicator (fun _ => (1 : ℝ)) p ∂μ2 :=
    integral_add hA (hind.const_mul _)
  have e2 : ∫ p, (4 + 4 * Real.sqrt (cT T) * ∑ t : Fin T, f t p) ∂μ2 =
      (∫ _p, (4 : ℝ) ∂μ2) + ∫ p, 4 * Real.sqrt (cT T) * ∑ t : Fin T, f t p ∂μ2 :=
    integral_add (integrable_const _) (hfsum.const_mul _)
  have e3 : ∫ p, 4 * Real.sqrt (cT T) * ∑ t : Fin T, f t p ∂μ2 =
      4 * Real.sqrt (cT T) * ∑ t : Fin T, ∫ p, f t p ∂μ2 := by
    rw [integral_const_mul, integral_finsetSum _ (fun t _ => hfint t)]
  have e4 : ∫ p, 2 * T * (Sbad T μG).indicator (fun _ => (1 : ℝ)) p ∂μ2 =
      2 * T * μ2.real (Sbad T μG) := by
    rw [integral_const_mul, integral_indicator_const _ (meas_Sbad μG)]; simp
  have e5 : ∫ _p, (4 : ℝ) ∂μ2 = 4 := by simp
  rw [e1, e2, e3, e4, e5] at hbound
  -- the rank terms
  have hrank : ∑ t : Fin T, ∫ p, f t p ∂μ2 ≤ 8 * Real.sqrt 2 * Real.sqrt T := by
    have hterm : ∀ t : Fin T, ∫ p, f t p ∂μ2 ≤ 4 * Real.sqrt 2 * (1 / Real.sqrt ((t : ℝ) + 1)) := by
      intro t
      by_cases ht : 1 ≤ t.val
      · simp only [hfdef, if_pos ht]
        rw [hμ2, integral_fun_fst (fun x => hf (Ncnt T x t))]
        simp only [probReal_univ, one_smul]
        have := rank_round F t.val t.isLt ht
        rw [mul_one_div]; exact this
      · simp only [hfdef, if_neg ht, integral_zero]
        positivity
    calc ∑ t : Fin T, ∫ p, f t p ∂μ2
        ≤ ∑ t : Fin T, 4 * Real.sqrt 2 * (1 / Real.sqrt ((t : ℝ) + 1)) :=
          Finset.sum_le_sum (fun t _ => hterm t)
      _ = 4 * Real.sqrt 2 * ∑ t ∈ Finset.range T, 1 / Real.sqrt ((t : ℝ) + 1) := by
          rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun t => 1 / Real.sqrt ((t : ℝ) + 1))]
      _ ≤ 4 * Real.sqrt 2 * (2 * Real.sqrt T) := by
          apply mul_le_mul_of_nonneg_left (sum_inv_sqrt_le T) (by positivity)
      _ = 8 * Real.sqrt 2 * Real.sqrt T := by ring
  -- the bad event
  have hbad : μ2.real (Sbad T μG) ≤ (T : ℝ) * T * (2 * Real.exp (-2 * cT T)) := by
    unfold Sbad
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    calc ∑ r ∈ (Finset.range T).filter (fun r => 2 ^ (ep r + 1) - 1 ≤ T),
          μ2.real (⋃ j ∈ Finset.range T, Bset T μG r j)
        ≤ ∑ r ∈ (Finset.range T).filter (fun r => 2 ^ (ep r + 1) - 1 ≤ T),
            (T : ℝ) * (2 * Real.exp (-2 * cT T)) := by
          apply Finset.sum_le_sum
          intro r hr
          obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp hr
          refine (measureReal_biUnion_finset_le _ _).trans ?_
          calc ∑ j ∈ Finset.range T, μ2.real (Bset T μG r j)
              ≤ ∑ _j ∈ Finset.range T, 2 * Real.exp (-2 * cT T) := by
                apply Finset.sum_le_sum
                intro j _
                exact ENNReal.toReal_le_of_le_ofReal (by positivity)
                  (bset_prob F μG hT r j (Finset.mem_range.mp hr1) hr2)
            _ = (T : ℝ) * (2 * Real.exp (-2 * cT T)) := by simp
      _ ≤ ∑ _r ∈ Finset.range T, (T : ℝ) * (2 * Real.exp (-2 * cT T)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
      _ = (T : ℝ) * T * (2 * Real.exp (-2 * cT T)) := by simp; ring
  have hexp := exp_cT hT
  have hbad2 : 2 * T * μ2.real (Sbad T μG) ≤ 2 := by
    have h1 : 2 * (T : ℝ) * μ2.real (Sbad T μG) ≤ 2 * T * ((T : ℝ) * T * (2 * Real.exp (-2 * cT T))) :=
      mul_le_mul_of_nonneg_left hbad (by positivity)
    have h2 : 2 * (T : ℝ) * ((T : ℝ) * T * (2 * Real.exp (-2 * cT T))) = 4 / T := by
      rw [eq_div_iff hTpos.ne']
      have : 2 * (T : ℝ) * ((T : ℝ) * T * (2 * Real.exp (-2 * cT T))) * T =
          4 * (Real.exp (-2 * cT T) * (T : ℝ) ^ 4) := by ring
      rw [this, hexp]; ring
    have h3 : (4 : ℝ) / T ≤ 2 := by
      rw [div_le_iff₀ hTpos]
      have : (2 : ℝ) ≤ T := by exact_mod_cast hT
      linarith
    linarith
  have hc : Real.sqrt (cT T) = Real.sqrt 2 * Real.sqrt (Real.log T) := by
    unfold cT; rw [Real.sqrt_mul (by norm_num)]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hcnn : 0 ≤ Real.sqrt (cT T) := Real.sqrt_nonneg _
  have hmain : 4 * Real.sqrt (cT T) * ∑ t : Fin T, ∫ p, f t p ∂μ2 ≤
      64 * Real.sqrt (Real.log T) * Real.sqrt T := by
    calc 4 * Real.sqrt (cT T) * ∑ t : Fin T, ∫ p, f t p ∂μ2
        ≤ 4 * Real.sqrt (cT T) * (8 * Real.sqrt 2 * Real.sqrt T) :=
          mul_le_mul_of_nonneg_left hrank (by positivity)
      _ = 32 * (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt (Real.log T) * Real.sqrt T := by
          rw [hc]; ring
      _ = 64 * Real.sqrt (Real.log T) * Real.sqrt T := by rw [hs2]; ring
  linarith

end FPA1

open FPA1 in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 2 ≤ T → ∃ π : FirstPriceLearning.Stochastic.Policy T,
      ∀ (F μG : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure μG],
        F (Set.Icc (0 : ℝ) 1)ᶜ = 0 → μG (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
        Integrable (π.regretOf μG) (π.jointLaw F μG) ∧
          π.expectedRegret F μG ≤ C * Real.sqrt T * Real.log T ^ ((5 : ℝ) / 2) := by
  refine ⟨300, by norm_num, fun T hT => ⟨pol T, fun F μG _ _ hF _ => ?_⟩⟩
  obtain ⟨hint, hbd⟩ := expected_bound hT F μG hF
  set μ2 := (Measure.pi fun _ : Fin T => F).prod (Measure.pi fun _ : Fin T => μG)
  have hjoint : (pol T).jointLaw F μG = Measure.map (Prod.mk ()) μ2 := by
    unfold FirstPriceLearning.Stochastic.Policy.jointLaw
    exact Measure.dirac_prod ()
  have hreg : (pol T).regretOf μG = fun ω => Rg T μG ω.2 := by
    funext ω
    obtain ⟨u, v, m⟩ := ω
    unfold FirstPriceLearning.Stochastic.Policy.regretOf Rg
    simp only
    congr 1
    funext t
    exact pol_bids v m t
  have hemb := measurableEmbedding_prodMk_left (β := (Fin T → ℝ) × (Fin T → ℝ)) ()
  constructor
  · rw [hjoint, hreg]
    change Integrable (fun ω : Unit × (Fin T → ℝ) × (Fin T → ℝ) => Rg T μG ω.2)
      (Measure.map (Prod.mk ()) μ2)
    rw [hemb.integrable_map_iff]
    exact hint
  · unfold FirstPriceLearning.Stochastic.Policy.expectedRegret
    rw [hjoint, hreg]
    change ∫ ω : Unit × (Fin T → ℝ) × (Fin T → ℝ), Rg T μG ω.2 ∂(Measure.map (Prod.mk ()) μ2) ≤ _
    rw [hemb.integral_map]
    refine hbd.trans ?_
    -- numerics
    have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast hT
    have hL : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT2
    have hl2 := Real.log_two_gt_d9
    set L := Real.log T with hLdef
    have hLpos : 0.69 ≤ L := by linarith
    have hsT : 1 ≤ Real.sqrt T := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
    have hsL2 : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (by linarith)
    have hpow : L ^ ((5 : ℝ) / 2) = L ^ 2 * Real.sqrt L := by
      rw [Real.sqrt_eq_rpow, show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num,
        Real.rpow_add (by linarith), Real.rpow_two]
    rw [hpow]
    -- sqrt L ≥ 0.8
    have hsL8 : 0.8 ≤ Real.sqrt L := by
      rw [show (0.8 : ℝ) = Real.sqrt (0.8 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hL2 : 0.47 ≤ L ^ 2 := by nlinarith
    have h1 : 6 ≤ 150 * Real.sqrt T * (L ^ 2 * Real.sqrt L) := by
      have : 0.37 ≤ L ^ 2 * Real.sqrt L := by nlinarith
      nlinarith
    have h2 : 64 * Real.sqrt L * Real.sqrt T ≤ 150 * Real.sqrt T * (L ^ 2 * Real.sqrt L) := by
      have : 64 ≤ 150 * L ^ 2 := by nlinarith
      have := mul_nonneg hsL (by linarith : (0 : ℝ) ≤ Real.sqrt T)
      nlinarith
    linarith

