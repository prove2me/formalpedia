-- Prove2me | solution 1 for FosterQueues.MG1.theorem4_transience_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T09:20:39.218568+00:00
-- url     : https://prove2.me/submissions/3f6e071a-3779-4b45-9e29-b33abcf46402

import Mathlib
import Definitions.Def_FosterQueues_MG1_Model

open scoped ENNReal
open QueueingFundamentals.Foundations

set_option autoImplicit false

namespace TC47

variable (P : TransitionMatrix)

lemma p_le_one (i j : ℕ) : P.p i j ≤ 1 :=
  le_hasSum (P.row_sum i) j (fun k _ => P.nonneg i k)

lemma fp_two (n i j : ℕ) : P.firstPassage (n + 2) i j =
    ∑' l, if l = j then 0 else P.p i l * P.firstPassage (n + 1) l j := rfl

lemma fp_bound : ∀ n i j, 0 ≤ P.firstPassage n i j ∧ P.firstPassage n i j ≤ 1 := by
  intro n
  induction n with
  | zero => intro i j; simp [TransitionMatrix.firstPassage]
  | succ n ih =>
    intro i j
    cases n with
    | zero => exact ⟨P.nonneg i j, p_le_one P i j⟩
    | succ m =>
      rw [fp_two]
      have h0 : ∀ l, 0 ≤ (if l = j then 0 else P.p i l * P.firstPassage (m + 1) l j) := by
        intro l; split_ifs
        · exact le_rfl
        · exact mul_nonneg (P.nonneg i l) (ih l j).1
      have h1 : ∀ l, (if l = j then 0 else P.p i l * P.firstPassage (m + 1) l j) ≤ P.p i l := by
        intro l; split_ifs
        · exact P.nonneg i l
        · exact mul_le_of_le_one_right (P.nonneg i l) (ih l j).2
      have hs := Summable.of_nonneg_of_le h0 h1 (P.row_sum i).summable
      refine ⟨tsum_nonneg h0, ?_⟩
      calc _ ≤ ∑' l, P.p i l := hs.tsum_le_tsum h1 (P.row_sum i).summable
        _ = 1 := (P.row_sum i).tsum_eq

lemma fp_two_enn (n i j : ℕ) : ENNReal.ofReal (P.firstPassage (n + 2) i j) =
    ∑' l, if l = j then 0 else
      ENNReal.ofReal (P.p i l) * ENNReal.ofReal (P.firstPassage (n + 1) l j) := by
  have h0 : ∀ l, 0 ≤ (if l = j then 0 else P.p i l * P.firstPassage (n + 1) l j) := by
    intro l; split_ifs
    · exact le_rfl
    · exact mul_nonneg (P.nonneg i l) (fp_bound P (n + 1) l j).1
  have h1 : ∀ l, (if l = j then 0 else P.p i l * P.firstPassage (n + 1) l j) ≤ P.p i l := by
    intro l; split_ifs
    · exact P.nonneg i l
    · exact mul_le_of_le_one_right (P.nonneg i l) (fp_bound P (n + 1) l j).2
  have hs := Summable.of_nonneg_of_le h0 h1 (P.row_sum i).summable
  rw [fp_two, ENNReal.ofReal_tsum_of_nonneg h0 hs]
  congr 1; funext l
  split_ifs
  · simp
  · rw [ENNReal.ofReal_mul (P.nonneg _ _)]

lemma row_enn (i : ℕ) : ∑' l, ENNReal.ofReal (P.p i l) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (P.nonneg i) (P.row_sum i).summable,
    (P.row_sum i).tsum_eq, ENNReal.ofReal_one]

lemma split_j (i j : ℕ) (g : ℕ → ℝ≥0∞) :
    ENNReal.ofReal (P.p i j) + ∑' l, (if l = j then 0 else ENNReal.ofReal (P.p i l) * g l) =
      ∑' l, ENNReal.ofReal (P.p i l) * (if l = j then 1 else g l) := by
  have h : ∀ l, ENNReal.ofReal (P.p i l) * (if l = j then 1 else g l) =
      (if l = j then ENNReal.ofReal (P.p i j) else 0) +
        (if l = j then 0 else ENNReal.ofReal (P.p i l) * g l) := by
    intro l; split_ifs with hl
    · subst hl; simp
    · simp
  simp_rw [h]
  rw [ENNReal.tsum_add, tsum_ite_eq]

noncomputable def FF (i j : ℕ) : ℝ≥0∞ := ∑' n, ENNReal.ofReal (P.firstPassage n i j)

lemma FF_shift (l j : ℕ) : FF P l j = ∑' n, ENNReal.ofReal (P.firstPassage (n + 1) l j) := by
  unfold FF
  rw [tsum_eq_zero_add' ENNReal.summable]
  have h0 : P.firstPassage 0 l j = 0 := rfl
  rw [h0, ENNReal.ofReal_zero, zero_add]

lemma G_le (j : ℕ) (N : ℕ) :
    ∀ i, ∑ n ∈ Finset.range N, ENNReal.ofReal (P.firstPassage (n + 1) i j) ≤ 1 := by
  induction N with
  | zero => intro i; simp
  | succ N ih =>
    intro i
    rw [Finset.sum_range_succ']
    have e : ∀ n : ℕ, ENNReal.ofReal (P.firstPassage (n + 1 + 1) i j) =
        ∑' l, if l = j then 0 else
          ENNReal.ofReal (P.p i l) * ENNReal.ofReal (P.firstPassage (n + 1) l j) :=
      fun n => fp_two_enn P n i j
    simp only [e]
    have e1 : P.firstPassage (0 + 1) i j = P.p i j := rfl
    rw [e1, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    have e2 : ∀ l, ∑ n ∈ Finset.range N, (if l = j then (0 : ℝ≥0∞) else
        ENNReal.ofReal (P.p i l) * ENNReal.ofReal (P.firstPassage (n + 1) l j)) =
        if l = j then 0 else ENNReal.ofReal (P.p i l) *
          ∑ n ∈ Finset.range N, ENNReal.ofReal (P.firstPassage (n + 1) l j) := by
      intro l; split_ifs <;> simp [Finset.mul_sum]
    simp only [e2]
    rw [add_comm, split_j]
    calc _ ≤ ∑' l, ENNReal.ofReal (P.p i l) * 1 := by
          gcongr with l
          split_ifs
          · exact le_rfl
          · exact ih l
      _ = 1 := by simp only [mul_one]; exact row_enn P i

lemma FF_le_one (i j : ℕ) : FF P i j ≤ 1 := by
  rw [FF_shift, ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun N => G_le P j N i

noncomputable def CC (j l : ℕ) : ℝ≥0∞ := if l = j then 1 else FF P l j

lemma CC_le (j l : ℕ) : CC P j l ≤ 1 := by
  unfold CC; split_ifs
  · exact le_rfl
  · exact FF_le_one P l j

lemma FF_rec (i j : ℕ) : FF P i j = ∑' l, ENNReal.ofReal (P.p i l) * CC P j l := by
  have hsplit : FF P i j = ENNReal.ofReal (P.firstPassage 1 i j) +
      ∑' n, ENNReal.ofReal (P.firstPassage (n + 2) i j) := by
    rw [FF_shift, tsum_eq_zero_add' ENNReal.summable]
  unfold CC
  rw [hsplit, ← split_j]
  have e1 : P.firstPassage 1 i j = P.p i j := rfl
  rw [e1]
  congr 1
  simp_rw [fp_two_enn]
  rw [ENNReal.tsum_comm]
  congr 1; funext l
  split_ifs with h
  · simp
  · rw [ENNReal.tsum_mul_left, FF_shift]

lemma real_rec (i j : ℕ) :
    (FF P i j).toReal = ∑' l, P.p i l * (CC P j l).toReal := by
  rw [FF_rec, ENNReal.tsum_toReal_eq]
  · congr 1; funext l
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (P.nonneg i l)]
  · intro l
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top (CC_le P j l))

lemma eq_of_avg (i : ℕ) (w : ℕ → ℝ) (m : ℝ) (hs : Summable (fun l => P.p i l * w l))
    (hle : ∀ l, w l ≤ m) (hge : m ≤ ∑' l, P.p i l * w l) (l : ℕ) (hl : 0 < P.p i l) :
    w l = m := by
  by_contra hne
  have hlt : w l < m := lt_of_le_of_ne (hle l) hne
  have hg : HasSum (fun t => P.p i t * (m - w t)) (1 * m - ∑' t, P.p i t * w t) := by
    have := ((P.row_sum i).mul_right m).sub hs.hasSum
    convert this using 1
    all_goals first | rfl | (funext t; ring)
  have hpos : 0 < ∑' t, P.p i t * (m - w t) :=
    hg.summable.tsum_pos (fun t => mul_nonneg (P.nonneg i t) (by linarith [hle t])) l
      (mul_pos hl (by linarith))
  rw [hg.tsum_eq] at hpos
  linarith

lemma propagate (Q : ℕ → Prop) (hQ : ∀ i l, Q i → 0 < P.p i l → Q l) :
    ∀ n i j, Q i → 0 < P.stepProb n i j → Q j := by
  intro n
  induction n with
  | zero =>
    intro i j hi hs
    change 0 < (if i = j then (1 : ℝ) else 0) at hs
    split_ifs at hs with h
    · subst h; exact hi
    · exact absurd hs (lt_irrefl 0)
  | succ n ih =>
    intro i j hi hs
    change 0 < ∑' k, P.p i k * P.stepProb n k j at hs
    obtain ⟨k, hk⟩ : ∃ k, 0 < P.p i k * P.stepProb n k j := by
      by_contra hc
      push Not at hc
      exact absurd (tsum_nonpos hc) (not_le.2 hs)
    have hboth := (pos_and_pos_or_neg_and_neg_of_mul_pos hk).resolve_right
      (fun h => absurd h.1 (not_lt.2 (P.nonneg i k)))
    exact ih k j (hQ i k hi hboth.1) hboth.2


lemma G_succ (i j N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), ENNReal.ofReal (P.firstPassage (n + 1) i j) =
      ∑' l, ENNReal.ofReal (P.p i l) * (if l = j then 1 else
        ∑ n ∈ Finset.range N, ENNReal.ofReal (P.firstPassage (n + 1) l j)) := by
  rw [Finset.sum_range_succ']
  have e : ∀ n : ℕ, ENNReal.ofReal (P.firstPassage (n + 1 + 1) i j) =
      ∑' l, if l = j then 0 else
        ENNReal.ofReal (P.p i l) * ENNReal.ofReal (P.firstPassage (n + 1) l j) :=
    fun n => fp_two_enn P n i j
  simp only [e]
  have e1 : P.firstPassage (0 + 1) i j = P.p i j := rfl
  rw [e1, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  have e2 : ∀ l, ∑ n ∈ Finset.range N, (if l = j then (0 : ℝ≥0∞) else
      ENNReal.ofReal (P.p i l) * ENNReal.ofReal (P.firstPassage (n + 1) l j)) =
      if l = j then 0 else ENNReal.ofReal (P.p i l) *
        ∑ n ∈ Finset.range N, ENNReal.ofReal (P.firstPassage (n + 1) l j) := by
    intro l; split_ifs <;> simp [Finset.mul_sum]
  simp only [e2]
  rw [add_comm, split_j]

lemma summ_bdd (u : ℕ → ℝ) (C : ℝ) (hC : ∀ l, |u l| ≤ C) (i : ℕ) :
    Summable (fun l => P.p i l * u l) := by
  refine Summable.of_norm_bounded ((P.row_sum i).summable.mul_left C) (fun l => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (P.nonneg i l)]
  have := mul_le_mul_of_nonneg_left (hC l) (P.nonneg i l)
  linarith

/-- Dirichlet bound: a `[0,1]`-valued function vanishing at `j` and subharmonic off `j`
is at most the probability of never reaching `j`. -/
lemma dir (j : ℕ) (s : ℕ → ℝ) (h0 : ∀ l, 0 ≤ s l) (h1 : ∀ l, s l ≤ 1) (hj : s j = 0)
    (hsub : ∀ i, i ≠ j → s i ≤ ∑' l, P.p i l * s l) (i : ℕ) :
    ENNReal.ofReal (s i) + FF P i j ≤ 1 := by
  have key : ∀ N i, ENNReal.ofReal (s i) +
      ∑ n ∈ Finset.range N, ENNReal.ofReal (P.firstPassage (n + 1) i j) ≤ 1 := by
    intro N
    induction N with
    | zero => intro i; simpa using h1 i
    | succ N ih =>
      intro i
      by_cases hij : i = j
      · subst hij; rw [hj, ENNReal.ofReal_zero, zero_add]; exact G_le P i (N + 1) i
      · have hsm : Summable (fun l => P.p i l * s l) :=
          summ_bdd P s 1 (fun l => by rw [abs_of_nonneg (h0 l)]; exact h1 l) i
        have hS : ENNReal.ofReal (s i) ≤ ∑' l, ENNReal.ofReal (P.p i l) * ENNReal.ofReal (s l) := by
          calc ENNReal.ofReal (s i) ≤ ENNReal.ofReal (∑' l, P.p i l * s l) :=
                ENNReal.ofReal_le_ofReal (hsub i hij)
            _ = ∑' l, ENNReal.ofReal (P.p i l * s l) :=
                ENNReal.ofReal_tsum_of_nonneg (fun l => mul_nonneg (P.nonneg i l) (h0 l)) hsm
            _ = _ := by
                congr 1; funext l; rw [ENNReal.ofReal_mul (P.nonneg i l)]
        rw [G_succ]
        calc _ ≤ (∑' l, ENNReal.ofReal (P.p i l) * ENNReal.ofReal (s l)) +
              ∑' l, ENNReal.ofReal (P.p i l) * (if l = j then 1 else
                ∑ n ∈ Finset.range N, ENNReal.ofReal (P.firstPassage (n + 1) l j)) := by
              gcongr
          _ = ∑' l, ENNReal.ofReal (P.p i l) * (ENNReal.ofReal (s l) + (if l = j then 1 else
                ∑ n ∈ Finset.range N, ENNReal.ofReal (P.firstPassage (n + 1) l j))) := by
              rw [← ENNReal.tsum_add]; congr 1; funext l; rw [mul_add]
          _ ≤ ∑' l, ENNReal.ofReal (P.p i l) * 1 := by
              gcongr with l
              split_ifs with hl
              · subst hl; rw [hj]; simp
              · exact ih l
          _ = 1 := by simp only [mul_one]; exact row_enn P i
  rw [FF_shift, ENNReal.tsum_eq_iSup_nat, ENNReal.add_iSup]
  exact iSup_le fun N => key N i

lemma hit_all (hirr : P.Irreducible) (j : ℕ) (hj : FF P j j = 1) (l : ℕ) (hl : l ≠ j) :
    FF P l j = 1 := by
  have hCt : ∀ l, CC P j l ≠ ⊤ := fun l =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (CC_le P j l)
  have hc0 : ∀ l, 0 ≤ (CC P j l).toReal := fun l => ENNReal.toReal_nonneg
  have hc1 : ∀ l, (CC P j l).toReal ≤ 1 := fun l => by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (CC_le P j l)
    simpa using this
  have hclos : ∀ i m, CC P j i = 1 → 0 < P.p i m → CC P j m = 1 := by
    intro i m hi hpm
    have hFi : FF P i j = 1 := by
      by_cases hij : i = j
      · subst hij; exact hj
      · have := hi; unfold CC at this; rwa [if_neg hij] at this
    have hr := real_rec P i j
    rw [hFi, ENNReal.toReal_one] at hr
    have hs : Summable (fun l => P.p i l * (CC P j l).toReal) :=
      summ_bdd P _ 1 (fun l => by rw [abs_of_nonneg (hc0 l)]; exact hc1 l) i
    have h : (CC P j m).toReal = 1 :=
      eq_of_avg P i (fun l => (CC P j l).toReal) 1 hs hc1 (le_of_eq hr) m hpm
    rw [← ENNReal.ofReal_toReal (hCt m), h, ENNReal.ofReal_one]
  obtain ⟨n, hn⟩ := hirr j l
  have h := propagate P (fun m => CC P j m = 1) hclos n j l (by simp [CC]) hn
  simp only [CC, if_neg hl] at h
  exact h

lemma const_of_sub (hirr : P.Irreducible) (j : ℕ) (hj : FF P j j = 1) (u : ℕ → ℝ) (C : ℝ)
    (hC : ∀ l, |u l| ≤ C) (hsub : ∀ i, u i ≤ ∑' l, P.p i l * u l) (i : ℕ) : u i = u j := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hsm := summ_bdd P u C hC
  set B : ℝ := 2 * C + 1 with hB
  have hBpos : 0 < B := by linarith
  -- every value is at most `u j`
  have hle : ∀ l, u l ≤ u j := by
    intro l
    obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, ∀ m, s m = max ((u m - u j) / B) 0 := ⟨_, fun m => rfl⟩
    have h0 : ∀ m, 0 ≤ s m := fun m => by rw [hs]; exact le_max_right _ _
    have h1 : ∀ m, s m ≤ 1 := fun m => by
      rw [hs]
      refine max_le ?_ zero_le_one
      rw [div_le_one hBpos]
      have a1 := (abs_le.1 (hC m)).2
      have a2 := (abs_le.1 (hC j)).1
      linarith
    have hj0 : s j = 0 := by rw [hs]; simp
    have hsubs : ∀ i, i ≠ j → s i ≤ ∑' m, P.p i m * s m := by
      intro i _
      have hss : Summable (fun m => P.p i m * s m) :=
        summ_bdd P s 1 (fun m => by rw [abs_of_nonneg (h0 m)]; exact h1 m) i
      rw [hs]
      refine max_le ?_ (tsum_nonneg fun m => mul_nonneg (P.nonneg i m) (h0 m))
      have hH : HasSum (fun m => P.p i m * ((u m - u j) / B))
          ((∑' m, P.p i m * u m) / B - u j / B * 1) := by
        have := ((hsm i).hasSum.div_const B).sub ((P.row_sum i).mul_left (u j / B))
        convert this using 1
        all_goals first | rfl | (funext m; ring)
      have hcmp : ∑' m, P.p i m * ((u m - u j) / B) ≤ ∑' m, P.p i m * s m :=
        hH.summable.tsum_le_tsum (fun m => mul_le_mul_of_nonneg_left
          (by rw [hs]; exact le_max_left _ _) (P.nonneg i m)) hss
      rw [hH.tsum_eq] at hcmp
      have h3 := div_le_div_of_nonneg_right (sub_le_sub_right (hsub i) (u j)) hBpos.le
      have e : ((∑' m, P.p i m * u m) - u j) / B = (∑' m, P.p i m * u m) / B - u j / B * 1 := by
        ring
      rw [e] at h3
      linarith
    by_cases hlj : l = j
    · rw [hlj]
    · have hd := dir P j s h0 h1 hj0 hsubs l
      rw [hit_all P hirr j hj l hlj] at hd
      have hz : ENNReal.ofReal (s l) = 0 := by
        have h4 : ENNReal.ofReal (s l) + 1 ≤ 0 + 1 := by simpa using hd
        exact nonpos_iff_eq_zero.1 ((ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 h4)
      have hsl : s l ≤ 0 := ENNReal.ofReal_eq_zero.1 hz
      have hm := le_max_left ((u l - u j) / B) 0
      rw [← hs] at hm
      have : (u l - u j) / B ≤ 0 := le_trans hm hsl
      have := (div_nonpos_iff.1 this)
      rcases this with ⟨_, h⟩ | ⟨h, _⟩
      · linarith
      · linarith
  have hclos : ∀ b m, u b = u j → 0 < P.p b m → u m = u j := by
    intro b m hb hpm
    exact eq_of_avg P b u (u j) (hsm b) hle (by rw [← hb]; exact hsub b) m hpm
  obtain ⟨n, hn⟩ := hirr j i
  exact propagate P (fun m => u m = u j) hclos n j i rfl hn

end TC47

open QueueingFundamentals.Foundations FosterQueues.MG1 in
theorem solution (P : TransitionMatrix) (hirr : P.Irreducible)
    (hap : P.Aperiodic) :
    IsTransient P ↔
      ∃ y : ℕ → ℝ, (∃ C : ℝ, ∀ i, |y i| ≤ C) ∧ (∃ i j : ℕ, y i ≠ y j) ∧
        ∀ i : ℕ, i ≠ 0 → HasSum (fun j => P.p i j * y j) (y i) := by
  constructor
  · intro htr
    have hc0 : ∀ l, 0 ≤ (TC47.CC P 0 l).toReal := fun l => ENNReal.toReal_nonneg
    have hc1 : ∀ l, (TC47.CC P 0 l).toReal ≤ 1 := fun l => by
      have := ENNReal.toReal_mono ENNReal.one_ne_top (TC47.CC_le P 0 l)
      simpa using this
    have habs : ∀ l, |(TC47.CC P 0 l).toReal| ≤ 1 := fun l => by
      rw [abs_of_nonneg (hc0 l)]; exact hc1 l
    have hsc := TC47.summ_bdd P _ 1 habs
    refine ⟨fun l => (TC47.CC P 0 l).toReal, ⟨1, habs⟩, ?_, ?_⟩
    · by_contra hall
      push Not at hall
      have hy0 : (TC47.CC P 0 0).toReal = 1 := by simp [TC47.CC]
      have hr := TC47.real_rec P 0 0
      have hall' : ∀ l, (TC47.CC P 0 l).toReal = 1 := fun l => by
        rw [← hy0]; exact (hall 0 l).symm
      simp only [hall', mul_one] at hr
      rw [(P.row_sum 0).tsum_eq] at hr
      have hne : TC47.FF P 0 0 ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top (TC47.FF_le_one P 0 0)
      have h1 : TC47.FF P 0 0 = 1 := by
        rw [← ENNReal.ofReal_toReal hne, hr, ENNReal.ofReal_one]
      have h2 : P.returnProb 0 < 1 := htr 0
      change TC47.FF P 0 0 < 1 at h2
      rw [h1] at h2
      exact lt_irrefl _ h2
    · intro i hi
      have h := (hsc i).hasSum
      rw [← TC47.real_rec] at h
      simpa [TC47.CC, hi] using h
  · rintro ⟨y, ⟨C, hC⟩, ⟨a, b, hab⟩, hy⟩ j
    by_contra hlt
    have hj : TC47.FF P j j = 1 :=
      le_antisymm (TC47.FF_le_one P j j) (not_lt.1 hlt)
    by_cases hs : y 0 ≤ ∑' l, P.p 0 l * y l
    · have hsub : ∀ i, y i ≤ ∑' l, P.p i l * y l := by
        intro i
        by_cases hi : i = 0
        · subst hi; exact hs
        · exact le_of_eq (hy i hi).tsum_eq.symm
      have ha := TC47.const_of_sub P hirr j hj y C hC hsub a
      have hb := TC47.const_of_sub P hirr j hj y C hC hsub b
      exact hab (ha.trans hb.symm)
    · push Not at hs
      have hC' : ∀ l, |(-y) l| ≤ C := fun l => by simpa using hC l
      have hsub : ∀ i, (-y) i ≤ ∑' l, P.p i l * (-y) l := by
        intro i
        simp only [Pi.neg_apply, mul_neg, tsum_neg]
        by_cases hi : i = 0
        · subst hi; linarith
        · rw [(hy i hi).tsum_eq]
      have ha := TC47.const_of_sub P hirr j hj (-y) C hC' hsub a
      have hb := TC47.const_of_sub P hirr j hj (-y) C hC' hsub b
      simp only [Pi.neg_apply, neg_inj] at ha hb
      exact hab (ha.trans hb.symm)
