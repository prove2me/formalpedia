-- Prove2me | solution 1 for FosterQueues.MG1.theorem5_recurrence_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T06:12:31.342321+00:00
-- url     : https://prove2.me/submissions/885a7873-08b0-41dd-b314-53bef7860b5e

import Mathlib
import Definitions.Def_FosterQueues_MG1_Model

open scoped ENNReal
open QueueingFundamentals.Foundations

set_option autoImplicit false

namespace FR2B

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

lemma maxp (hirr : P.Irreducible) (y : ℕ → ℝ)
    (hsum : ∀ i : ℕ, i ≠ 0 → Summable (fun j => P.p i j * y j))
    (hineq : ∀ i : ℕ, i ≠ 0 → ∑' j : ℕ, P.p i j * y j ≤ y i)
    (hlim : Filter.Tendsto y Filter.atTop Filter.atTop)
    (v : ℕ → ℝ) (hv0 : ∀ l, 0 ≤ v l) (hv1 : ∀ l, v l ≤ 1)
    (hsub : ∀ i, i ≠ 0 → v i ≤ ∑' l, P.p i l * v l) (i : ℕ) : v i ≤ v 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hεpos, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * (|y i - y 0| + 1) = (v i - v 0) / 2 :=
    ⟨(v i - v 0) / (2 * (|y i - y 0| + 1)), by
      have : 0 < |y i - y 0| + 1 := by positivity
      have : 0 < v i - v 0 := by linarith
      positivity, by
      have : 0 < |y i - y 0| + 1 := by positivity
      field_simp⟩
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, ∀ l, w l = v l - v 0 - ε * (y l - y 0) := ⟨_, fun l => rfl⟩
  have hw0 : w 0 = 0 := by rw [hw]; ring
  have hwi : 0 < w i := by
    have h1 : ε * (y i - y 0) ≤ ε * |y i - y 0| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hεpos.le
    rw [hw]
    nlinarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlim.eventually_ge_atTop (y 0 + 2 / ε))
  have hwN : ∀ l, N ≤ l → w l < 0 := by
    intro l hl
    have h3 := hN l hl
    have h2 : 2 ≤ ε * (y l - y 0) := by
      have h4 : 2 / ε ≤ y l - y 0 := by linarith
      calc (2 : ℝ) = ε * (2 / ε) := by field_simp
        _ ≤ ε * (y l - y 0) := mul_le_mul_of_nonneg_left h4 hεpos.le
    rw [hw]; linarith [hv1 l, hv0 0]
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image (Finset.range (N + 1)) w ⟨0, by simp⟩
  have hmax : ∀ l, w l ≤ w a := by
    intro l
    by_cases hl : l < N + 1
    · exact ha l (Finset.mem_range.2 hl)
    · have h5 := hwN l (by omega)
      have h6 := ha 0 (by simp)
      linarith
  have hm : 0 < w a := lt_of_lt_of_le hwi (hmax i)
  have hclos : ∀ b l, w b = w a → 0 < P.p b l → w l = w a := by
    intro b l hb hpl
    have hb0 : b ≠ 0 := by intro h; rw [h, hw0] at hb; linarith
    have hsv : Summable (fun l => P.p b l * v l) :=
      Summable.of_nonneg_of_le (fun l => mul_nonneg (P.nonneg b l) (hv0 l))
        (fun l => mul_le_of_le_one_right (P.nonneg b l) (hv1 l)) (P.row_sum b).summable
    have hH : HasSum (fun l => P.p b l * w l) ((∑' l, P.p b l * v l) - v 0 * 1 -
        ε * (∑' l, P.p b l * y l) + ε * y 0 * 1) := by
      have := (((hsv.hasSum.sub ((P.row_sum b).mul_left (v 0))).sub
        ((hsum b hb0).hasSum.mul_left ε)).add ((P.row_sum b).mul_left (ε * y 0)))
      convert this using 1
      all_goals first | rfl | (funext l; rw [hw]; ring)
    refine eq_of_avg P b w (w a) hH.summable hmax ?_ l hpl
    rw [hH.tsum_eq, ← hb, hw]
    have h7 := hsub b hb0
    have h8 := mul_le_mul_of_nonneg_left (hineq b hb0) hεpos.le
    linarith
  obtain ⟨n, hn⟩ := hirr a 0
  have h9 := propagate P (fun l => w l = w a) hclos n a 0 rfl hn
  rw [hw0] at h9
  linarith

lemma zero_of_harm (hirr : P.Irreducible) (j : ℕ) (v : ℕ → ℝ) (hv0 : ∀ l, 0 ≤ v l)
    (hv1 : ∀ l, v l ≤ 1) (hvj : v j = 0) (hmax : ∀ l, v l ≤ v 0)
    (hharm : ∀ i, i ≠ j → v i = ∑' l, P.p i l * v l) : v 0 = 0 := by
  by_contra hne
  have hpos : 0 < v 0 := lt_of_le_of_ne (hv0 0) (Ne.symm hne)
  have hclos : ∀ b l, v b = v 0 → 0 < P.p b l → v l = v 0 := by
    intro b l hb hpl
    have hbj : b ≠ j := by intro h; rw [h, hvj] at hb; linarith
    have hs : Summable (fun l => P.p b l * v l) :=
      Summable.of_nonneg_of_le (fun l => mul_nonneg (P.nonneg b l) (hv0 l))
        (fun l => mul_le_of_le_one_right (P.nonneg b l) (hv1 l)) (P.row_sum b).summable
    exact eq_of_avg P b v (v 0) hs hmax (le_of_eq (by rw [← hharm b hbj, hb])) l hpl
  obtain ⟨n, hn⟩ := hirr 0 j
  have h := propagate P (fun l => v l = v 0) hclos n 0 j rfl hn
  rw [hvj] at h
  linarith

end FR2B

open QueueingFundamentals.Foundations FosterQueues.MG1 in
theorem solution (P : TransitionMatrix) (hirr : P.Irreducible)
    (hap : P.Aperiodic) (y : ℕ → ℝ)
    (hsum : ∀ i : ℕ, i ≠ 0 → Summable (fun j => P.p i j * y j))
    (hineq : ∀ i : ℕ, i ≠ 0 → ∑' j : ℕ, P.p i j * y j ≤ y i)
    (hlim : Filter.Tendsto y Filter.atTop Filter.atTop) :
    IsRecurrent P := by
  intro j
  have hCt : ∀ l, FR2B.CC P j l ≠ ⊤ := fun l =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (FR2B.CC_le P j l)
  have hc0 : ∀ l, 0 ≤ (FR2B.CC P j l).toReal := fun l => ENNReal.toReal_nonneg
  have hc1 : ∀ l, (FR2B.CC P j l).toReal ≤ 1 := fun l => by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (FR2B.CC_le P j l)
    simpa using this
  have hsc : ∀ i, Summable (fun l => P.p i l * (FR2B.CC P j l).toReal) := fun i =>
    Summable.of_nonneg_of_le (fun l => mul_nonneg (P.nonneg i l) (hc0 l))
      (fun l => mul_le_of_le_one_right (P.nonneg i l) (hc1 l)) (P.row_sum i).summable
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ℝ, ∀ l, v l = 1 - (FR2B.CC P j l).toReal := ⟨_, fun l => rfl⟩
  have hsv : ∀ i, ∑' l, P.p i l * v l = 1 - ∑' l, P.p i l * (FR2B.CC P j l).toReal := by
    intro i
    have := (P.row_sum i).sub (hsc i).hasSum
    refine (HasSum.tsum_eq ?_)
    convert this using 1
    all_goals first | rfl | (funext l; rw [hv]; ring)
  have hvj : v j = 0 := by rw [hv]; simp [FR2B.CC]
  have hharm : ∀ i, i ≠ j → v i = ∑' l, P.p i l * v l := by
    intro i hij
    rw [hsv, ← FR2B.real_rec, hv]
    simp [FR2B.CC, hij]
  have hv0 : ∀ l, 0 ≤ v l := fun l => by rw [hv]; linarith [hc1 l]
  have hv1 : ∀ l, v l ≤ 1 := fun l => by rw [hv]; linarith [hc0 l]
  have hsub : ∀ i, i ≠ 0 → v i ≤ ∑' l, P.p i l * v l := by
    intro i _
    by_cases hij : i = j
    · subst hij; rw [hvj]
      exact tsum_nonneg fun l => mul_nonneg (P.nonneg i l) (hv0 l)
    · exact le_of_eq (hharm i hij)
  have hmax := FR2B.maxp P hirr y hsum hineq hlim v hv0 hv1 hsub
  have hz := FR2B.zero_of_harm P hirr j v hv0 hv1 hvj hmax hharm
  have hall : ∀ l, (FR2B.CC P j l).toReal = 1 := by
    intro l
    have h1 := hmax l
    have h2 := hv0 l
    rw [hz] at h1
    rw [hv] at h1 h2
    linarith
  have hreal : (FR2B.FF P j j).toReal = 1 := by
    rw [FR2B.real_rec]
    simp only [hall, mul_one]
    exact (P.row_sum j).tsum_eq
  have hne : FR2B.FF P j j ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (FR2B.FF_le_one P j j)
  show FR2B.FF P j j = 1
  rw [← ENNReal.ofReal_toReal hne, hreal, ENNReal.ofReal_one]
