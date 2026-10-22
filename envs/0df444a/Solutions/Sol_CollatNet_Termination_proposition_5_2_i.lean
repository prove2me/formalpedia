-- Prove2me | solution 1 for CollatNet.Termination.proposition_5_2_i
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T12:43:51.315571+00:00
-- url     : https://prove2.me/submissions/b48bb7f7-eaf4-4175-bbdb-1b251a0adb5f

import Mathlib
import Definitions.Def_CollatNet_Termination_Model

set_option autoImplicit false

namespace CollatNet.Termination.P52aux

open CollatNet.Termination Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma ratio_nonneg' {o : ι → ι → ℝ} (h : ∀ i j, 0 ≤ o i j) (i j : ι) : 0 ≤ ratio o i j := by
  unfold ratio
  split_ifs
  · exact le_refl _
  · exact div_nonneg (h i j) (sum_nonneg fun k _ => h i k)

lemma ratio_sum_le {o : ι → ι → ℝ} (i : ι) : ∑ j, ratio o i j ≤ 1 := by
  unfold ratio
  split_ifs with h0
  · simp
  · rw [← Finset.sum_div, div_self h0]

lemma ratio_row {o o' : ι → ι → ℝ} (i j : ι) (h : ∀ k, o i k = o' i k) :
    ratio o i j = ratio o' i j := by
  unfold ratio
  simp only [h]

lemma ratio_zero_row {o : ι → ι → ℝ} (i j : ι) (h : ∀ k, o i k = 0) : ratio o i j = 0 := by
  unfold ratio
  simp [h]

lemma p1_nonneg {X : Network ι} {p1 : ι → ι → ℝ} (h : Clears1 X p1) (i j : ι) : 0 ≤ p1 i j :=
  (h i j).1

lemma p1_le {X : Network ι} {p1 : ι → ι → ℝ} (h : Clears1 X p1) (i j : ι) :
    p1 i j ≤ X.pbar i j := by
  have e := (h i j).2
  split_ifs at e
  · rw [e]; exact min_le_left _ _
  · rw [e]

lemma p1_eq_of_not {X : Network ι} {p1 : ι → ι → ℝ} (h : Clears1 X p1) {i : ι}
    (hi : i ∉ D1 X p1) (j : ι) : p1 i j = X.pbar i j := by
  have e := (h i j).2
  rwa [if_neg hi] at e

lemma seized1_of_not {X : Network ι} {p1 : ι → ι → ℝ} {i : ι} (hi : i ∉ D1 X p1) (j : ι) :
    seized1 X p1 i j = 0 := by
  simp [seized1, hi]

lemma cash_nonneg {X : Network ι} (hX : X.Standing) {p1 : ι → ι → ℝ} (h : Clears1 X p1)
    (i : ι) : 0 ≤ (initFT X p1).cash i := by
  show 0 ≤ X.c i + ∑ k, p1 k i - ∑ k, (p1 i k - seized1 X p1 i k)
  have hA : 0 ≤ assets1 X p1 i :=
    add_nonneg (hX.2.1 i) (sum_nonneg fun k _ => p1_nonneg h k i)
  by_cases hi : i ∈ D1 X p1
  · have hterm : ∀ k, p1 i k - seized1 X p1 i k ≤ a1 X i k * assets1 X p1 i := by
      intro k
      have e := (h i k).2
      rw [if_pos hi] at e
      have ha : 0 ≤ a1 X i k :=
        ratio_nonneg' (fun a b => le_max_right (X.pbar a b - X.m a b) 0) i k
      have hs : seized1 X p1 i k = min (X.m i k) (X.pbar i k) := by simp [seized1, hi]
      rw [hs, e]
      have h1 := min_le_right (X.pbar i k) (X.m i k + a1 X i k * assets1 X p1 i)
      have h2 := min_le_left (X.pbar i k) (X.m i k + a1 X i k * assets1 X p1 i)
      rcases le_total (X.m i k) (X.pbar i k) with hm | hm
      · rw [min_eq_left hm]; linarith
      · rw [min_eq_right hm]; nlinarith [mul_nonneg ha hA]
    have hsum : ∑ k, (p1 i k - seized1 X p1 i k) ≤ assets1 X p1 i := by
      calc ∑ k, (p1 i k - seized1 X p1 i k) ≤ ∑ k, a1 X i k * assets1 X p1 i :=
            sum_le_sum fun k _ => hterm k
        _ = (∑ k, a1 X i k) * assets1 X p1 i := by rw [Finset.sum_mul]
        _ ≤ assets1 X p1 i := mul_le_of_le_one_left hA (ratio_sum_le i)
    unfold assets1 at hsum
    linarith
  · have hi' : oblTot X i ≤ assets1 X p1 i := by
      simpa [D1] using hi
    have : ∑ k, (p1 i k - seized1 X p1 i k) = oblTot X i := by
      unfold oblTot
      exact sum_congr rfl fun k _ => by rw [p1_eq_of_not h hi, seized1_of_not hi, sub_zero]
    unfold assets1 at hi'
    linarith

lemma ret_nonneg {X : Network ι} (hX : X.Standing) (p1 : ι → ι → ℝ) (i : ι) :
    0 ≤ (initFT X p1).ret i := by
  show 0 ≤ returned2 X p1 i
  unfold returned2
  split_ifs with hi
  · refine sum_nonneg fun j _ => ?_
    have : seized1 X p1 i j ≤ X.m i j := by
      simp only [seized1, if_pos hi]; exact min_le_left _ _
    linarith
  · exact sum_nonneg fun j _ => hX.2.2.1 i j

lemma base_nonneg {X : Network ι} (hX : X.Standing) {p1 : ι → ι → ℝ} (h : Clears1 X p1)
    (i : ι) : 0 ≤ (initFT X p1).cash i + (initFT X p1).ret i :=
  add_nonneg (cash_nonneg hX h i) (ret_nonneg hX p1 i)

/-! ### Round 2 maps -/

/-- The right-hand side of the clearing equation (30). -/
noncomputable def G (X : Network ι) (s : RoundState ι) (x : ι → ι → ℝ) : ι → ι → ℝ :=
  fun i j => min (s.obl i j) (seizedAt X s x i j + propAt X s x i j * assetsAt s x i)

lemma seizedFT_zero {X : Network ι} (hX : X.Standing) (p1 x : ι → ι → ℝ) (i j : ι) :
    seizedAt X (initFT X p1) x i j = 0 := by
  unfold seizedAt
  split_ifs with hc
  · obtain ⟨hi, hj⟩ := hc
    have hi' : i ∈ (initFT X p1).alive := (mem_filter.1 hi).1
    have hi2 : i ∉ D1 X p1 := by simpa [initFT] using hi'
    have hj2 : j ∉ D1 X p1 := by simpa [initFT] using hj
    have : (initFT X p1).obl i j = 0 := by
      show (if i ∈ D1 X p1 ∨ j ∈ D1 X p1 then X.v i j + X.pbar i j - p1 i j else 0) = 0
      rw [if_neg (by tauto)]
    rw [this]; exact min_eq_right (hX.2.2.1 i j)
  · rfl

lemma seizedST_zero {X : Network ι} (hX : X.Standing) (p1 x : ι → ι → ℝ) (i j : ι) :
    seizedAt X (initST X p1) x i j = 0 := by
  unfold seizedAt
  split_ifs with hc
  · obtain ⟨hi, _⟩ := hc
    have hi' : i ∈ (initST X p1).alive := (mem_filter.1 hi).1
    have hi2 : i ∉ D1 X p1 := by simpa [initST, initFT] using hi'
    have : (initST X p1).obl i j = 0 := by
      show (if i ∈ D1 X p1 then X.v i j + X.pbar i j - p1 i j else 0) = 0
      rw [if_neg hi2]
    rw [this]; exact min_eq_right (hX.2.2.1 i j)
  · rfl

lemma G_eq {X : Network ι} {s : RoundState ι} (hz : ∀ x i j, seizedAt X s x i j = 0)
    (x : ι → ι → ℝ) (i j : ι) :
    G X s x i j = min (s.obl i j) (ratio s.obl i j * (s.cash i + s.ret i + ∑ k, x k i)) := by
  simp only [G, propAt, hz, sub_zero, zero_add, assetsAt]

lemma G_mono {X : Network ι} {s : RoundState ι} (hz : ∀ x i j, seizedAt X s x i j = 0)
    (hobl : ∀ i j, 0 ≤ s.obl i j) {x y : ι → ι → ℝ} (hxy : x ≤ y) : G X s x ≤ G X s y := by
  intro i j
  rw [G_eq hz, G_eq hz]
  apply min_le_min_left
  apply mul_le_mul_of_nonneg_left _ (ratio_nonneg' hobl i j)
  have : ∑ k, x k i ≤ ∑ k, y k i := sum_le_sum fun k _ => hxy k i
  linarith

lemma G_nonneg {X : Network ι} {s : RoundState ι} (hz : ∀ x i j, seizedAt X s x i j = 0)
    (hobl : ∀ i j, 0 ≤ s.obl i j) (hb : ∀ i, 0 ≤ s.cash i + s.ret i) {x : ι → ι → ℝ}
    (hx : 0 ≤ x) : 0 ≤ G X s x := by
  intro i j
  rw [G_eq hz]
  refine le_min (hobl i j) (mul_nonneg (ratio_nonneg' hobl i j) ?_)
  have : 0 ≤ ∑ k, x k i := sum_nonneg fun k _ => hx k i
  linarith [hb i]

lemma G_le {X : Network ι} {s : RoundState ι} (x : ι → ι → ℝ) : G X s x ≤ s.obl :=
  fun i j => min_le_left _ _

lemma oblFT_nonneg {X : Network ι} (hX : X.Standing) {p1 : ι → ι → ℝ} (h : Clears1 X p1)
    (i j : ι) : 0 ≤ (initFT X p1).obl i j := by
  show 0 ≤ (if i ∈ D1 X p1 ∨ j ∈ D1 X p1 then X.v i j + X.pbar i j - p1 i j else 0)
  split_ifs
  · linarith [hX.2.2.2.1 i j, p1_le h i j]
  · exact le_refl _

lemma oblST_nonneg {X : Network ι} (hX : X.Standing) {p1 : ι → ι → ℝ} (h : Clears1 X p1)
    (i j : ι) : 0 ≤ (initST X p1).obl i j := by
  show 0 ≤ (if i ∈ D1 X p1 then X.v i j + X.pbar i j - p1 i j else 0)
  split_ifs
  · linarith [hX.2.2.2.1 i j, p1_le h i j]
  · exact le_refl _

lemma oblST_le {X : Network ι} (hX : X.Standing) {p1 : ι → ι → ℝ} (h : Clears1 X p1) :
    (initST X p1).obl ≤ (initFT X p1).obl := by
  intro i j
  show (if i ∈ D1 X p1 then X.v i j + X.pbar i j - p1 i j else 0) ≤
    (if i ∈ D1 X p1 ∨ j ∈ D1 X p1 then X.v i j + X.pbar i j - p1 i j else 0)
  by_cases hi : i ∈ D1 X p1
  · rw [if_pos hi, if_pos (Or.inl hi)]
  · rw [if_neg hi]; exact oblFT_nonneg hX h i j

lemma G_ST_le_FT {X : Network ι} (hX : X.Standing) {p1 : ι → ι → ℝ} (h : Clears1 X p1)
    {x : ι → ι → ℝ} (hx : 0 ≤ x) : G X (initST X p1) x ≤ G X (initFT X p1) x := by
  intro i j
  rw [G_eq (seizedST_zero hX p1), G_eq (seizedFT_zero hX p1)]
  by_cases hi : i ∈ D1 X p1
  · have hrow : ∀ k, (initST X p1).obl i k = (initFT X p1).obl i k := by
      intro k
      show (if i ∈ D1 X p1 then X.v i k + X.pbar i k - p1 i k else 0) =
        (if i ∈ D1 X p1 ∨ k ∈ D1 X p1 then X.v i k + X.pbar i k - p1 i k else 0)
      rw [if_pos hi, if_pos (Or.inl hi)]
    rw [hrow j, ratio_row i j hrow]
    exact le_refl _
  · have hrow : ∀ k, (initST X p1).obl i k = 0 := by
      intro k
      show (if i ∈ D1 X p1 then X.v i k + X.pbar i k - p1 i k else 0) = 0
      rw [if_neg hi]
    rw [hrow j, ratio_zero_row i j hrow, zero_mul, min_self]
    have := G_nonneg (seizedFT_zero hX p1) (oblFT_nonneg hX h) (base_nonneg hX h) hx i j
    rwa [G_eq (seizedFT_zero hX p1)] at this

lemma exists_fixed {a b : ι → ι → ℝ} (hab : a ≤ b) (F : (ι → ι → ℝ) → (ι → ι → ℝ))
    (hmono : ∀ x y, x ≤ y → F x ≤ F y)
    (hmaps : ∀ x, a ≤ x → x ≤ b → a ≤ F x ∧ F x ≤ b) :
    ∃ y, a ≤ y ∧ y ≤ b ∧ F y = y := by
  haveI : Fact (a ≤ b) := ⟨hab⟩
  let f : Set.Icc a b →o Set.Icc a b :=
    ⟨fun x => ⟨F x.1, hmaps x.1 x.2.1 x.2.2⟩, fun x y hxy => hmono x.1 y.1 hxy⟩
  refine ⟨(OrderHom.lfp f).1, (OrderHom.lfp f).2.1, (OrderHom.lfp f).2.2, ?_⟩
  exact congrArg Subtype.val f.map_lfp

lemma clears_of_fixed {X : Network ι} {s : RoundState ι} {y : ι → ι → ℝ} (hy0 : 0 ≤ y)
    (hy : G X s y = y) : ClearsAt X s y := by
  intro i j
  exact ⟨hy0 i j, (congrFun (congrFun hy i) j).symm⟩

lemma clears_fixed {X : Network ι} {s : RoundState ι} {y : ι → ι → ℝ} (hc : ClearsAt X s y) :
    G X s y = y := by
  funext i j
  exact ((hc i j).2).symm

lemma clears_nonneg {X : Network ι} {s : RoundState ι} {y : ι → ι → ℝ} (hc : ClearsAt X s y) :
    0 ≤ y := fun i j => (hc i j).1

lemma clears_le {X : Network ι} {s : RoundState ι} {y : ι → ι → ℝ} (hc : ClearsAt X s y)
    (i j : ι) : y i j ≤ s.obl i j := by
  have e := (hc i j).2
  have := min_le_left (s.obl i j) (seizedAt X s y i j + propAt X s y i j * assetsAt s y i)
  linarith

lemma q2_le_p2 {X : Network ι} (hX : X.Standing) (p : ℕ → ι → ι → ℝ) (q2 : ι → ι → ℝ)
    (hp : ClearsFT X p)
    (hext : (IsGreatest (round2FT X (p 1)) (p 2) ∧ IsGreatest (round2ST X (p 1)) q2) ∨
      (IsLeast (round2FT X (p 1)) (p 2) ∧ IsLeast (round2ST X (p 1)) q2)) :
    q2 ≤ p 2 := by
  have h1 := hp.1
  have hzF := seizedFT_zero hX (p 1)
  have hzS := seizedST_zero hX (p 1)
  rcases hext with ⟨hF, hS⟩ | ⟨hF, hS⟩
  · have hq : ClearsAt X (initST X (p 1)) q2 := hS.1
    have hq0 := clears_nonneg hq
    have hab : q2 ≤ (initFT X (p 1)).obl :=
      le_trans (fun i j => clears_le hq i j) (oblST_le hX h1)
    obtain ⟨y, hy1, hy2, hy⟩ := exists_fixed hab (G X (initFT X (p 1)))
      (fun x y hxy => G_mono hzF (oblFT_nonneg hX h1) hxy)
      (fun x hx1 _ => by
        refine ⟨?_, G_le x⟩
        calc q2 = G X (initST X (p 1)) q2 := (clears_fixed hq).symm
          _ ≤ G X (initFT X (p 1)) q2 := G_ST_le_FT hX h1 hq0
          _ ≤ G X (initFT X (p 1)) x := G_mono hzF (oblFT_nonneg hX h1) hx1)
    have hyc : ClearsAt X (initFT X (p 1)) y := clears_of_fixed (le_trans hq0 hy1) hy
    exact le_trans hy1 (hF.2 hyc)
  · have hpc : ClearsAt X (initFT X (p 1)) (p 2) := hF.1
    have hp0 := clears_nonneg hpc
    obtain ⟨y, hy1, hy2, hy⟩ := exists_fixed hp0 (G X (initST X (p 1)))
      (fun x y hxy => G_mono hzS (oblST_nonneg hX h1) hxy)
      (fun x hx1 hx2 => by
        refine ⟨G_nonneg hzS (oblST_nonneg hX h1) (base_nonneg hX h1) hx1, ?_⟩
        calc G X (initST X (p 1)) x ≤ G X (initST X (p 1)) (p 2) :=
              G_mono hzS (oblST_nonneg hX h1) hx2
          _ ≤ G X (initFT X (p 1)) (p 2) := G_ST_le_FT hX h1 hp0
          _ = p 2 := clears_fixed hpc)
    have hyc : ClearsAt X (initST X (p 1)) y := clears_of_fixed hy1 hy
    exact le_trans (hS.2 hyc) hy2

/-! ### Later rounds: no new defaults under (40) -/

lemma inv {X : Network ι} (hX : X.Standing) (p : ℕ → ι → ι → ℝ) (hp : ClearsFT X p) :
    ∀ k, k + 1 ≤ numRounds ι → ∀ i ∈ (stateFT X p k).alive,
      netWorth X (p 1) i - ∑ j, ∑ l ∈ range k, p (l + 2) i j ≤
          (stateFT X p k).cash i + (stateFT X p k).ret i ∧
      (∀ j, (stateFT X p k).obl i j + ∑ l ∈ range k, p (l + 2) i j ≤ X.v i j) ∧
      (∀ j ∈ (stateFT X p k).alive,
        (stateFT X p k).obl i j = 0 ∧ ∑ l ∈ range k, p (l + 2) i j = 0) := by
  intro k
  induction k with
  | zero =>
    intro _ i hi
    have hi2 : i ∉ D1 X (p 1) := by simpa [stateFT, initFT] using hi
    simp only [Finset.sum_range_zero, sum_const_zero, sub_zero, add_zero]
    refine ⟨?_, ?_, ?_⟩
    · show netWorth X (p 1) i ≤ (initFT X (p 1)).cash i + (initFT X (p 1)).ret i
      have : (initFT X (p 1)).cash i = X.c i + ∑ k, p 1 k i - oblTot X i := by
        show X.c i + ∑ k, p 1 k i - ∑ k, (p 1 i k - seized1 X (p 1) i k) = _
        unfold oblTot
        congr 1
        exact sum_congr rfl fun k _ => by
          rw [p1_eq_of_not hp.1 hi2, seized1_of_not hi2, sub_zero]
      rw [this]; unfold netWorth; linarith
    · intro j
      show (if i ∈ D1 X (p 1) ∨ j ∈ D1 X (p 1) then X.v i j + X.pbar i j - p 1 i j else 0)
        ≤ X.v i j
      rw [p1_eq_of_not hp.1 hi2]
      split_ifs
      · linarith
      · exact hX.2.2.2.1 i j
    · intro j hj
      have hj2 : j ∉ D1 X (p 1) := by simpa [stateFT, initFT] using hj
      refine ⟨?_, trivial⟩
      show (if i ∈ D1 X (p 1) ∨ j ∈ D1 X (p 1) then X.v i j + X.pbar i j - p 1 i j else 0) = 0
      rw [if_neg (by tauto)]
  | succ k ih =>
    intro hk i hi
    have IH := ih (by omega)
    have hc := hp.2 k (by omega)
    rw [show stateFT X p (k + 1) = nextFT X (stateFT X p k) (p (k + 2)) from rfl] at hi ⊢
    simp only [Finset.sum_range_succ]
    generalize p (k + 2) = x at hc hi ⊢
    generalize stateFT X p k = s at IH hc hi ⊢
    obtain ⟨hia, hind⟩ := mem_sdiff.1 hi
    obtain ⟨I1, I2, I3⟩ := IH i hia
    have hsz : ∀ j, seizedAt X s x i j = 0 := fun j => by
      unfold seizedAt; rw [if_neg (fun h => hind h.1)]
    have hx0 := clears_nonneg hc
    refine ⟨?_, ?_, ?_⟩
    · have hcash : (nextFT X s x).cash i = s.cash i + s.ret i + ∑ k, x k i - ∑ k, x i k := by
        show s.cash i + s.ret i + ∑ k, x k i - ∑ k, (x i k - seizedAt X s x i k) = _
        simp only [hsz, sub_zero]
      have hret : (nextFT X s x).ret i = ∑ j ∈ defaultsAt s x, X.m i j := by
        show (if i ∈ defaultsAt s x then ∑ j ∈ s.alive, (X.m i j - seizedAt X s x i j)
          else if i ∈ s.alive then ∑ j ∈ defaultsAt s x, X.m i j else 0) = _
        rw [if_neg hind, if_pos hia]
      rw [hcash, hret, sum_add_distrib]
      have : 0 ≤ ∑ j ∈ defaultsAt s x, X.m i j := sum_nonneg fun j _ => hX.2.2.1 i j
      have : 0 ≤ ∑ k, x k i := sum_nonneg fun k _ => hx0 k i
      linarith
    · intro j
      show (if i ∈ s.alive ∧ j ∈ s.alive then
          (if i ∈ defaultsAt s x ∨ j ∈ defaultsAt s x then X.v i j + s.obl i j - x i j else 0)
          else s.obl i j - x i j) + (∑ l ∈ range k, p (l + 2) i j + x i j) ≤ X.v i j
      by_cases hja : j ∈ s.alive
      · obtain ⟨h1, h2⟩ := I3 j hja
        by_cases hjd : j ∈ defaultsAt s x
        · rw [if_pos ⟨hia, hja⟩, if_pos (Or.inr hjd)]
          linarith
        · rw [if_pos ⟨hia, hja⟩, if_neg (by tauto)]
          have := clears_le hc i j
          linarith [hX.2.2.2.1 i j]
      · rw [if_neg (fun h => hja h.2)]
        linarith [I2 j]
    · intro j hj
      obtain ⟨hja, hjd⟩ := mem_sdiff.1 hj
      obtain ⟨h1, h2⟩ := I3 j hja
      have := clears_le hc i j
      have : 0 ≤ x i j := hx0 i j
      refine ⟨?_, by linarith⟩
      show (if i ∈ s.alive ∧ j ∈ s.alive then
          (if i ∈ defaultsAt s x ∨ j ∈ defaultsAt s x then X.v i j + s.obl i j - x i j else 0)
          else s.obl i j - x i j) = 0
      rw [if_pos ⟨hia, hja⟩, if_neg (by tauto)]

lemma default_lt {X : Network ι} (hX : X.Standing) (p : ℕ → ι → ι → ℝ) (hp : ClearsFT X p)
    (k : ℕ) (hk : k + 2 ≤ numRounds ι) (i : ι)
    (hi : i ∈ defaultsAt (stateFT X p k) (p (k + 2))) : netWorth X (p 1) i < vTot X i := by
  have hc := hp.2 k hk
  obtain ⟨hia, hlt⟩ := mem_filter.1 hi
  obtain ⟨I1, I2, -⟩ := inv hX p hp k (by omega) i hia
  have hx0 := clears_nonneg hc
  have hrec : 0 ≤ ∑ k', p (k + 2) k' i := sum_nonneg fun k' _ => hx0 k' i
  have hob : ∑ j, (stateFT X p k).obl i j ≤ vTot X i - ∑ j, ∑ l ∈ range k, p (l + 2) i j := by
    unfold vTot
    rw [← sum_sub_distrib]
    exact sum_le_sum fun j _ => by linarith [I2 j]
  unfold assetsAt at hlt
  linarith

end CollatNet.Termination.P52aux

open CollatNet.Termination Finset in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Network ι)
    (hX : X.Standing) (p : ℕ → ι → ι → ℝ) (q2 : ι → ι → ℝ) (hp : ClearsFT X p)
    (hext : (IsGreatest (round2FT X (p 1)) (p 2) ∧ IsGreatest (round2ST X (p 1)) q2) ∨
      (IsLeast (round2FT X (p 1)) (p 2) ∧ IsLeast (round2ST X (p 1)) q2))
    (h40 : ∑ i ∈ Df X p \ D1 X (p 1), vTot X i ≤
      ∑ i ∈ Df X p \ D1 X (p 1), netWorth X (p 1) i) :
    shortfallFT X p ≤ shortfallST X (p 1) q2 := by
  have hR : 2 ≤ numRounds ι := le_max_left _ _
  have hDf : Df X p = D1 X (p 1) := by
    have hemp : Df X p \ D1 X (p 1) = ∅ := by
      by_contra hne
      have hne' : (Df X p \ D1 X (p 1)).Nonempty := nonempty_iff_ne_empty.2 hne
      have hlt : ∑ i ∈ Df X p \ D1 X (p 1), netWorth X (p 1) i <
          ∑ i ∈ Df X p \ D1 X (p 1), vTot X i := by
        apply sum_lt_sum_of_nonempty hne'
        intro i hi
        obtain ⟨hiDf, hiD1⟩ := mem_sdiff.1 hi
        unfold Df at hiDf
        rcases mem_union.1 hiDf with h | h
        · exact absurd h hiD1
        · obtain ⟨k, hk, hik⟩ := mem_biUnion.1 h
          have := mem_range.1 hk
          exact P52aux.default_lt hX p hp k (by omega) i hik
      linarith
    exact Subset.antisymm (sdiff_eq_empty_iff_subset.1 hemp)
      (by unfold Df; exact subset_union_left)
  have hq := P52aux.q2_le_p2 hX p q2 hp hext
  unfold shortfallFT shortfallST
  rw [hDf]
  apply sum_le_sum
  intro i _
  have hsub : ({1, 2} : Finset ℕ) ⊆ Icc 1 (numRounds ι) := by
    intro l hl
    simp only [mem_insert, mem_singleton] at hl
    rw [Finset.mem_Icc]
    omega
  have h12 : ∑ l ∈ ({1, 2} : Finset ℕ), ∑ j, p l i j ≤
      ∑ l ∈ Icc 1 (numRounds ι), ∑ j, p l i j := by
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro l hl hl2
    have hl' := Finset.mem_Icc.1 hl
    simp only [mem_insert, mem_singleton, not_or] at hl2
    have hc := hp.2 (l - 2) (by omega)
    rw [show l - 2 + 2 = l by omega] at hc
    exact sum_nonneg fun j _ => (hc i j).1
  rw [sum_pair (by norm_num)] at h12
  have : ∑ j, q2 i j ≤ ∑ j, p 2 i j := sum_le_sum fun j _ => hq i j
  linarith
