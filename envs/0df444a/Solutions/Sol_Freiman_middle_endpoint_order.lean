-- Prove2me | solution 1 for Freiman.middle_endpoint_order
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T09:48:33.666722+00:00
-- url     : https://prove2.me/submissions/9f40efbd-7764-4656-88db-2322e7362e5d

import Definitions.Def_Freiman_middleRoots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

open Freiman

namespace FreimanM8EndpointOrder20260910

private lemma pe_nonneg (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ prefixEval w x := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    change 0 ≤ 1 / (((a:ℕ):ℝ) + prefixEval w x)
    positivity

private lemma pe_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, prefixEval, ih]

private lemma pe_order (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) :
    (w.length % 2 = 0 → prefixEval w x ≤ prefixEval w y) ∧
    (w.length % 2 = 1 → prefixEval w y ≤ prefixEval w x) := by
  induction w with
  | nil => simp [prefixEval, hxy]
  | cons a w ih =>
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    have hpx := pe_nonneg w x hx
    have hpy := pe_nonneg w y hy
    constructor
    · intro h
      have hw : w.length % 2 = 1 := by simp only [List.length_cons] at h; omega
      exact one_div_le_one_div_of_le (by linarith : 0 < ((a:ℕ):ℝ)+prefixEval w y)
        (by linarith only [ih.2 hw])
    · intro h
      have hw : w.length % 2 = 0 := by simp only [List.length_cons] at h; omega
      exact one_div_le_one_div_of_le (by linarith : 0 < ((a:ℕ):ℝ)+prefixEval w x)
        (by linarith only [ih.1 hw])

private lemma basic_bounds : 0 ≤ middleAlpha ∧ middleAlpha ≤ (1/2:ℝ) ∧
    (1/2:ℝ) ≤ middleBeta ∧ 0 ≤ middleRho := by
  have h4 : (4:ℝ) ≤ Real.sqrt 21 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h5 : Real.sqrt 21 ≤ (5:ℝ) := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h1 : (1:ℝ) ≤ Real.sqrt 3 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  dsimp [middleAlpha, middleBeta, middleRho]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private lemma small_tails :
    middleAlpha ∈ Set.Icc (0:ℝ) (1/2) ∧
    prefixEval [3] middleRho ∈ Set.Icc (0:ℝ) (1/2) ∧
    prefixEval [2] middleBeta ∈ Set.Icc (0:ℝ) (1/2) := by
  obtain ⟨ha, ha', hb, hr⟩ := basic_bounds
  refine ⟨⟨ha, ha'⟩, ?_, ?_⟩
  · change 0 ≤ 1/(3+middleRho) ∧ 1/(3+middleRho) ≤ (1/2:ℝ)
    constructor
    · positivity
    · apply (div_le_iff₀ (by linarith : 0 < 3+middleRho)).2
      linarith
  · change 0 ≤ 1/(2+middleBeta) ∧ 1/(2+middleBeta) ≤ (1/2:ℝ)
    constructor
    · positivity
    · apply (div_le_iff₀ (by linarith : 0 < 2+middleBeta)).2
      linarith

private lemma big_tails :
    (1/2:ℝ) ≤ middleBeta ∧
    (1/2:ℝ) ≤ prefixEval [1,3] middleRho ∧
    (1/2:ℝ) ≤ prefixEval [1,2] middleBeta := by
  obtain ⟨_, hs3, hs2⟩ := small_tails
  refine ⟨basic_bounds.2.2.1, ?_, ?_⟩
  · simp only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one]
    change (1/2:ℝ) ≤ 1/(1+prefixEval [3] middleRho)
    apply (le_div_iff₀ (by linarith [hs3.1] : 0 < 1+prefixEval [3] middleRho)).2
    linarith [hs3.2]
  · simp only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one]
    change (1/2:ℝ) ≤ 1/(1+prefixEval [2] middleBeta)
    apply (le_div_iff₀ (by linarith [hs2.1] : 0 < 1+prefixEval [2] middleBeta)).2
    linarith [hs2.2]

private lemma e3_le (c : MiddleCore) (L R : ℝ)
    (hl : ∀ x ∈ Set.Icc (0:ℝ) (1/2), prefixEval c.left x ≤ L)
    (hr : ∀ x ∈ Set.Icc (0:ℝ) (1/2), prefixEval c.right x ≤ R) :
    middleE3 c ≤ 4+L+R := by
  obtain ⟨ha, h3, h2⟩ := small_tails
  unfold middleE3
  split_ifs
  · rw [pe_append, pe_append]
    linarith only [hl _ h3, hr _ h2]
  · rw [pe_append]
    linarith only [hl _ ha, hr _ h3]

private lemma e3_ge (c : MiddleCore) (L R : ℝ)
    (hl : ∀ x ∈ Set.Icc (0:ℝ) (1/2), L ≤ prefixEval c.left x)
    (hr : ∀ x ∈ Set.Icc (0:ℝ) (1/2), R ≤ prefixEval c.right x) :
    4+L+R ≤ middleE3 c := by
  obtain ⟨ha, h3, h2⟩ := small_tails
  unfold middleE3
  split_ifs
  · rw [pe_append, pe_append]
    linarith only [hl _ h3, hr _ h2]
  · rw [pe_append]
    linarith only [hl _ ha, hr _ h3]

private lemma e13_le (c : MiddleCore) (L R : ℝ)
    (hl : ∀ x : ℝ, (1/2:ℝ) ≤ x → prefixEval c.left x ≤ L)
    (hr : ∀ x : ℝ, (1/2:ℝ) ≤ x → prefixEval c.right x ≤ R) :
    middleE13 c ≤ 4+L+R := by
  obtain ⟨hb, h13, h12⟩ := big_tails
  unfold middleE13
  split_ifs
  · rw [pe_append, pe_append]
    linarith only [hl _ h13, hr _ h12]
  · rw [pe_append]
    linarith only [hl _ hb, hr _ h13]

private lemma e13_ge (c : MiddleCore) (L R : ℝ)
    (hl : ∀ x : ℝ, (1/2:ℝ) ≤ x → L ≤ prefixEval c.left x)
    (hr : ∀ x : ℝ, (1/2:ℝ) ≤ x → R ≤ prefixEval c.right x) :
    4+L+R ≤ middleE13 c := by
  obtain ⟨hb, h13, h12⟩ := big_tails
  unfold middleE13
  split_ifs
  · rw [pe_append, pe_append]
    linarith only [hl _ h13, hr _ h12]
  · rw [pe_append]
    linarith only [hl _ hb, hr _ h13]

private lemma even_small (w : List ℕ+) (hw : w.length % 2 = 0) :
    ∀ x ∈ Set.Icc (0:ℝ) (1/2), prefixEval w x ≤ prefixEval w (1/2) := by
  intro x hx
  exact (pe_order w x (1/2) hx.1 (by norm_num) hx.2).1 hw

private lemma odd_small (w : List ℕ+) (hw : w.length % 2 = 1) :
    ∀ x ∈ Set.Icc (0:ℝ) (1/2), prefixEval w (1/2) ≤ prefixEval w x := by
  intro x hx
  exact (pe_order w x (1/2) hx.1 (by norm_num) hx.2).2 hw

private lemma even_big (w : List ℕ+) (hw : w.length % 2 = 0) :
    ∀ x : ℝ, (1/2:ℝ) ≤ x → prefixEval w (1/2) ≤ prefixEval w x := by
  intro x hx
  exact (pe_order w (1/2) x (by norm_num) (by linarith) hx).1 hw

private lemma odd_big (w : List ℕ+) (hw : w.length % 2 = 1) :
    ∀ x : ℝ, (1/2:ℝ) ≤ x → prefixEval w x ≤ prefixEval w (1/2) := by
  intro x hx
  exact (pe_order w (1/2) x (by norm_num) (by linarith) hx).2 hw

private lemma even_append_one_small (w : List ℕ+) (hw : w.length % 2 = 0) :
    ∀ x ∈ Set.Icc (0:ℝ) (1/2), prefixEval w (1/2) ≤ prefixEval (w++[1]) x := by
  intro x hx
  rw [pe_append]
  apply even_big w hw
  simp only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one]
  change (1/2:ℝ) ≤ 1/(1+x)
  apply (le_div_iff₀ (by linarith [hx.1] : 0 < 1+x)).2
  linarith [hx.2]

private lemma odd_append_one_small (w : List ℕ+) (hw : w.length % 2 = 1) :
    ∀ x ∈ Set.Icc (0:ℝ) (1/2), prefixEval (w++[1]) x ≤ prefixEval w (1/2) := by
  intro x hx
  rw [pe_append]
  apply odd_big w hw
  simp only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one]
  change (1/2:ℝ) ≤ 1/(1+x)
  apply (le_div_iff₀ (by linarith [hx.1] : 0 < 1+x)).2
  linarith [hx.2]

private lemma normalized_parity (c : MiddleCore) (k : ℕ)
    (hl : c.left.length % 2 = k) (hr : c.right.length % 2 = k) :
    (middleNormalized c).left.length % 2 = k ∧ (middleNormalized c).right.length % 2 = k := by
  unfold middleNormalized
  split_ifs
  · exact ⟨hl, hr⟩
  · exact ⟨hr, hl⟩

private lemma equal_even (c : MiddleCore)
    (hl : c.left.length % 2 = 0) (hr : c.right.length % 2 = 0) :
    (middleEqualBounds c).1 = middleE3 (middleNormalized c) := by
  unfold middleEqualBounds
  simp only [(normalized_parity c 0 hl hr).1, ite_true]

private lemma equal_odd (c : MiddleCore)
    (hl : c.left.length % 2 = 1) (hr : c.right.length % 2 = 1) :
    (middleEqualBounds c).2 = middleE3 (middleNormalized c) := by
  unfold middleEqualBounds
  simp only [(normalized_parity c 1 hl hr).1, one_ne_zero, ite_false]

private lemma e3_normalized_le (c : MiddleCore) (L R : ℝ)
    (hl : ∀ x ∈ Set.Icc (0:ℝ) (1/2), prefixEval c.left x ≤ L)
    (hr : ∀ x ∈ Set.Icc (0:ℝ) (1/2), prefixEval c.right x ≤ R) :
    middleE3 (middleNormalized c) ≤ 4+L+R := by
  unfold middleNormalized
  split_ifs
  · exact e3_le c L R hl hr
  · have h := e3_le ⟨c.right,c.left⟩ R L hr hl
    linarith only [h]

private lemma e3_normalized_ge (c : MiddleCore) (L R : ℝ)
    (hl : ∀ x ∈ Set.Icc (0:ℝ) (1/2), L ≤ prefixEval c.left x)
    (hr : ∀ x ∈ Set.Icc (0:ℝ) (1/2), R ≤ prefixEval c.right x) :
    4+L+R ≤ middleE3 (middleNormalized c) := by
  unfold middleNormalized
  split_ifs
  · exact e3_ge c L R hl hr
  · have h := e3_ge ⟨c.right,c.left⟩ R L hr hl
    linarith only [h]

private lemma equal_order (c : MiddleCore) (hp : c.left.length % 2 = c.right.length % 2) :
    (middleEqualBounds c).1 ≤ (middleEqualBounds c).2 := by
  let d := middleNormalized c
  have hd : d.left.length % 2 = d.right.length % 2 := by
    dsimp [d, middleNormalized]
    split_ifs
    · exact hp
    · exact hp.symm
  change (if d.left.length % 2 = 0 then (middleE3 d,middleE13 d)
    else (middleE13 d,middleE3 d)).1 ≤
    (if d.left.length % 2 = 0 then (middleE3 d,middleE13 d)
    else (middleE13 d,middleE3 d)).2
  by_cases he : d.left.length % 2 = 0
  · simp only [he, ite_true]
    have hr : d.right.length % 2 = 0 := hd.symm.trans he
    exact le_trans (e3_le d _ _ (even_small _ he) (even_small _ hr))
      (e13_ge d _ _ (even_big _ he) (even_big _ hr))
  · simp only [he, ite_false]
    have ho : d.left.length % 2 = 1 := by omega
    have hr : d.right.length % 2 = 1 := hd.symm.trans ho
    exact le_trans (e13_le d _ _ (odd_big _ ho) (odd_big _ hr))
      (e3_ge d _ _ (odd_small _ ho) (odd_small _ hr))

private lemma mixed_even_order (d : MiddleCore)
    (hl : d.left.length % 2 = 0) (hr : d.right.length % 2 = 1) :
    (middleEqualBounds ⟨d.left,d.right++[1]⟩).1 ≤
      (middleEqualBounds ⟨d.left++[1],d.right⟩).2 := by
  have hl1 : (d.left++[1]).length % 2 = 1 := by simp only [List.length_append, List.length_singleton]; omega
  have hr1 : (d.right++[1]).length % 2 = 0 := by simp only [List.length_append, List.length_singleton]; omega
  rw [equal_even ⟨d.left,d.right++[1]⟩ hl hr1, equal_odd ⟨d.left++[1],d.right⟩ hl1 hr]
  exact le_trans
    (e3_normalized_le ⟨d.left,d.right++[1]⟩ _ _ (even_small _ hl) (odd_append_one_small _ hr))
    (e3_normalized_ge ⟨d.left++[1],d.right⟩ _ _ (even_append_one_small _ hl) (odd_small _ hr))

private lemma mixed_odd_order (d : MiddleCore)
    (hl : d.left.length % 2 = 1) (hr : d.right.length % 2 = 0) :
    (middleEqualBounds ⟨d.left++[1],d.right⟩).1 ≤
      (middleEqualBounds ⟨d.left,d.right++[1]⟩).2 := by
  have hl1 : (d.left++[1]).length % 2 = 0 := by simp only [List.length_append, List.length_singleton]; omega
  have hr1 : (d.right++[1]).length % 2 = 1 := by simp only [List.length_append, List.length_singleton]; omega
  rw [equal_even ⟨d.left++[1],d.right⟩ hl1 hr, equal_odd ⟨d.left,d.right++[1]⟩ hl hr1]
  exact le_trans
    (e3_normalized_le ⟨d.left++[1],d.right⟩ _ _ (odd_append_one_small _ hl) (even_small _ hr))
    (e3_normalized_ge ⟨d.left,d.right++[1]⟩ _ _ (odd_small _ hl) (even_append_one_small _ hr))

end FreimanM8EndpointOrder20260910

open FreimanM8EndpointOrder20260910

theorem solution :
    ∀ c : MiddleCore, middleRegular c → (middleBounds c).1 ≤ (middleBounds c).2 := by
  intro c _
  unfold middleBounds
  dsimp only
  split_ifs with hsame he
  · exact equal_order _ hsame
  · exact mixed_even_order _ he (by omega)
  · exact mixed_odd_order _ (by omega) (by omega)

#print axioms solution
