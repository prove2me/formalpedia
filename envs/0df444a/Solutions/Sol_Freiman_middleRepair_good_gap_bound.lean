-- Prove2me | solution 1 for Freiman.middleRepair_good_gap_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T10:05:16.709418+00:00
-- url     : https://prove2.me/submissions/240bffc4-8084-4912-9c30-94aca047d2fc

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

open Freiman

namespace M8Sep10GoodGap

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

private theorem cd_eq (w : List ℕ+) : middleCD w =
    List.foldl (fun z (a : ℕ) => (z.2, z.1 + ((a : ℕ) : ℝ) * z.2)) (0, 1) (w.map PNat.val) := by
  have hbind : (do let a ← w; pure (a : ℕ)) = w.map PNat.val := by
    induction w with
    | nil => rfl
    | cons a w ih => simpa using ih
  unfold middleCD
  rw [hbind]

private theorem cd_append (w : List ℕ+) (a : ℕ+) :
    middleCD (w ++ [a]) = ((middleCD w).2, (middleCD w).1 + ((a : ℕ) : ℝ) * (middleCD w).2) := by
  rw [cd_eq, cd_eq, List.map_append, List.foldl_append]
  simp

private theorem cd_pos : ∀ w : List ℕ+, 0 ≤ (middleCD w).1 ∧ 0 < (middleCD w).2 := by
  intro w
  induction w using List.reverseRecOn with
  | nil => rw [cd_eq]; constructor <;> norm_num
  | append_singleton w a ih =>
      rw [cd_append]
      have ha : (0:ℝ) < ((a : ℕ) : ℝ) := by exact_mod_cast a.pos
      exact ⟨le_of_lt ih.2, by nlinarith [ih.1, ih.2]⟩

/-- The Möbius derivative identity for the continuant pair of a word. -/
private theorem diff_formula : ∀ (w : List ℕ+) (x y : ℝ), 0 ≤ x → 0 ≤ y →
    |prefixEval w y - prefixEval w x| *
      (((middleCD w).2 + (middleCD w).1 * x) * ((middleCD w).2 + (middleCD w).1 * y))
      = |y - x| := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro x y hx hy; rw [cd_eq]; simp [prefixEval]
  | append_singleton w a ih =>
      intro x y hx hy
      obtain ⟨hc, hd⟩ := cd_pos w
      have ha : (1:ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast a.one_le
      have hax : (0:ℝ) < ((a : ℕ) : ℝ) + x := by linarith
      have hay : (0:ℝ) < ((a : ℕ) : ℝ) + y := by linarith
      have hpos : (0:ℝ) < (((a : ℕ) : ℝ) + x) * (((a : ℕ) : ℝ) + y) := mul_pos hax hay
      have hx' : (0:ℝ) ≤ 1 / (((a : ℕ) : ℝ) + x) := by positivity
      have hy' : (0:ℝ) ≤ 1 / (((a : ℕ) : ℝ) + y) := by positivity
      have esingle : ∀ t : ℝ, prefixEval [a] t = 1 / (((a : ℕ) : ℝ) + t) := by
        intro t; simp [prefixEval]
      have ex : prefixEval (w ++ [a]) x = prefixEval w (1 / (((a : ℕ) : ℝ) + x)) := by
        rw [pe_append, esingle]
      have ey : prefixEval (w ++ [a]) y = prefixEval w (1 / (((a : ℕ) : ℝ) + y)) := by
        rw [pe_append, esingle]
      have hIH := ih (1 / (((a : ℕ) : ℝ) + x)) (1 / (((a : ℕ) : ℝ) + y)) hx' hy'
      have hL : ((middleCD w).2 + (middleCD w).1 * (1 / (((a : ℕ) : ℝ) + x))) *
          ((middleCD w).2 + (middleCD w).1 * (1 / (((a : ℕ) : ℝ) + y)))
          = (((middleCD w).1 + ((a : ℕ) : ℝ) * (middleCD w).2 + (middleCD w).2 * x) *
             ((middleCD w).1 + ((a : ℕ) : ℝ) * (middleCD w).2 + (middleCD w).2 * y))
            / ((((a : ℕ) : ℝ) + x) * (((a : ℕ) : ℝ) + y)) := by
        field_simp
        try ring
      have hR : 1 / (((a : ℕ) : ℝ) + y) - 1 / (((a : ℕ) : ℝ) + x)
          = (x - y) / ((((a : ℕ) : ℝ) + x) * (((a : ℕ) : ℝ) + y)) := by
        field_simp
        try ring
      rw [hL, hR, abs_div, abs_of_pos hpos] at hIH
      rw [ex, ey, cd_append]
      simp only
      have hfin : |prefixEval w (1 / (((a : ℕ) : ℝ) + y))
            - prefixEval w (1 / (((a : ℕ) : ℝ) + x))| *
          (((middleCD w).1 + ((a : ℕ) : ℝ) * (middleCD w).2 + (middleCD w).2 * x) *
           ((middleCD w).1 + ((a : ℕ) : ℝ) * (middleCD w).2 + (middleCD w).2 * y))
          = |x - y| := by
        field_simp at hIH
        linarith [hIH]
      rw [abs_sub_comm y x]
      rw [← hfin]

/-- Target: `Freiman.middle_width_identity`. -/
private theorem width_identity :
    ∀ w : List ℕ+,
      middleWidth w = (middleBeta-middleAlpha) /
        ((middleCD w).2^2 * (1+middleParameter w*middleAlpha) * (1+middleParameter w*middleBeta)) := by
  intro w
  obtain ⟨hc, hd⟩ := cd_pos w
  have h3 : (3 : ℝ) < Real.sqrt 21 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hα : 0 ≤ middleAlpha := by unfold middleAlpha; linarith
  have hβ : 0 ≤ middleBeta := by unfold middleBeta; linarith
  have hlt : middleAlpha < middleBeta := by unfold middleAlpha middleBeta; linarith
  have hkey := diff_formula w middleAlpha middleBeta hα hβ
  have hdα : (0:ℝ) < (middleCD w).2 + (middleCD w).1 * middleAlpha := by nlinarith
  have hdβ : (0:ℝ) < (middleCD w).2 + (middleCD w).1 * middleBeta := by nlinarith
  have habs : |middleBeta - middleAlpha| = middleBeta - middleAlpha := by
    rw [abs_of_pos (by linarith)]
  rw [habs] at hkey
  have hden : (middleCD w).2^2 * (1+middleParameter w*middleAlpha) * (1+middleParameter w*middleBeta)
      = ((middleCD w).2 + (middleCD w).1 * middleAlpha) *
        ((middleCD w).2 + (middleCD w).1 * middleBeta) := by
    unfold middleParameter
    field_simp
    try ring
  unfold middleWidth
  rw [hden, eq_div_iff (by positivity)]
  exact hkey

private lemma alpha_beta_bounds :
    (1/4:ℝ) ≤ middleAlpha ∧ middleAlpha ≤ (4/15:ℝ) ∧
    (79/100:ℝ) ≤ middleBeta ∧ middleBeta ≤ (4/5:ℝ) ∧
    0 ≤ middleRho ∧ middleRho ≤ (3/4:ℝ) := by
  have hlow : (229/50:ℝ) ≤ Real.sqrt 21 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hhigh : Real.sqrt 21 ≤ (23/5:ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hrlow : (1:ℝ) ≤ Real.sqrt 3 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hrhigh : Real.sqrt 3 ≤ (7/4:ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  dsimp only [middleAlpha, middleBeta, middleRho]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private lemma beta_one_alpha : middleBeta * (1 + middleAlpha) = 1 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 21 by norm_num)
  dsimp only [middleAlpha, middleBeta]
  nlinarith

private lemma one_maps_interval (x : ℝ) (hx : x ∈ Set.Icc middleAlpha middleBeta) :
    prefixEval [1] x ∈ Set.Icc middleAlpha middleBeta := by
  obtain ⟨ha, ha', hb, hb', _, _⟩ := alpha_beta_bounds
  simp only [prefixEval, PNat.val_ofNat, Nat.cast_one]
  change middleAlpha ≤ 1 / (1+x) ∧ 1 / (1+x) ≤ middleBeta
  have hx0 : 0 < 1+x := by linarith [hx.1]
  constructor
  · apply (le_div_iff₀ hx0).2
    nlinarith [hx.2]
  · apply (div_le_iff₀ hx0).2
    have he := beta_one_alpha
    nlinarith [hx.1]

private lemma endpoint_tails :
    prefixEval [3] middleRho ∈ Set.Icc middleAlpha middleBeta ∧
    prefixEval [2] middleBeta ∈ Set.Icc middleAlpha middleBeta ∧
    prefixEval [1,3] middleRho ∈ Set.Icc middleAlpha middleBeta ∧
    prefixEval [1,2] middleBeta ∈ Set.Icc middleAlpha middleBeta := by
  obtain ⟨ha, ha', hb, hb', hr, hr'⟩ := alpha_beta_bounds
  have h3 : prefixEval [3] middleRho ∈ Set.Icc middleAlpha middleBeta := by
    change middleAlpha ≤ 1/(3+middleRho) ∧ 1/(3+middleRho) ≤ middleBeta
    have hp : 0 < 3+middleRho := by linarith
    constructor
    · apply (le_div_iff₀ hp).2
      nlinarith
    · apply (div_le_iff₀ hp).2
      nlinarith
  have h2 : prefixEval [2] middleBeta ∈ Set.Icc middleAlpha middleBeta := by
    change middleAlpha ≤ 1/(2+middleBeta) ∧ 1/(2+middleBeta) ≤ middleBeta
    have hp : 0 < 2+middleBeta := by linarith
    constructor
    · apply (le_div_iff₀ hp).2
      nlinarith
    · apply (div_le_iff₀ hp).2
      nlinarith
  refine ⟨h3, h2, ?_, ?_⟩
  · exact one_maps_interval _ h3
  · exact one_maps_interval _ h2

private noncomputable def wordLo (w : List ℕ+) : ℝ :=
  min (prefixEval w middleAlpha) (prefixEval w middleBeta)
private noncomputable def wordHi (w : List ℕ+) : ℝ :=
  max (prefixEval w middleAlpha) (prefixEval w middleBeta)
private noncomputable def cylinderLo (c : MiddleCore) : ℝ :=
  4 + wordLo c.left + wordLo c.right
private noncomputable def cylinderHi (c : MiddleCore) : ℝ :=
  4 + wordHi c.left + wordHi c.right

private lemma pe_interval (w : List ℕ+) (x : ℝ) (hx : x ∈ Set.Icc middleAlpha middleBeta) :
    wordLo w ≤ prefixEval w x ∧ prefixEval w x ≤ wordHi w := by
  obtain ⟨ha, ha', hb, hb', _, _⟩ := alpha_beta_bounds
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hax := pe_order w middleAlpha x (by linarith) hx0 hx.1
  have hxb := pe_order w x middleBeta hx0 (by linarith) hx.2
  by_cases he : w.length % 2 = 0
  · exact ⟨(min_le_left _ _).trans (hax.1 he), (hxb.1 he).trans (le_max_right _ _)⟩
  · have ho : w.length % 2 = 1 := by omega
    exact ⟨(min_le_right _ _).trans (hxb.2 ho), (hax.2 ho).trans (le_max_left _ _)⟩

private lemma e3_cylinder (c : MiddleCore) :
    cylinderLo c ≤ middleE3 c ∧ middleE3 c ≤ cylinderHi c := by
  obtain ⟨h3, h2, _, _⟩ := endpoint_tails
  have hab : middleAlpha ≤ middleBeta := by
    obtain ⟨ha, ha', hb, _, _, _⟩ := alpha_beta_bounds
    linarith
  unfold middleE3
  split_ifs
  · rw [pe_append, pe_append]
    have hl := pe_interval c.left _ h3
    have hr := pe_interval c.right _ h2
    constructor <;> dsimp only [cylinderLo, cylinderHi] <;> linarith only [hl.1, hl.2, hr.1, hr.2]
  · rw [pe_append]
    have hl := pe_interval c.left middleAlpha ⟨le_rfl, hab⟩
    have hr := pe_interval c.right _ h3
    constructor <;> dsimp only [cylinderLo, cylinderHi] <;> linarith only [hl.1, hl.2, hr.1, hr.2]

private lemma e13_cylinder (c : MiddleCore) :
    cylinderLo c ≤ middleE13 c ∧ middleE13 c ≤ cylinderHi c := by
  obtain ⟨_, _, h13, h12⟩ := endpoint_tails
  have hab : middleAlpha ≤ middleBeta := by
    obtain ⟨ha, ha', hb, _, _, _⟩ := alpha_beta_bounds
    linarith
  unfold middleE13
  split_ifs
  · rw [pe_append, pe_append]
    have hl := pe_interval c.left _ h13
    have hr := pe_interval c.right _ h12
    constructor <;> dsimp only [cylinderLo, cylinderHi] <;> linarith only [hl.1, hl.2, hr.1, hr.2]
  · rw [pe_append]
    have hl := pe_interval c.left middleBeta ⟨hab, le_rfl⟩
    have hr := pe_interval c.right _ h13
    constructor <;> dsimp only [cylinderLo, cylinderHi] <;> linarith only [hl.1, hl.2, hr.1, hr.2]

private lemma cylinder_normalized (c : MiddleCore) :
    cylinderLo (middleNormalized c) = cylinderLo c ∧
      cylinderHi (middleNormalized c) = cylinderHi c := by
  unfold middleNormalized
  split_ifs
  · exact ⟨rfl, rfl⟩
  · constructor <;> dsimp only [cylinderLo, cylinderHi] <;> ring

private lemma equal_cylinder (c : MiddleCore) :
    cylinderLo c ≤ (middleEqualBounds c).1 ∧
      (middleEqualBounds c).2 ≤ cylinderHi c := by
  have h3 := e3_cylinder (middleNormalized c)
  have h13 := e13_cylinder (middleNormalized c)
  rw [(cylinder_normalized c).1, (cylinder_normalized c).2] at h3 h13
  unfold middleEqualBounds
  dsimp only
  split_ifs
  · exact ⟨h3.1, h13.2⟩
  · exact ⟨h13.1, h3.2⟩

private lemma append_one_word (w : List ℕ+) :
    wordLo w ≤ wordLo (w++[1]) ∧ wordHi (w++[1]) ≤ wordHi w := by
  have hab : middleAlpha ≤ middleBeta := by
    obtain ⟨ha, ha', hb, _, _, _⟩ := alpha_beta_bounds
    linarith
  have ha := pe_interval w _ (one_maps_interval middleAlpha ⟨le_rfl, hab⟩)
  have hb := pe_interval w _ (one_maps_interval middleBeta ⟨hab, le_rfl⟩)
  change wordLo w ≤ min (prefixEval (w++[1]) middleAlpha) (prefixEval (w++[1]) middleBeta) ∧
    max (prefixEval (w++[1]) middleAlpha) (prefixEval (w++[1]) middleBeta) ≤ wordHi w
  rw [pe_append, pe_append]
  exact ⟨le_min ha.1 hb.1, max_le ha.2 hb.2⟩

private lemma bounds_cylinder (c : MiddleCore) :
    cylinderLo c ≤ (middleBounds c).1 ∧ (middleBounds c).2 ≤ cylinderHi c := by
  let d := middleNormalized c
  have hn := cylinder_normalized c
  have h01 := equal_cylinder (⟨d.left, d.right++[1]⟩ : MiddleCore)
  have h10 := equal_cylinder (⟨d.left++[1], d.right⟩ : MiddleCore)
  have hl := append_one_word d.left
  have hr := append_one_word d.right
  change cylinderLo c ≤ (if d.left.length%2=d.right.length%2 then middleEqualBounds d
    else if d.left.length%2=0 then
      ((middleEqualBounds ⟨d.left,d.right++[1]⟩).1, (middleEqualBounds ⟨d.left++[1],d.right⟩).2)
    else ((middleEqualBounds ⟨d.left++[1],d.right⟩).1, (middleEqualBounds ⟨d.left,d.right++[1]⟩).2)).1 ∧
    (if d.left.length%2=d.right.length%2 then middleEqualBounds d
    else if d.left.length%2=0 then
      ((middleEqualBounds ⟨d.left,d.right++[1]⟩).1, (middleEqualBounds ⟨d.left++[1],d.right⟩).2)
    else ((middleEqualBounds ⟨d.left++[1],d.right⟩).1, (middleEqualBounds ⟨d.left,d.right++[1]⟩).2)).2 ≤ cylinderHi c
  rw [← hn.1, ← hn.2]
  change cylinderLo d ≤ _ ∧ _ ≤ cylinderHi d
  split_ifs
  · exact equal_cylinder d
  · dsimp only [cylinderLo, cylinderHi] at h01 h10 ⊢
    constructor <;> linarith only [h01.1, h01.2, h10.1, h10.2, hl.1, hl.2, hr.1, hr.2]
  · dsimp only [cylinderLo, cylinderHi] at h01 h10 ⊢
    constructor <;> linarith only [h01.1, h01.2, h10.1, h10.2, hl.1, hl.2, hr.1, hr.2]

private lemma word_width (w : List ℕ+) : wordHi w - wordLo w = middleWidth w := by
  unfold wordHi wordLo middleWidth
  by_cases h : prefixEval w middleAlpha ≤ prefixEval w middleBeta
  · rw [max_eq_right h, min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
  · have h' : prefixEval w middleBeta ≤ prefixEval w middleAlpha := le_of_not_ge h
    rw [max_eq_left h', min_eq_right h', abs_of_nonpos (sub_nonpos.mpr h')]
    ring

private lemma word_even (w : List ℕ+) (hw : w.length % 2 = 0) :
    wordLo w = prefixEval w middleAlpha ∧ wordHi w = prefixEval w middleBeta := by
  obtain ⟨ha, ha', hb, _, _, _⟩ := alpha_beta_bounds
  have h := (pe_order w middleAlpha middleBeta (by linarith) (by linarith) (by linarith)).1 hw
  exact ⟨min_eq_left h, max_eq_right h⟩

private lemma word_odd (w : List ℕ+) (hw : w.length % 2 = 1) :
    wordLo w = prefixEval w middleBeta ∧ wordHi w = prefixEval w middleAlpha := by
  obtain ⟨ha, ha', hb, _, _, _⟩ := alpha_beta_bounds
  have h := (pe_order w middleAlpha middleBeta (by linarith) (by linarith) (by linarith)).2 hw
  exact ⟨min_eq_right h, max_eq_left h⟩

private lemma child_cylinder (c : MiddleCore) (u : List ℕ+) (t : ℝ)
    (ht : t ∈ middleCover (middleRepairChild c u [])) :
    4 + wordLo ((middleNormalized c).left++u) + wordLo (middleNormalized c).right ≤ t ∧
      t ≤ 4 + wordHi ((middleNormalized c).left++u) + wordHi (middleNormalized c).right := by
  have h := bounds_cylinder (middleRepairChild c u [])
  have hc : cylinderLo (middleRepairChild c u []) ≤ t ∧
      t ≤ cylinderHi (middleRepairChild c u []) := ⟨h.1.trans ht.1, ht.2.trans h.2⟩
  dsimp only [middleRepairChild] at hc
  rw [(cylinder_normalized _).1, (cylinder_normalized _).2] at hc
  simpa only [cylinderLo, cylinderHi, middleRepairRawChild, List.append_nil] using hc

private lemma gap_base :
    0 ≤ prefixEval [2] middleAlpha ∧ 0 ≤ prefixEval [1] middleBeta ∧
      prefixEval [2] middleAlpha ≤ prefixEval [1] middleBeta := by
  obtain ⟨ha, _, hb, hb', _, _⟩ := alpha_beta_bounds
  have hp : 0 < 2+middleAlpha := by linarith
  have hq : 0 < 1+middleBeta := by linarith
  simp only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one]
  refine ⟨(one_div_pos.mpr hp).le, (one_div_pos.mpr hq).le, ?_⟩
  exact one_div_le_one_div_of_le hq (by linarith)

private lemma gap_from_common (c : MiddleCore) (hg : middleRepairGood c) :
    |prefixEval (middleNormalized c).left (prefixEval [1] middleBeta) -
      prefixEval (middleNormalized c).left (prefixEval [2] middleAlpha)| ≤
      middleWidth (middleNormalized c).right := by
  obtain ⟨t, ht₁, ht₂⟩ := hg
  have h₁ := child_cylinder c [1] t ht₁
  have h₂ := child_cylinder c [2] t ht₂
  have ho := pe_order (middleNormalized c).left (prefixEval [2] middleAlpha)
    (prefixEval [1] middleBeta) gap_base.1 gap_base.2.1 gap_base.2.2
  have hw := word_width (middleNormalized c).right
  by_cases he : (middleNormalized c).left.length % 2 = 0
  · have he₁ : ((middleNormalized c).left++[1]).length % 2 = 1 := by
      simp only [List.length_append, List.length_singleton]; omega
    have he₂ : ((middleNormalized c).left++[2]).length % 2 = 1 := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [(word_odd _ he₁).1, pe_append] at h₁
    rw [(word_odd _ he₂).2, pe_append] at h₂
    rw [abs_of_nonneg (sub_nonneg.mpr (ho.1 he))]
    linarith only [h₁.1, h₂.2, hw]
  · have hop : (middleNormalized c).left.length % 2 = 1 := by omega
    have he₁ : ((middleNormalized c).left++[1]).length % 2 = 0 := by
      simp only [List.length_append, List.length_singleton]; omega
    have he₂ : ((middleNormalized c).left++[2]).length % 2 = 0 := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [(word_even _ he₁).2, pe_append] at h₁
    rw [(word_even _ he₂).1, pe_append] at h₂
    rw [abs_of_nonpos (sub_nonpos.mpr (ho.2 hop))]
    linarith only [h₂.1, h₁.2, hw]

private lemma gap_identity (w : List ℕ+) :
    middleGapFraction (middleParameter w) * middleWidth w =
      |prefixEval w (prefixEval [1] middleBeta) - prefixEval w (prefixEval [2] middleAlpha)| := by
  let u := prefixEval [2] middleAlpha
  let v := prefixEval [1] middleBeta
  let p := middleParameter w
  obtain ⟨hc, hd⟩ := cd_pos w
  obtain ⟨ha, ha', hb, hb', _, _⟩ := alpha_beta_bounds
  have hα : 0 ≤ middleAlpha := by linarith
  have hβ : 0 ≤ middleBeta := by linarith
  have hβα : 0 < middleBeta-middleAlpha := by linarith
  have hu : 0 ≤ u := gap_base.1
  have hv : 0 ≤ v := gap_base.2.1
  have huv : u ≤ v := gap_base.2.2
  have hp : 0 ≤ p := by dsimp only [p, middleParameter]; positivity
  have hA : 0 < 1+p*middleAlpha := by positivity
  have hB : 0 < 1+p*middleBeta := by positivity
  have hU : 0 < 1+p*u := by positivity
  have hV : 0 < 1+p*v := by positivity
  have hden : ((middleCD w).2+(middleCD w).1*u)*((middleCD w).2+(middleCD w).1*v) =
      (middleCD w).2^2*(1+p*u)*(1+p*v) := by
    dsimp only [p, middleParameter]
    field_simp
    <;> ring
  have hg := diff_formula w u v hu hv
  rw [abs_of_nonneg (sub_nonneg.mpr huv), hden] at hg
  have hd' : (middleCD w).2^2*(1+p*u)*(1+p*v) ≠ 0 := by positivity
  have he : |prefixEval w v - prefixEval w u| =
      (v-u)/((middleCD w).2^2*(1+p*u)*(1+p*v)) := (eq_div_iff hd').mpr hg
  change middleGapFraction p * middleWidth w = |prefixEval w v - prefixEval w u|
  rw [he, width_identity w]
  change (v-u)/(middleBeta-middleAlpha) * ((1+p*middleAlpha)*(1+p*middleBeta)) /
      ((1+p*u)*(1+p*v)) * ((middleBeta-middleAlpha) /
      ((middleCD w).2^2*(1+p*middleAlpha)*(1+p*middleBeta))) =
      (v-u)/((middleCD w).2^2*(1+p*u)*(1+p*v))
  field_simp [ne_of_gt hβα, ne_of_gt hd, ne_of_gt hA, ne_of_gt hB, ne_of_gt hU, ne_of_gt hV]
  <;> ring

end M8Sep10GoodGap

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c →
      middleGapFraction (middleParameter (middleNormalized c).left) * middleWidth (middleNormalized c).left ≤
        middleWidth (middleNormalized c).right := by
  intro c _ hg
  rw [M8Sep10GoodGap.gap_identity]
  exact M8Sep10GoodGap.gap_from_common c hg

#print axioms solution
