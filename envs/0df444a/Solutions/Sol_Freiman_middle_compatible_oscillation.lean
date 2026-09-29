-- Prove2me | solution 1 for Freiman.middle_compatible_oscillation
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T10:34:33.917968+00:00
-- url     : https://prove2.me/submissions/ab64b8f1-fc49-4079-bc1e-f3aac9d45fd4

import Theorems.Thm_Freiman_cf_convergence
import Theorems.Thm_Freiman_background_unrestricted_tail
import Theorems.Thm_Freiman_cfValue_prefix
import Mathlib.Data.List.GetD
import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

open Freiman

namespace M8Sep10CompatibleOscillation

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

private lemma unrestricted_interval (b : ℕ → ℕ+) (hb : ∀ n, (b n : ℕ) ≤ 3) :
    cfValue b ∈ Set.Icc middleAlpha middleBeta := by
  have hu : cfValue b ≤ middleBeta := background_unrestricted_tail b hb
  have hus : cfValue (fun n => b (n+1)) ≤ middleBeta :=
    background_unrestricted_tail (fun n => b (n+1)) (fun n => hb (n+1))
  have hp := (cf_convergence (fun n => b (n+1))).2.2.1
  have hd : (0:ℝ) < ((b 0 : ℕ) : ℝ) := by exact_mod_cast (b 0).pos
  have hd3 : ((b 0 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hb 0
  have hβ : 0 < middleBeta := by linarith
  have hα : middleAlpha = 1/(3+middleBeta) := by
    apply (eq_div_iff (by linarith : 3+middleBeta ≠ 0)).mpr
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ 21 by norm_num)
    dsimp only [middleAlpha, middleBeta]
    nlinarith
  refine ⟨?_, hu⟩
  rw [(cf_convergence b).2.2.2.2, hα]
  exact one_div_le_one_div_of_le (by linarith : 0 < ((b 0 : ℕ) : ℝ) + cfValue (fun n => b (n+1)))
    (by linarith)

private lemma fixed_prefix (w : List ℕ+) (b : ℕ → ℕ+)
    (h : ∀ n, n < w.length → b n = w.getD n 1) :
    cfValue b = prefixEval w (cfValue (fun n => b (w.length+n))) := by
  rw [cfValue_prefix b w.length]
  have hw : (List.range w.length).map b = w := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range]
    · intro n hn hn'
      simp only [List.getElem_map, List.getElem_range]
      rw [h n hn', List.getD_eq_getElem _ _ hn']
  rw [hw]

private lemma compatible_cylinder (c : MiddleCore) (a : ℤ → ℕ+)
    (ha : middleCompatible c a) :
    cylinderLo c ≤ localValue a 0 ∧ localValue a 0 ≤ cylinderHi c := by
  let bL : ℕ → ℕ+ := fun n => a (-(n:ℤ)-1)
  let bR : ℕ → ℕ+ := fun n => a ((n:ℤ)+1)
  have hleft := fixed_prefix c.left bL ha.2.1
  have hright := fixed_prefix c.right bR ha.2.2.1
  have hLt : cfValue (fun n => bL (c.left.length+n)) ∈ Set.Icc middleAlpha middleBeta := by
    apply unrestricted_interval
    intro n
    exact ha.2.2.2.1 (c.left.length+n) (by omega)
  have hRt : cfValue (fun n => bR (c.right.length+n)) ∈ Set.Icc middleAlpha middleBeta := by
    apply unrestricted_interval
    intro n
    exact ha.2.2.2.2 (c.right.length+n) (by omega)
  have hL := pe_interval c.left _ hLt
  have hR := pe_interval c.right _ hRt
  have hlocal : localValue a 0 = 4+cfValue bL+cfValue bR := by
    norm_num [localValue, ha.1, bL, bR]
  rw [hlocal, hleft, hright]
  constructor <;> dsimp only [cylinderLo, cylinderHi] <;>
    linarith only [hL.1, hL.2, hR.1, hR.2]

end M8Sep10CompatibleOscillation

theorem solution :
    ∀ (c : MiddleCore) (a : ℤ→ℕ+) (t : ℝ), middleRegular c → middleCompatible c a → t∈middleCover c →
      |localValue a 0-t| ≤ middleWidth c.left+middleWidth c.right := by
  intro c a t _ ha ht
  have hc := M8Sep10CompatibleOscillation.bounds_cylinder c
  have hv := M8Sep10CompatibleOscillation.compatible_cylinder c a ha
  have h₁ := M8Sep10CompatibleOscillation.word_width c.left
  have h₂ := M8Sep10CompatibleOscillation.word_width c.right
  have htl := hc.1.trans ht.1
  have htr := ht.2.trans hc.2
  rw [abs_le]
  dsimp only [M8Sep10CompatibleOscillation.cylinderLo, M8Sep10CompatibleOscillation.cylinderHi] at hv htl htr
  constructor <;> linarith only [hv.1, hv.2, htl, htr, h₁, h₂]

#print axioms solution
