-- Prove2me | solution 1 for Freiman.middleRepair_j_contact_from_threshold
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T10:25:19.738654+00:00
-- url     : https://prove2.me/submissions/d7f8c059-b9b7-4329-8d8b-31830d7b2268

import Definitions.Def_Freiman_middleRepair
import Theorems.Thm_Freiman_middle_width_identity
import Theorems.Thm_Freiman_middle_continuant_growth
import Theorems.Thm_Freiman_prefixEval_difference
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

open Freiman

namespace M8Sep10JContactFull

private theorem cd_append (w : List ℕ+) (a : ℕ+) :
    middleCD (w++[a]) = ((middleCD w).2,(middleCD w).1+((a:ℕ):ℝ)*(middleCD w).2) := by
  simp [middleCD, List.foldl_append]

private theorem local_continuant_append (w : List ℕ+) (a : ℕ+) :
    wordContinuantData (w ++ [a]) =
      ((wordContinuantP w, (a:ℕ)*wordContinuantP w+wordContinuantPrevP w),
       (wordContinuantQ w, (a:ℕ)*wordContinuantQ w+wordContinuantPrevQ w)) := by
  simp [wordContinuantData, wordContinuantP, wordContinuantPrevP, wordContinuantQ,
    wordContinuantPrevQ, List.foldl_append]

private theorem cd_coordinates (w : List ℕ+) :
    middleCD w = ((wordContinuantPrevQ w : ℝ),(wordContinuantQ w : ℝ)) := by
  induction w using List.reverseRecOn with
  | nil => norm_num [middleCD, wordContinuantPrevQ, wordContinuantQ, wordContinuantData]
  | append_singleton w a ih =>
    rw [cd_append, ih]
    simp only [wordContinuantQ, wordContinuantPrevQ, local_continuant_append]
    push_cast
    congr 1
    ring

private theorem pe_unit (w : List ℕ+) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    prefixEval w x ∈ Set.Icc (0:ℝ) 1 := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.one_le
    change 0 ≤ 1/(((a:ℕ):ℝ)+prefixEval w x) ∧ 1/(((a:ℕ):ℝ)+prefixEval w x) ≤ 1
    have hpos : 0 < ((a:ℕ):ℝ)+prefixEval w x := by linarith [ih.1]
    constructor
    · exact le_of_lt (div_pos (by norm_num) hpos)
    · apply (div_le_iff₀ hpos).2
      linarith [ih.1]

private theorem ab_unit : middleAlpha ∈ Set.Icc (0:ℝ) 1 ∧
    middleBeta ∈ Set.Icc (0:ℝ) 1 ∧ middleAlpha < middleBeta := by
  have h4 : (4:ℝ) ≤ Real.sqrt 21 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h5 : Real.sqrt 21 ≤ (5:ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  dsimp [middleAlpha, middleBeta]
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  · linarith

private theorem pe_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u++v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, prefixEval, ih]

private theorem width_pos (w : List ℕ+) : 0 < middleWidth w := by
  have hg := middle_continuant_growth w
  have hp := hg.1
  have hD := hg.2.1
  have hA := ab_unit.1.1
  have hB := ab_unit.2.1.1
  rw [middle_width_identity]
  exact div_pos (sub_pos.mpr ab_unit.2.2) (by positivity)

private theorem width_append (w v : List ℕ+) : middleWidth (w++v) =
    middleWidth v / ((middleCD w).2^2 *
      (1+middleParameter w*prefixEval v middleAlpha) *
      (1+middleParameter w*prefixEval v middleBeta)) := by
  have ha := pe_unit v middleAlpha ab_unit.1
  have hb := pe_unit v middleBeta ab_unit.2.1
  have hD := (middle_continuant_growth w).2.1
  have hc := congrArg Prod.fst (cd_coordinates w)
  have hd := congrArg Prod.snd (cd_coordinates w)
  dsimp only at hc hd
  calc
    middleWidth (w++v) = middleWidth v /
        (((wordContinuantQ w:ℝ) + prefixEval v middleBeta*wordContinuantPrevQ w) *
         ((wordContinuantQ w:ℝ) + prefixEval v middleAlpha*wordContinuantPrevQ w)) := by
      simpa only [middleWidth, pe_append] using prefixEval_difference w _ _ hb ha
    _ = _ := by
      rw [← hc, ← hd]
      congr 1
      unfold middleParameter
      field_simp [ne_of_gt hD]

private theorem ratio_append (u w v : List ℕ+) :
    middleWidth (u++v) / middleWidth (w++v) =
      middleH (middleParameter u) (middleParameter w) (prefixEval v middleAlpha) (prefixEval v middleBeta) /
      ((middleCD u).2^2 / (middleCD w).2^2) := by
  have hu := middle_continuant_growth u
  have hw := middle_continuant_growth w
  have hup := hu.1
  have hwp := hw.1
  have ha := (pe_unit v middleAlpha ab_unit.1).1
  have hb := (pe_unit v middleBeta ab_unit.2.1).1
  have hdv := width_pos v
  rw [width_append, width_append]
  unfold middleH
  field_simp (disch := positivity)
  <;> ring



private theorem f3beta : prefixEval [3] middleBeta = middleAlpha := by
  have hsq : Real.sqrt (21:ℝ)^2 = 21 := Real.sq_sqrt (by norm_num)
  have hd : 0 < 3+middleBeta := by linarith [ab_unit.2.1.1]
  change 1/(3+middleBeta) = middleAlpha
  apply (div_eq_iff (ne_of_gt hd)).2
  unfold middleAlpha middleBeta
  nlinarith


private theorem hStar_value (p s : ℝ) : middleHStar p s =
    (5/7:ℝ)*middleH p s (prefixEval [3] middleAlpha) (prefixEval [3] middleBeta) := by
  rw [f3beta]
  unfold middleHStar middleScalarThreshold middleH
  ring


private theorem q_pos (c : MiddleCore) : 0 < middleQ c := by
  have hl := (middle_continuant_growth (middleNormalized c).left).2.1
  have hr := (middle_continuant_growth (middleNormalized c).right).2.1
  exact div_pos (sq_pos_of_pos hl) (sq_pos_of_pos hr)


private theorem short1_iff (c : MiddleCore) : middleShort c 1 ↔
    middleHStar (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) ≤ middleQ c := by
  rw [hStar_value]
  change middleWidth ((middleNormalized c).left++[3]) ≤
    (7/5:ℝ)*middleWidth ((middleNormalized c).right++[3]) ↔ _
  rw [← div_le_iff₀ (width_pos ((middleNormalized c).right++[3])), ratio_append]
  change _ /middleQ c ≤ (7/5:ℝ) ↔ _
  rw [div_le_iff₀ (q_pos c)]
  constructor <;> intro h <;> nlinarith only [h]


private theorem normalized_regular (c : MiddleCore) (hc : middleRegular c) :
    middleRegular (middleNormalized c) := by
  unfold middleNormalized
  split_ifs
  · exact hc
  · exact ⟨hc.2.1,hc.1,hc.2.2.2,hc.2.2.1⟩


private theorem parameter_append (w : List ℕ+) (a : ℕ+) :
    middleParameter (w++[a]) = 1 / (((a:ℕ):ℝ)+middleParameter w) := by
  have hD := (middle_continuant_growth w).2.1
  unfold middleParameter
  rw [cd_append]
  dsimp only
  rw [add_div' _ _ _ hD.ne', one_div_div]
  congr 1
  ring

private theorem repeated_parameter (k : ℕ) :
    middleParameter (List.replicate k (3:ℕ+)) = finiteCF (List.replicate k (3:ℕ+)) := by
  induction k with
  | zero => norm_num [middleParameter, middleCD, finiteCF]
  | succ k ih =>
    conv_lhs => rw [List.replicate_succ', parameter_append, ih]
    simp only [List.replicate_succ, finiteCF]

private lemma pe_nonneg (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ prefixEval w x := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    change 0 ≤ 1 / (((a:ℕ):ℝ) + prefixEval w x)
    positivity


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


private lemma absdiff_formula (w : List ℕ+) (x y : ℝ)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    |prefixEval w x-prefixEval w y| = |x-y| /
      ((middleCD w).2^2*(1+middleParameter w*x)*(1+middleParameter w*y)) := by
  have hD := (middle_continuant_growth w).2.1
  have hc := congrArg Prod.fst (cd_coordinates w)
  have hd := congrArg Prod.snd (cd_coordinates w)
  dsimp only at hc hd
  rw [prefixEval_difference w x y hx hy, ← hc, ← hd]
  congr 1
  unfold middleParameter
  field_simp [ne_of_gt hD]

private lemma absdiff_pos (w : List ℕ+) (x y : ℝ)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) (hxy : y < x) :
    0 < |prefixEval w x-prefixEval w y| := by
  rw [absdiff_formula w x y hx hy, abs_of_pos (sub_pos.mpr hxy)]
  have hD := (middle_continuant_growth w).2.1
  have hp := (middle_continuant_growth w).1
  have hx0 := hx.1
  have hy0 := hy.1
  exact div_pos (sub_pos.mpr hxy) (by positivity)

private lemma ratio_two_stage (u v w : List ℕ+) (a b c d : ℝ)
    (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1)
    (hc : c ∈ Set.Icc (0:ℝ) 1) (hd : d ∈ Set.Icc (0:ℝ) 1)
    (hab : a < b) (hdc : d < c) :
    |prefixEval (u++w) b-prefixEval (u++w) a| /
      |prefixEval (v++w) c-prefixEval (v++w) d| =
    ((b-a)/(c-d)) *
      ((1+middleParameter w*c)*(1+middleParameter w*d)) /
      ((1+middleParameter w*a)*(1+middleParameter w*b)) *
      ((1+middleParameter v*prefixEval w c)*(1+middleParameter v*prefixEval w d)) /
      ((1+middleParameter u*prefixEval w a)*(1+middleParameter u*prefixEval w b)) /
      ((middleCD u).2^2/(middleCD v).2^2) := by
  have hwa := pe_unit w a ha
  have hwb := pe_unit w b hb
  have hwc := pe_unit w c hc
  have hwd := pe_unit w d hd
  simp only [pe_append]
  rw [absdiff_formula u _ _ hwb hwa, absdiff_formula v _ _ hwc hwd,
    absdiff_formula w b a hb ha, absdiff_formula w c d hc hd,
    abs_of_pos (sub_pos.mpr hab), abs_of_pos (sub_pos.mpr hdc)]
  have huD := (middle_continuant_growth u).2.1
  have hvD := (middle_continuant_growth v).2.1
  have hwD := (middle_continuant_growth w).2.1
  have hup := (middle_continuant_growth u).1
  have hvp := (middle_continuant_growth v).1
  have hwp := (middle_continuant_growth w).1
  have ha0 := ha.1
  have hb0 := hb.1
  have hc0 := hc.1
  have hd0 := hd.1
  have hwa0 := hwa.1
  have hwb0 := hwb.1
  have hwc0 := hwc.1
  have hwd0 := hwd.1
  have hab0 := sub_pos.mpr hab
  have hcd0 := sub_pos.mpr hdc
  field_simp (disch := positivity)
  <;> ring

private lemma rho_unit : middleRho ∈ Set.Icc (0:ℝ) 1 := by
  obtain ⟨_, _, _, _, hr, hr'⟩ := alpha_beta_bounds
  exact ⟨hr, by linarith⟩

private lemma jtails_unit :
    middleJA ∈ Set.Icc (0:ℝ) 1 ∧ middleJB ∈ Set.Icc (0:ℝ) 1 ∧
    middleJC ∈ Set.Icc (0:ℝ) 1 ∧ middleJD ∈ Set.Icc (0:ℝ) 1 :=
  ⟨pe_unit [3] _ rho_unit, pe_unit [3,3,1,3] _ rho_unit,
    pe_unit [2] _ ab_unit.2.1, pe_unit [3,3,1,2] _ ab_unit.2.1⟩

private lemma phi_bounds (x : ℝ) (hx : 0 ≤ x) :
    0 < prefixEval [3] x ∧ prefixEval [3] x ≤ (1/3:ℝ) := by
  change 0 < 1/(3+x) ∧ 1/(3+x) ≤ (1/3:ℝ)
  constructor
  · positivity
  · apply (div_le_iff₀ (by linarith : 0 < 3+x)).2
    linarith

private lemma phi2_bounds (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    (3/10:ℝ) ≤ prefixEval [3,3] x ∧ prefixEval [3,3] x < (1/3:ℝ) := by
  have h := phi_bounds x hx.1
  change (3/10:ℝ) ≤ 1/(3+prefixEval [3] x) ∧ 1/(3+prefixEval [3] x) < (1/3:ℝ)
  have hp : 0 < 3+prefixEval [3] x := by linarith [h.1]
  constructor
  · apply (le_div_iff₀ hp).2
    linarith [h.2]
  · apply (div_lt_iff₀ hp).2
    linarith [h.1]

private lemma jtails_order : middleJA < middleJB ∧ middleJD < middleJC := by
  have hr : (1/2:ℝ) ≤ middleRho := by
    have h : (3/2:ℝ) ≤ Real.sqrt 3 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    unfold middleRho
    linarith
  have ha : middleJA < (3/10:ℝ) := by
    change 1/(3+middleRho) < (3/10:ℝ)
    apply (div_lt_iff₀ (by linarith : 0 < 3+middleRho)).2
    linarith
  have hb : (3/10:ℝ) ≤ middleJB := (phi2_bounds (prefixEval [1,3] middleRho)
    (pe_unit [1,3] _ rho_unit)).1
  have hd : middleJD < (1/3:ℝ) := (phi2_bounds (prefixEval [1,2] middleBeta)
    (pe_unit [1,2] _ ab_unit.2.1)).2
  have hc : (1/3:ℝ) ≤ middleJC := by
    have hb0 := ab_unit.2.1.1
    change (1/3:ℝ) ≤ 1/(2+middleBeta)
    apply (le_div_iff₀ (by linarith : 0 < 2+middleBeta)).2
    linarith [ab_unit.2.1.2]
  exact ⟨lt_of_lt_of_le ha hb, lt_of_lt_of_le hd hc⟩

private lemma contact_ratio (u v : List ℕ+) (k : ℕ) :
    |prefixEval (u++List.replicate k 3) middleJB-prefixEval (u++List.replicate k 3) middleJA| /
      |prefixEval (v++List.replicate k 3) middleJC-prefixEval (v++List.replicate k 3) middleJD| =
    middleJThreshold (middleParameter u) (middleParameter v) k /
      ((middleCD u).2^2/(middleCD v).2^2) := by
  have h := ratio_two_stage u v (List.replicate k 3) middleJA middleJB middleJC middleJD
    jtails_unit.1 jtails_unit.2.1 jtails_unit.2.2.1 jtails_unit.2.2.2
    jtails_order.1 jtails_order.2
  simpa only [repeated_parameter, middleJThreshold, middleJR] using h


private noncomputable def short3 (c : MiddleCore) : ℝ :=
  4+prefixEval c.left middleJA+prefixEval c.right middleJC
private noncomputable def short13 (c : MiddleCore) : ℝ :=
  4+prefixEval c.left (prefixEval [1,3] middleRho)+prefixEval c.right (prefixEval [1,2] middleBeta)
private noncomputable def shortLo (c : MiddleCore) : ℝ :=
  if c.left.length%2=0 then short3 c else short13 c
private noncomputable def shortHi (c : MiddleCore) : ℝ :=
  if c.left.length%2=0 then short13 c else short3 c

private lemma short_tails_order : middleAlpha ≤ middleJA ∧ middleJA ≤ middleJC ∧
    middleJC ≤ prefixEval [1,2] middleBeta ∧
    prefixEval [1,2] middleBeta ≤ prefixEval [1,3] middleRho ∧
    prefixEval [1,3] middleRho ≤ middleBeta := by
  obtain ⟨ha, ha', hb, hb', hr, hr'⟩ := alpha_beta_bounds
  have hac : middleJA ≤ middleJC := by
    exact one_div_le_one_div_of_le (by linarith : 0 < 2+middleBeta)
      (by linarith : 2+middleBeta ≤ 3+middleRho)
  have hc0 := jtails_unit.2.2.1.1
  have hcHalf : middleJC ≤ (1/2:ℝ) := by
    change 1/(2+middleBeta) ≤ (1/2:ℝ)
    apply (div_le_iff₀ (by linarith : 0 < 2+middleBeta)).2
    linarith
  refine ⟨endpoint_tails.1.1, hac, ?_, ?_, endpoint_tails.2.2.1.2⟩
  · simp only [prefixEval, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat]
    change middleJC ≤ 1/(1+middleJC)
    apply (le_div_iff₀ (by linarith : 0 < 1+middleJC)).2
    have hsq := mul_le_mul_of_nonneg_right hcHalf hc0
    nlinarith
  · simp only [prefixEval, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat]
    have ha0 := jtails_unit.1.1
    exact one_div_le_one_div_of_le (by linarith : 0 < 1+middleJA)
      (by linarith : 1+middleJA ≤ 1+middleJC)

private lemma e3_inner (c : MiddleCore) (hp : c.left.length%2=c.right.length%2) :
    if c.left.length%2=0 then middleE3 c ≤ short3 c else short3 c ≤ middleE3 c := by
  have hl := pe_order c.left middleAlpha middleJA ab_unit.1.1 jtails_unit.1.1 short_tails_order.1
  have hr := pe_order c.right middleJA middleJC jtails_unit.1.1 jtails_unit.2.2.1.1 short_tails_order.2.1
  by_cases he : c.left.length%2=0
  · have he' : c.right.length%2=0 := hp.symm.trans he
    simp only [he, ite_true]
    unfold middleE3
    split_ifs
    · simp only [short3, middleJA, middleJC, pe_append]
      exact le_rfl
    · simp only [short3, pe_append]
      change 4+prefixEval c.left middleAlpha+prefixEval c.right middleJA ≤ _
      linarith only [hl.1 he, hr.1 he']
  · have ho : c.left.length%2=1 := by omega
    have ho' : c.right.length%2=1 := hp.symm.trans ho
    simp only [he, ite_false]
    unfold middleE3
    split_ifs
    · simp only [short3, middleJA, middleJC, pe_append]
      exact le_rfl
    · simp only [short3, pe_append]
      change _ ≤ 4+prefixEval c.left middleAlpha+prefixEval c.right middleJA
      linarith only [hl.2 ho, hr.2 ho']

private lemma e13_inner (c : MiddleCore) (hp : c.left.length%2=c.right.length%2) :
    if c.left.length%2=0 then short13 c ≤ middleE13 c else middleE13 c ≤ short13 c := by
  have h13 := pe_unit [1,3] middleRho rho_unit
  have h12 := pe_unit [1,2] middleBeta ab_unit.2.1
  have hl := pe_order c.left (prefixEval [1,3] middleRho) middleBeta h13.1 ab_unit.2.1.1 short_tails_order.2.2.2.2
  have hr := pe_order c.right (prefixEval [1,2] middleBeta) (prefixEval [1,3] middleRho)
    h12.1 h13.1 short_tails_order.2.2.2.1
  by_cases he : c.left.length%2=0
  · have he' : c.right.length%2=0 := hp.symm.trans he
    simp only [he, ite_true]
    unfold middleE13
    split_ifs
    · simp only [short13, pe_append]
      exact le_rfl
    · simp only [short13, pe_append]
      linarith only [hl.1 he, hr.1 he']
  · have ho : c.left.length%2=1 := by omega
    have ho' : c.right.length%2=1 := hp.symm.trans ho
    simp only [he, ite_false]
    unfold middleE13
    split_ifs
    · simp only [short13, pe_append]
      exact le_rfl
    · simp only [short13, pe_append]
      linarith only [hl.2 ho, hr.2 ho']

private lemma short_order (c : MiddleCore) (hp : c.left.length%2=c.right.length%2) :
    if c.left.length%2=0 then short3 c ≤ short13 c else short13 c ≤ short3 c := by
  have h13 := pe_unit [1,3] middleRho rho_unit
  have h12 := pe_unit [1,2] middleBeta ab_unit.2.1
  have hac := short_tails_order.2.1
  have hcb := short_tails_order.2.2.1
  have hbd := short_tails_order.2.2.2.1
  have hl := pe_order c.left middleJA (prefixEval [1,3] middleRho)
    jtails_unit.1.1 h13.1 (hac.trans (hcb.trans hbd))
  have hr := pe_order c.right middleJC (prefixEval [1,2] middleBeta)
    jtails_unit.2.2.1.1 h12.1 hcb
  by_cases he : c.left.length%2=0
  · have he' : c.right.length%2=0 := hp.symm.trans he
    simp only [he, ite_true, short3, short13]
    linarith only [hl.1 he, hr.1 he']
  · have ho : c.left.length%2=1 := by omega
    have ho' : c.right.length%2=1 := hp.symm.trans ho
    simp only [he, ite_false, short3, short13]
    linarith only [hl.2 ho, hr.2 ho']

private lemma bounds_no_swap (c : MiddleCore) (hn : middleNormalized c=c)
    (hp : c.left.length%2=c.right.length%2) :
    middleBounds c = if c.left.length%2=0 then (middleE3 c,middleE13 c) else (middleE13 c,middleE3 c) := by
  unfold middleBounds
  rw [hn]
  simp only [if_pos hp]
  simp only [middleEqualBounds, hn]

private lemma short_bounds (c : MiddleCore) (hn : middleNormalized c=c)
    (hp : c.left.length%2=c.right.length%2) :
    (middleBounds c).1 ≤ shortLo c ∧ shortLo c ≤ shortHi c ∧ shortHi c ≤ (middleBounds c).2 := by
  have h3 := e3_inner c hp
  have h13 := e13_inner c hp
  have ho := short_order c hp
  rw [bounds_no_swap c hn hp]
  by_cases he : c.left.length%2=0
  · simp only [he, ite_true, shortLo, shortHi] at h3 h13 ho ⊢
    exact ⟨h3,ho,h13⟩
  · simp only [he, ite_false, shortLo, shortHi] at h3 h13 ho ⊢
    exact ⟨h13,ho,h3⟩

private lemma short13_two (u v : List ℕ+) (k : ℕ) :
    short13 ⟨u++List.replicate (k+2) 3,v++List.replicate (k+2) 3⟩ =
    4+prefixEval (u++List.replicate k 3) middleJB+prefixEval (v++List.replicate k 3) middleJD := by
  simp only [short13, List.replicate_succ',
    List.append_assoc, pe_append, middleJB, middleJD]
  rfl

private lemma short3_two (u v : List ℕ+) (k : ℕ) :
    short3 ⟨u++List.replicate (k+2) 3,v++List.replicate (k+2) 3⟩ =
    4+prefixEval (u++List.replicate k 3) (prefixEval [3,3] middleJA)+
      prefixEval (v++List.replicate k 3) (prefixEval [3,3] middleJC) := by
  simp only [short3, List.replicate_succ',
    List.append_assoc, pe_append]
  rfl

private lemma opposite_tails :
    prefixEval [3,3] middleJA ≤ prefixEval [1,3] middleRho ∧
    prefixEval [3,3] middleJC ≤ prefixEval [1,2] middleBeta := by
  have ha := (phi2_bounds middleJA jtails_unit.1).2
  have hc := (phi2_bounds middleJC jtails_unit.2.2.1).2
  have h13 : (1/2:ℝ) ≤ prefixEval [1,3] middleRho := by
    have h := jtails_unit.1
    simp only [prefixEval, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat]
    change (1/2:ℝ) ≤ 1/(1+middleJA)
    apply (le_div_iff₀ (by linarith [h.1] : 0 < 1+middleJA)).2
    linarith [h.2]
  have h12 : (1/2:ℝ) ≤ prefixEval [1,2] middleBeta := by
    have h := jtails_unit.2.2.1
    simp only [prefixEval, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat]
    change (1/2:ℝ) ≤ 1/(1+middleJC)
    apply (le_div_iff₀ (by linarith [h.1] : 0 < 1+middleJC)).2
    linarith [h.2]
  constructor <;> linarith

private lemma opposite_cross (u v : List ℕ+) (k : ℕ)
    (hp : u.length%2=v.length%2) :
    if (u++List.replicate k 3).length%2=0 then
      short3 ⟨u++List.replicate (k+2) 3,v++List.replicate (k+2) 3⟩ ≤
        short13 ⟨u++List.replicate k 3,v++List.replicate k 3⟩
    else short13 ⟨u++List.replicate k 3,v++List.replicate k 3⟩ ≤
      short3 ⟨u++List.replicate (k+2) 3,v++List.replicate (k+2) 3⟩ := by
  have hM : (u++List.replicate k 3).length%2=(v++List.replicate k 3).length%2 := by
    simp only [List.length_append, List.length_replicate]
    omega
  have hLa := (pe_unit [3,3] middleJA jtails_unit.1).1
  have hLc := (pe_unit [1,3] middleRho rho_unit).1
  have hRa := (pe_unit [3,3] middleJC jtails_unit.2.2.1).1
  have hRc := (pe_unit [1,2] middleBeta ab_unit.2.1).1
  have hl := pe_order (u++List.replicate k 3) _ _ hLa hLc opposite_tails.1
  have hr := pe_order (v++List.replicate k 3) _ _ hRa hRc opposite_tails.2
  rw [short3_two]
  by_cases he : (u++List.replicate k 3).length%2=0
  · have he' : (v++List.replicate k 3).length%2=0 := hM.symm.trans he
    simp only [he, ite_true, short13]
    linarith only [hl.1 he,hr.1 he']
  · have ho : (u++List.replicate k 3).length%2=1 := by omega
    have ho' : (v++List.replicate k 3).length%2=1 := hM.symm.trans ho
    simp only [he, ite_false, short13]
    linarith only [hl.2 ho,hr.2 ho']

private lemma threshold_cross (u v : List ℕ+) (k : ℕ)
    (hp : u.length%2=v.length%2)
    (hq : (middleCD u).2^2/(middleCD v).2^2 < middleJThreshold (middleParameter u) (middleParameter v) k) :
    if (u++List.replicate k 3).length%2=0 then
      short3 ⟨u++List.replicate k 3,v++List.replicate k 3⟩ <
        short13 ⟨u++List.replicate (k+2) 3,v++List.replicate (k+2) 3⟩
    else short13 ⟨u++List.replicate (k+2) 3,v++List.replicate (k+2) 3⟩ <
      short3 ⟨u++List.replicate k 3,v++List.replicate k 3⟩ := by
  have huD := (middle_continuant_growth u).2.1
  have hvD := (middle_continuant_growth v).2.1
  have hqpos : 0 < (middleCD u).2^2/(middleCD v).2^2 :=
    div_pos (sq_pos_of_pos huD) (sq_pos_of_pos hvD)
  have hRpos := absdiff_pos (v++List.replicate k 3) middleJC middleJD
    jtails_unit.2.2.1 jtails_unit.2.2.2 jtails_order.2
  have hrat : 1 <
      |prefixEval (u++List.replicate k 3) middleJB-prefixEval (u++List.replicate k 3) middleJA| /
      |prefixEval (v++List.replicate k 3) middleJC-prefixEval (v++List.replicate k 3) middleJD| := by
    rw [contact_ratio]
    apply (lt_div_iff₀ hqpos).2
    simpa only [one_mul] using hq
  have hineq := (lt_div_iff₀ hRpos).mp hrat
  simp only [one_mul] at hineq
  have hM : (u++List.replicate k 3).length%2=(v++List.replicate k 3).length%2 := by
    simp only [List.length_append, List.length_replicate]
    omega
  have hl := pe_order (u++List.replicate k 3) middleJA middleJB
    jtails_unit.1.1 jtails_unit.2.1.1 (le_of_lt jtails_order.1)
  have hr := pe_order (v++List.replicate k 3) middleJD middleJC
    jtails_unit.2.2.2.1 jtails_unit.2.2.1.1 (le_of_lt jtails_order.2)
  rw [short13_two]
  by_cases he : (u++List.replicate k 3).length%2=0
  · have he' : (v++List.replicate k 3).length%2=0 := hM.symm.trans he
    rw [abs_of_nonneg (sub_nonneg.mpr (hl.1 he)),
      abs_of_nonneg (sub_nonneg.mpr (hr.1 he'))] at hineq
    simp only [he, ite_true, short3]
    linarith only [hineq]
  · have ho : (u++List.replicate k 3).length%2=1 := by omega
    have ho' : (v++List.replicate k 3).length%2=1 := hM.symm.trans ho
    rw [abs_of_nonpos (sub_nonpos.mpr (hl.2 ho)),
      abs_of_nonpos (sub_nonpos.mpr (hr.2 ho'))] at hineq
    simp only [he, ite_false, short3]
    linarith only [hineq]

private lemma normalized_of_ratio (c : MiddleCore)
    (h : 1 < middleWidth c.left/middleWidth c.right) : middleNormalized c=c := by
  apply if_pos
  have hh := (lt_div_iff₀ (width_pos c.right)).mp h
  linarith

end M8Sep10JContactFull

open M8Sep10JContactFull

theorem solution :
    (∀ (p s : ℝ) (k : ℕ), p ∈ Set.Icc (1/4:ℝ) (4/5) → s ∈ Set.Icc (1/4:ℝ) (4/5) → 1 ≤ k → middleHStar p s < middleJThreshold p s k) →
    (∀ (c : MiddleCore) (r : MiddleRow) (k : ℕ), middleRegular c → middleRowCondition c r → middleEssentialJ r = true → 1 ≤ k → 1 < middleWidth ((middleNormalized c).left ++ List.replicate k 3) / middleWidth ((middleNormalized c).right ++ List.replicate k 3)) →
    ∀ (c : MiddleCore) (r : MiddleRow) (k : ℕ), middleRegular c → middleRowCondition c r → middleEssentialJ r = true → 1 ≤ k →
      (middleCover (middleRepairJ c k) ∩ middleCover (middleRepairJ c (k+2))).Nonempty := by
  intro hnum hratio c r k hc hrow hj hk
  have hrows : (middleNormalized c).left.length%2=(middleNormalized c).right.length%2 ∧
      ¬middleShort c 1 := by
    cases r <;> simp [middleEssentialJ] at hj
    · exact ⟨hrow.1,hrow.2.2⟩
    · exact ⟨hrow.1,hrow.2.2.2.2⟩
  let u := (middleNormalized c).left
  let v := (middleNormalized c).right
  let j : ℕ → MiddleCore := fun n => ⟨u++List.replicate n 3,v++List.replicate n 3⟩
  have hp : u.length%2=v.length%2 := hrows.1
  have hjp (n : ℕ) : (j n).left.length%2=(j n).right.length%2 := by
    dsimp only [j]
    simp only [List.length_append, List.length_replicate]
    omega
  have hnorm (n : ℕ) (hn : 1 ≤ n) : middleNormalized (j n)=j n :=
    normalized_of_ratio _ (hratio c r n hc hrow hj hn)
  have hJ (n : ℕ) (hn : 1 ≤ n) : middleRepairJ c n=j n := by
    change middleNormalized (j n)=j n
    exact hnorm n hn
  have hqstar : middleQ c < middleHStar (middleParameter u) (middleParameter v) :=
    lt_of_not_ge (fun h => hrows.2 ((short1_iff c).2 h))
  have hreg := normalized_regular c hc
  have hq : (middleCD u).2^2/(middleCD v).2^2 <
      middleJThreshold (middleParameter u) (middleParameter v) k :=
    lt_trans hqstar (hnum _ _ k hreg.1 hreg.2.1 hk)
  have hcross := threshold_cross u v k hp hq
  have hop := opposite_cross u v k hp
  change (if (j k).left.length%2=0 then short3 (j k) < short13 (j (k+2))
    else short13 (j (k+2)) < short3 (j k)) at hcross
  change (if (j k).left.length%2=0 then short3 (j (k+2)) ≤ short13 (j k)
    else short13 (j k) ≤ short3 (j (k+2))) at hop
  have hp2 : (j (k+2)).left.length%2=(j k).left.length%2 := by
    dsimp only [j]
    simp only [List.length_append, List.length_replicate]
    omega
  have hpair : shortLo (j k) ≤ shortHi (j (k+2)) ∧ shortLo (j (k+2)) ≤ shortHi (j k) := by
    by_cases he : (j k).left.length%2=0
    · simp only [he, ite_true] at hcross hop
      simp only [shortLo, shortHi, hp2, he, ite_true]
      exact ⟨le_of_lt hcross,hop⟩
    · simp only [he, ite_false] at hcross hop
      simp only [shortLo, shortHi, hp2, he, ite_false]
      exact ⟨hop,le_of_lt hcross⟩
  have h1 := short_bounds (j k) (hnorm k hk) (hjp k)
  have h2 := short_bounds (j (k+2)) (hnorm (k+2) (by omega)) (hjp (k+2))
  rw [hJ k hk, hJ (k+2) (by omega)]
  refine ⟨max (shortLo (j k)) (shortLo (j (k+2))), ?_⟩
  constructor
  · exact ⟨h1.1.trans (le_max_left _ _), (max_le h1.2.1 hpair.2).trans h1.2.2⟩
  · exact ⟨h2.1.trans (le_max_right _ _), (max_le hpair.1 h2.2.1).trans h2.2.2⟩

#print axioms solution

