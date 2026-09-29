-- Prove2me | solution 2 for Freiman.lower_path_fairness_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-18T13:32:28.12295+00:00
-- url     : https://prove2.me/submissions/ff8a2039-978a-4586-bb35-7acaad3d9c8c

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

open Freiman

namespace FairCore

/-! ## Part A: width machinery (ported from our accepted work/r19/s14sel/Tie.lean) -/

lemma pe_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, prefixEval, ih]

lemma pe_single (a : ℕ+) (x : ℝ) : prefixEval [a] x = 1 / (((a:ℕ):ℝ) + x) := rfl

lemma ab_unit : lowerAlpha ∈ Set.Icc (0:ℝ) 1 ∧ lowerBeta ∈ Set.Icc (0:ℝ) 1 ∧ lowerAlpha < lowerBeta := by
  have h4 : (4:ℝ) ≤ Real.sqrt 21 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h5 : Real.sqrt 21 ≤ (5:ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  dsimp [lowerAlpha, lowerBeta]
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by linarith⟩
lemma rho_unit : lowerTau ∈ Set.Icc (0:ℝ) 1 := by
  have h1 : (1:ℝ) ≤ Real.sqrt 3 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h2 : Real.sqrt 3 ≤ (2:ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  dsimp [lowerTau]
  exact ⟨by linarith, by linarith⟩

/-! ### Continuants and the signed difference identity -/

/-- real-valued continuants of `lowerCD`. -/
noncomputable def rCD (w : List ℕ+) : ℝ × ℝ := (((lowerCD w).1 : ℝ), ((lowerCD w).2 : ℝ))

lemma lowerCD_append (w : List ℕ+) (a : ℕ+) :
    lowerCD (w ++ [a]) = ((lowerCD w).2, (lowerCD w).1 + (a:ℕ) * (lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]

lemma cd_append (w : List ℕ+) (a : ℕ+) :
    rCD (w ++ [a]) = ((rCD w).2, (rCD w).1 + ((a:ℕ):ℝ) * (rCD w).2) := by
  simp only [rCD, lowerCD_append]; push_cast; rfl

lemma cd_nil : rCD [] = (0, 1) := by simp [rCD, lowerCD]

lemma ratio_eq (w : List ℕ+) : lowerRatio w = (rCD w).1 / (rCD w).2 := rfl

lemma cd_pos (w : List ℕ+) : 0 ≤ (rCD w).1 ∧ 0 < (rCD w).2 := by
  induction w using List.reverseRecOn with
  | nil => rw [cd_nil]; norm_num
  | append_singleton w a ih =>
    rw [cd_append]
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    exact ⟨le_of_lt ih.2, by nlinarith [ih.1, ih.2]⟩

lemma param_nonneg (w : List ℕ+) : 0 ≤ lowerRatio w :=
  div_nonneg (cd_pos w).1 (cd_pos w).2.le

/-- `(-1)^{|w|}` written with an `if`. -/
noncomputable def sgnOf (w : List ℕ+) : ℝ := if w.length % 2 = 0 then 1 else -1

lemma sgnOf_append (w : List ℕ+) (a : ℕ+) : sgnOf (w ++ [a]) = - sgnOf w := by
  unfold sgnOf
  have hl : (w ++ [a]).length = w.length + 1 := by simp
  rw [hl]
  rcases Nat.mod_two_eq_zero_or_one w.length with h | h
  · rw [if_neg (by omega : ¬ (w.length + 1) % 2 = 0), if_pos h]; try norm_num
  · rw [if_pos (by omega : (w.length + 1) % 2 = 0), if_neg (by omega : ¬ w.length % 2 = 0)]; try norm_num

lemma sgnOf_sq (w : List ℕ+) : sgnOf w * sgnOf w = 1 := by
  unfold sgnOf; split_ifs <;> norm_num

lemma pe_diff_raw (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    prefixEval w x - prefixEval w y =
      sgnOf w * (x - y) / (((rCD w).2 + (rCD w).1 * x) * ((rCD w).2 + (rCD w).1 * y)) := by
  induction w using List.reverseRecOn generalizing x y with
  | nil => simp [cd_nil, prefixEval, sgnOf]
  | append_singleton w a ih =>
    obtain ⟨hc, hd⟩ := cd_pos w
    have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    have hax : 0 < ((a:ℕ):ℝ) + x := by linarith
    have hay : 0 < ((a:ℕ):ℝ) + y := by linarith
    have hx' : 0 ≤ 1 / (((a:ℕ):ℝ) + x) := by positivity
    have hy' : 0 ≤ 1 / (((a:ℕ):ℝ) + y) := by positivity
    have hdx : 0 < (rCD w).2 + (rCD w).1 * (1 / (((a:ℕ):ℝ) + x)) := by positivity
    have hdy : 0 < (rCD w).2 + (rCD w).1 * (1 / (((a:ℕ):ℝ) + y)) := by positivity
    have hdx' : 0 < (rCD w).1 + ((a:ℕ):ℝ) * (rCD w).2 + (rCD w).2 * x := by positivity
    have hdy' : 0 < (rCD w).1 + ((a:ℕ):ℝ) * (rCD w).2 + (rCD w).2 * y := by positivity
    rw [pe_append, pe_append, pe_single, pe_single, ih _ _ hx' hy', cd_append, sgnOf_append]
    simp only
    field_simp
    try ring

lemma pe_diff (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    prefixEval w x - prefixEval w y =
      sgnOf w * (x - y) /
        ((rCD w).2 ^ 2 * (1 + lowerRatio w * x) * (1 + lowerRatio w * y)) := by
  rw [pe_diff_raw w x y hx hy]
  obtain ⟨hc, hd⟩ := cd_pos w
  congr 1
  rw [ratio_eq]
  field_simp
  try ring

lemma width_eq (w : List ℕ+) :
    lowerWidth w = (lowerBeta - lowerAlpha) /
      ((rCD w).2 ^ 2 * (1 + lowerRatio w * lowerAlpha) * (1 + lowerRatio w * lowerBeta)) := by
  obtain ⟨ha, hb, hab⟩ := ab_unit
  have hp := param_nonneg w
  have hd := (cd_pos w).2
  unfold lowerWidth
  rw [pe_diff w _ _ hb.1 ha.1]
  have hpos : 0 < (rCD w).2 ^ 2 * (1 + lowerRatio w * lowerBeta) * (1 + lowerRatio w * lowerAlpha) := by
    have : 0 ≤ lowerRatio w * lowerAlpha := mul_nonneg hp ha.1
    have : 0 ≤ lowerRatio w * lowerBeta := mul_nonneg hp hb.1
    positivity
  rw [abs_div, abs_of_pos hpos, abs_mul]
  have : |sgnOf w| = 1 := by unfold sgnOf; split_ifs <;> simp
  rw [this, one_mul, abs_of_pos (sub_pos.mpr hab)]
  ring

lemma width_pos (w : List ℕ+) : 0 < lowerWidth w := by
  obtain ⟨ha, hb, hab⟩ := ab_unit
  have hp := param_nonneg w
  have hd := (cd_pos w).2
  rw [width_eq]
  have : 0 ≤ lowerRatio w * lowerAlpha := mul_nonneg hp ha.1
  have : 0 ≤ lowerRatio w * lowerBeta := mul_nonneg hp hb.1
  apply div_pos (sub_pos.mpr hab)
  positivity

lemma rCD_fst (w : List ℕ+) : (rCD w).1 = ((lowerCD w).1 : ℝ) := rfl
lemma rCD_snd (w : List ℕ+) : (rCD w).2 = ((lowerCD w).2 : ℝ) := rfl

/-! ### The integer normal form of a width -/

def wA (w : List ℕ+) : ℤ := ((lowerCD w).1 : ℤ)^2 + ((lowerCD w).2 : ℤ)^2
def wB (w : List ℕ+) : ℤ :=
  4*((lowerCD w).1 : ℤ)*((lowerCD w).2 : ℤ) - 3*((lowerCD w).1 : ℤ)^2

lemma wA_cast (w : List ℕ+) : ((wA w : ℤ) : ℝ) = (rCD w).1^2 + (rCD w).2^2 := by
  rw [rCD_fst, rCD_snd]; simp only [wA]; push_cast; ring
lemma wB_cast (w : List ℕ+) :
    ((wB w : ℤ) : ℝ) = 4*(rCD w).1*(rCD w).2 - 3*(rCD w).1^2 := by
  rw [rCD_fst, rCD_snd]; simp only [wB]; push_cast; ring

lemma beta_eq : lowerBeta = 3 * lowerAlpha := by
  simp only [lowerAlpha, lowerBeta]; ring

lemma alpha_sq : 3 * lowerAlpha^2 = 1 - 3*lowerAlpha := by
  have h : Real.sqrt 21 ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  simp only [lowerAlpha]
  nlinarith [h]

lemma width_AB (w : List ℕ+) :
    lowerWidth w = (lowerBeta - lowerAlpha) / ((wA w : ℝ) + lowerAlpha * (wB w : ℝ)) := by
  rw [width_eq]
  congr 1
  have hd : (rCD w).2 ≠ 0 := ne_of_gt (cd_pos w).2
  have key : (rCD w).2 ^ 2 * (1 + lowerRatio w * lowerAlpha) * (1 + lowerRatio w * lowerBeta)
      = ((rCD w).2 + (rCD w).1 * lowerAlpha) * ((rCD w).2 + (rCD w).1 * lowerBeta) := by
    rw [ratio_eq]; field_simp
  rw [key, wA_cast, wB_cast, beta_eq]
  linear_combination ((rCD w).1^2) * alpha_sq

lemma width_den_pos (w : List ℕ+) : 0 < (wA w : ℝ) + lowerAlpha * (wB w : ℝ) := by
  obtain ⟨ha, hb, hab⟩ := ab_unit
  have hnum : (0:ℝ) < lowerBeta - lowerAlpha := sub_pos.mpr hab
  have h2 := width_pos w
  rw [width_AB w] at h2
  rcases lt_trichotomy ((wA w : ℝ) + lowerAlpha * (wB w : ℝ)) 0 with hc | hc | hc
  · have : (lowerBeta - lowerAlpha) / ((wA w : ℝ) + lowerAlpha * (wB w : ℝ)) < 0 :=
      div_neg_of_pos_of_neg hnum hc
    linarith
  · rw [hc, div_zero] at h2; linarith
  · exact hc

/-! ### Irrationality: a width determines the integer pair `(wA, wB)` -/

/-! ## Part B: strict width contraction -/

lemma alpha_pos : 0 < lowerAlpha := by
  have h4 : (4:ℝ) ≤ Real.sqrt 21 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  dsimp [lowerAlpha]; linarith

lemma wden_append (w : List ℕ+) (a : ℕ+) :
    ((wA (w ++ [a]) : ℝ) + lowerAlpha * (wB (w ++ [a]) : ℝ))
      = ((wA w : ℝ) + lowerAlpha * (wB w : ℝ))
        + (2*((a:ℕ):ℝ)*(rCD w).1*(rCD w).2 + ((a:ℕ):ℝ)^2*(rCD w).2^2
           + lowerAlpha * ((4*((a:ℕ):ℝ)-3)*(rCD w).2^2 + 3*(rCD w).1^2)) := by
  rw [wA_cast, wB_cast, wA_cast, wB_cast, cd_append]
  ring

lemma width_append_single_lt (w : List ℕ+) (a : ℕ+) :
    lowerWidth (w ++ [a]) < lowerWidth w := by
  obtain ⟨ha, hb, hab⟩ := ab_unit
  obtain ⟨hc, hd⟩ := cd_pos w
  have hap : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.pos
  have hal := alpha_pos
  have hgrow : ((wA w : ℝ) + lowerAlpha * (wB w : ℝ))
      < ((wA (w ++ [a]) : ℝ) + lowerAlpha * (wB (w ++ [a]) : ℝ)) := by
    rw [wden_append]
    have e1 : (0:ℝ) ≤ 2*((a:ℕ):ℝ)*(rCD w).1*(rCD w).2 := by positivity
    have e2 : (0:ℝ) < ((a:ℕ):ℝ)^2*(rCD w).2^2 := by positivity
    have e3 : (1:ℝ) ≤ 4*((a:ℕ):ℝ)-3 := by linarith
    have e4 : (0:ℝ) ≤ (4*((a:ℕ):ℝ)-3)*(rCD w).2^2 + 3*(rCD w).1^2 := by nlinarith [sq_nonneg (rCD w).1, sq_nonneg (rCD w).2]
    have e5 : (0:ℝ) ≤ lowerAlpha * ((4*((a:ℕ):ℝ)-3)*(rCD w).2^2 + 3*(rCD w).1^2) :=
      mul_nonneg hal.le e4
    linarith
  have hpos := width_den_pos w
  rw [width_AB w, width_AB (w ++ [a])]
  exact div_lt_div_of_pos_left (by linarith) hpos hgrow

lemma width_append_le (w u : List ℕ+) : lowerWidth (w ++ u) ≤ lowerWidth w := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u a ih =>
    have h1 : w ++ (u ++ [a]) = (w ++ u) ++ [a] := by simp
    rw [h1]
    exact le_trans (le_of_lt (width_append_single_lt (w ++ u) a)) ih

lemma width_append_lt (w u : List ℕ+) (hu : u ≠ []) : lowerWidth (w ++ u) < lowerWidth w := by
  induction u using List.reverseRecOn with
  | nil => exact absurd rfl hu
  | append_singleton u a _ =>
    have h1 : w ++ (u ++ [a]) = (w ++ u) ++ [a] := by simp
    rw [h1]
    exact lt_of_lt_of_le (width_append_single_lt (w ++ u) a) (width_append_le w u)

/-! ## Part C: the physical step law -/

lemma phys_cases (h : ℕ → LowerPair) (n : ℕ) :
    (lowerOrientation h n = false ∧ lowerPhysicalPath h n = h n) ∨
    (lowerOrientation h n = true ∧ lowerPhysicalPath h n = (h n).swap) := by
  unfold lowerPhysicalPath
  cases hb : lowerOrientation h n
  · exact Or.inl ⟨rfl, by simp [hb]⟩
  · exact Or.inr ⟨rfl, by simp [hb]⟩

lemma orient_succ (h : ℕ → LowerPair) (n : ℕ) :
    lowerOrientation h (n+1) = (lowerOrientation h n).xor (lowerReflects (h n)) := rfl

lemma refl_eq (p : LowerPair) : lowerReflects p = decide (lowerWidth p.1 < lowerWidth p.2) := by
  unfold lowerReflects; rfl

lemma norm_eq (p : LowerPair) :
    lowerNormalize p = if lowerWidth p.2 ≤ lowerWidth p.1 then p else (p.2, p.1) := by
  unfold lowerNormalize; rfl

lemma orient_of_lt (h : ℕ → LowerPair) (n : ℕ)
    (hw : lowerWidth (lowerPhysicalPath h n).2 < lowerWidth (lowerPhysicalPath h n).1) :
    lowerOrientation h (n+1) = false := by
  rw [orient_succ, refl_eq]
  rcases phys_cases h n with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2] at hw
    rw [h1, decide_eq_false (not_lt.mpr hw.le)]; rfl
  · rw [h2] at hw
    simp only [Prod.fst_swap, Prod.snd_swap] at hw
    rw [h1, decide_eq_true hw]; rfl

lemma orient_of_gt (h : ℕ → LowerPair) (n : ℕ)
    (hw : lowerWidth (lowerPhysicalPath h n).1 < lowerWidth (lowerPhysicalPath h n).2) :
    lowerOrientation h (n+1) = true := by
  rw [orient_succ, refl_eq]
  rcases phys_cases h n with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2] at hw
    rw [h1, decide_eq_true hw]; rfl
  · rw [h2] at hw
    simp only [Prod.fst_swap, Prod.snd_swap] at hw
    rw [h1, decide_eq_false (not_lt.mpr hw.le)]; rfl

lemma orient_of_eq (h : ℕ → LowerPair) (n : ℕ)
    (hw : lowerWidth (lowerPhysicalPath h n).1 = lowerWidth (lowerPhysicalPath h n).2) :
    lowerOrientation h (n+1) = lowerOrientation h n := by
  rw [orient_succ, refl_eq]
  rcases phys_cases h n with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2] at hw
    rw [decide_eq_false (by simp [hw] : ¬ lowerWidth (h n).1 < lowerWidth (h n).2)]
    simp
  · rw [h2] at hw
    simp only [Prod.fst_swap, Prod.snd_swap] at hw
    rw [decide_eq_false (by simp [hw] : ¬ lowerWidth (h n).1 < lowerWidth (h n).2)]
    simp

/-! ## Part D: step law and length monotonicity -/

lemma child_eq (p : LowerPair) (l : LowerLabel) :
    lowerChild p l = ((lowerNormalize p).1 ++ l.1.reverse, (lowerNormalize p).2 ++ l.2) := rfl

lemma phys_eq (h : ℕ → LowerPair) (n : ℕ) :
    lowerPhysicalPath h n = if lowerOrientation h n then (h n).swap else h n := rfl

lemma norm_phys (h : ℕ → LowerPair) (n : ℕ) :
    (lowerOrientation h (n+1) = false → lowerNormalize (h n) = lowerPhysicalPath h n) ∧
    (lowerOrientation h (n+1) = true → lowerNormalize (h n) = (lowerPhysicalPath h n).swap) := by
  have ho : lowerOrientation h (n+1) = (lowerOrientation h n).xor (lowerReflects (h n)) := rfl
  rw [norm_eq]
  by_cases hb : lowerWidth (h n).2 ≤ lowerWidth (h n).1
  · have hr : lowerReflects (h n) = false := by
      rw [refl_eq]; exact decide_eq_false (not_lt.mpr hb)
    rw [if_pos hb]
    rcases phys_cases h n with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun _ => h2.symm, fun hc => by rw [ho, h1, hr] at hc; exact absurd hc (by simp)⟩
    · exact ⟨fun hc => by rw [ho, h1, hr] at hc; exact absurd hc (by simp),
        fun _ => by rw [h2]; simp⟩
  · have hlt : lowerWidth (h n).1 < lowerWidth (h n).2 := lt_of_not_ge hb
    have hr : lowerReflects (h n) = true := by rw [refl_eq]; exact decide_eq_true hlt
    rw [if_neg hb]
    rcases phys_cases h n with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun hc => by rw [ho, h1, hr] at hc; exact absurd hc (by simp),
        fun _ => by rw [h2]; rfl⟩
    · exact ⟨fun _ => by rw [h2]; rfl,
        fun hc => by rw [ho, h1, hr] at hc; exact absurd hc (by simp)⟩

lemma step_left (h : ℕ → LowerPair) (n : ℕ) (l : LowerLabel)
    (hs : h (n+1) = lowerChild (h n) l) (ho : lowerOrientation h (n+1) = false) :
    lowerPhysicalPath h (n+1)
      = ((lowerPhysicalPath h n).1 ++ l.1.reverse, (lowerPhysicalPath h n).2 ++ l.2) := by
  rw [phys_eq, ho, if_neg (by simp), hs, child_eq, (norm_phys h n).1 ho]

lemma step_right (h : ℕ → LowerPair) (n : ℕ) (l : LowerLabel)
    (hs : h (n+1) = lowerChild (h n) l) (ho : lowerOrientation h (n+1) = true) :
    lowerPhysicalPath h (n+1)
      = ((lowerPhysicalPath h n).1 ++ l.2, (lowerPhysicalPath h n).2 ++ l.1.reverse) := by
  rw [phys_eq, ho, if_pos (by simp), hs, child_eq, (norm_phys h n).2 ho]
  rfl

lemma len_mono (h : ℕ → LowerPair) (n : ℕ) (l : LowerLabel)
    (hs : h (n+1) = lowerChild (h n) l) :
    (lowerPhysicalPath h n).1.length ≤ (lowerPhysicalPath h (n+1)).1.length ∧
    (lowerPhysicalPath h n).2.length ≤ (lowerPhysicalPath h (n+1)).2.length := by
  cases ho : lowerOrientation h (n+1)
  · rw [step_left h n l hs ho]; simp
  · rw [step_right h n l hs ho]; simp

/-! ## Part E: which labels can have an empty first component -/

lemma neh_cand : ∀ l ∈ lowerLateCandidates, l.1 ≠ [] := by decide

lemma late_mem (p : LowerPair) (l : LowerLabel) (hl : l ∈ lowerLateList p) :
    l ∈ lowerLateCandidates := by
  unfold lowerLateList at hl
  split at hl
  · rename_i hex
    exact ((Classical.choose_spec hex).1 l hl).1
  · simp at hl

lemma neh_late (p : LowerPair) : ∀ l ∈ lowerLateList p, l.1 ≠ [] :=
  fun l hl => neh_cand l (late_mem p l hl)

lemma neh_early (p : LowerPair) : ∀ l ∈ lowerEarlyList p, l.1 ≠ [] := by
  unfold lowerEarlyList
  split_ifs <;> decide

lemma neh_equal (p : LowerPair) : ∀ l ∈ lowerEqualList p, l.1 ≠ [] := by
  have hE := neh_early p
  have hL := neh_late p
  intro l hl
  unfold lowerEqualList at hl
  split_ifs at hl <;>
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl <;>
    casesm* _ ∨ _ <;>
    first
      | exact hE _ (by assumption)
      | exact hL _ (by assumption)
      | (subst_vars; simp)

lemma neh_mixed (p : LowerPair) : ∀ l ∈ lowerMixedList p, l.1 ≠ [] ∨ l = ([], [1]) := by
  unfold lowerMixedList
  split_ifs <;> decide

lemma mixed_no01 (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : lowerH p 5) :
    ∀ l ∈ lowerMixedList p, l.1 ≠ [] := by
  unfold lowerMixedList
  rw [if_neg h2, if_pos h5]
  split_ifs <;> decide

lemma cd_den_pos (w : List ℕ+) : 0 < (lowerCD w).2 := by
  have h := (cd_pos w).2
  rw [rCD_snd] at h
  exact_mod_cast h

lemma cd_num_pos (w : List ℕ+) (h : w ≠ []) : 0 < (lowerCD w).1 := by
  induction w using List.reverseRecOn with
  | nil => exact absurd rfl h
  | append_singleton w a _ => rw [lowerCD_append]; exact cd_den_pos w

lemma cd_le (w : List ℕ+) : (lowerCD w).1 ≤ (lowerCD w).2 := by
  induction w using List.reverseRecOn with
  | nil => simp [lowerCD]
  | append_singleton w a _ =>
    rw [lowerCD_append]
    have hmul : (lowerCD w).2 ≤ (a:ℕ) * (lowerCD w).2 := Nat.le_mul_of_pos_left _ a.pos
    omega

/-! ## Part F: numeric bounds -- after a width tie, the `([],[1])` label is not offered -/

lemma recip_bounds {x A B lo hi a : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (h1 : A ≤ x) (h2 : x ≤ B)
    (hlo0 : 0 ≤ lo) (hhi0 : 0 ≤ hi)
    (hlo : lo * (a + B) ≤ 1) (hhi : 1 ≤ hi * (a + A)) :
    lo ≤ 1/(a+x) ∧ 1/(a+x) ≤ hi := by
  have hax : 0 < a + x := by linarith
  constructor
  · rw [le_div_iff₀ hax]; nlinarith
  · rw [div_le_iff₀ hax]; nlinarith

lemma tau_bounds : (0.73205:ℝ) ≤ lowerTau ∧ lowerTau ≤ 0.73206 := by
  have h1 : (1.73205:ℝ) ≤ Real.sqrt 3 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h2 : Real.sqrt 3 ≤ (1.73206:ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  unfold lowerTau
  constructor <;> linarith

lemma alpha_bounds : (0.2637:ℝ) ≤ lowerAlpha ∧ lowerAlpha ≤ 0.2638 := by
  have h1 : (4.5825:ℝ) ≤ Real.sqrt 21 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h2 : Real.sqrt 21 ≤ (4.5827:ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  unfold lowerAlpha
  constructor <;> linarith

lemma th_eq : lowerTheta 63 = 1/(2 + 1/(3 + lowerTau)) ∧
    lowerTheta 66 = 1/(1 + 1/(1 + 1/(3 + lowerTau))) ∧
    lowerTheta 90 = 1/(1 + 1/(2 + 1/(1 + 1/(3 + lowerTau)))) ∧
    lowerTheta 70 = 1/(1 + 1/(1 + 1/(2 + 1/(1 + 1/(3 + lowerTau))))) ∧
    lowerTheta 35 = 1/(2 + 1/(1 + 1/(2 + 1/(1 + 1/(3 + lowerTau))))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [lowerTheta, prefixEval]

lemma theta_bounds :
    ((0.440926:ℝ) ≤ lowerTheta 63 ∧ lowerTheta 63 ≤ 0.440928) ∧
    ((0.559072:ℝ) ≤ lowerTheta 66 ∧ lowerTheta 66 ≤ 0.559074) ∧
    ((0.736055:ℝ) ≤ lowerTheta 90 ∧ lowerTheta 90 ≤ 0.736056) ∧
    ((0.576018:ℝ) ≤ lowerTheta 70 ∧ lowerTheta 70 ≤ 0.576019) ∧
    ((0.365489:ℝ) ≤ lowerTheta 35 ∧ lowerTheta 35 ≤ 0.36549) := by
  obtain ⟨e63, e66, e90, e70, e35⟩ := th_eq
  obtain ⟨tl, tu⟩ := tau_bounds
  have x1 : (0.267948:ℝ) ≤ 1/(3 + lowerTau) ∧ 1/(3 + lowerTau) ≤ 0.26795 :=
    recip_bounds (by norm_num) (by norm_num) tl tu (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have x2 : (0.788674:ℝ) ≤ 1/(1 + 1/(3 + lowerTau)) ∧ 1/(1 + 1/(3 + lowerTau)) ≤ 0.788676 :=
    recip_bounds (by norm_num) (by norm_num) x1.1 x1.2 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have x3 : (0.358593:ℝ) ≤ 1/(2 + 1/(1 + 1/(3 + lowerTau)))
      ∧ 1/(2 + 1/(1 + 1/(3 + lowerTau))) ≤ 0.358594 :=
    recip_bounds (by norm_num) (by norm_num) x2.1 x2.2 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have x4 : (0.736055:ℝ) ≤ 1/(1 + 1/(2 + 1/(1 + 1/(3 + lowerTau))))
      ∧ 1/(1 + 1/(2 + 1/(1 + 1/(3 + lowerTau)))) ≤ 0.736056 :=
    recip_bounds (by norm_num) (by norm_num) x3.1 x3.2 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have x5 : (0.576018:ℝ) ≤ 1/(1 + 1/(1 + 1/(2 + 1/(1 + 1/(3 + lowerTau)))))
      ∧ 1/(1 + 1/(1 + 1/(2 + 1/(1 + 1/(3 + lowerTau))))) ≤ 0.576019 :=
    recip_bounds (by norm_num) (by norm_num) x4.1 x4.2 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have x6 : (0.365489:ℝ) ≤ 1/(2 + 1/(1 + 1/(2 + 1/(1 + 1/(3 + lowerTau)))))
      ∧ 1/(2 + 1/(1 + 1/(2 + 1/(1 + 1/(3 + lowerTau))))) ≤ 0.36549 :=
    recip_bounds (by norm_num) (by norm_num) x4.1 x4.2 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have x7 : (0.559072:ℝ) ≤ 1/(1 + 1/(1 + 1/(3 + lowerTau)))
      ∧ 1/(1 + 1/(1 + 1/(3 + lowerTau))) ≤ 0.559074 :=
    recip_bounds (by norm_num) (by norm_num) x2.1 x2.2 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have x8 : (0.440926:ℝ) ≤ 1/(2 + 1/(3 + lowerTau)) ∧ 1/(2 + 1/(3 + lowerTau)) ≤ 0.440928 :=
    recip_bounds (by norm_num) (by norm_num) x1.1 x1.2 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  exact ⟨by rw [e63]; exact x8, by rw [e66]; exact x7, by rw [e90]; exact x4,
    by rw [e70]; exact x5, by rw [e35]; exact x6⟩

noncomputable def gfun (x : ℝ) : ℝ := 1 + x^2 + lowerAlpha*(4*x - 3*x^2)

lemma gfun_pos (x : ℝ) (h0 : 0 ≤ x) : 0 < gfun x := by
  obtain ⟨hal, hau⟩ := alpha_bounds
  unfold gfun
  nlinarith [sq_nonneg x, mul_nonneg h0 h0]

lemma gfun_ge (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 4/5) :
    1 + x^2 + 0.2637*(4*x - 3*x^2) ≤ gfun x := by
  obtain ⟨hal, hau⟩ := alpha_bounds
  have hq : (0:ℝ) ≤ 4*x - 3*x^2 := by nlinarith
  unfold gfun
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ lowerAlpha - 0.2637) hq]

lemma E_eq (w : List ℕ+) :
    (wA w : ℝ) + lowerAlpha * (wB w : ℝ) = (rCD w).2^2 * gfun (lowerRatio w) := by
  have hd : (rCD w).2 ≠ 0 := ne_of_gt (cd_pos w).2
  rw [wA_cast, wB_cast, gfun, ratio_eq]
  field_simp
  ring

lemma E_eq_of_width (u v : List ℕ+) (h : lowerWidth u = lowerWidth v) :
    (wA u : ℝ) + lowerAlpha * (wB u : ℝ) = (wA v : ℝ) + lowerAlpha * (wB v : ℝ) := by
  obtain ⟨ha, hb, hab⟩ := ab_unit
  have hu := width_den_pos u
  have hv := width_den_pos v
  rw [width_AB u, width_AB v, div_eq_div_iff (ne_of_gt hu) (ne_of_gt hv)] at h
  have hnum : (0:ℝ) < lowerBeta - lowerAlpha := by linarith
  nlinarith [h]

lemma cd_den_mono (w u : List ℕ+) : (lowerCD w).2 ≤ (lowerCD (w ++ u)).2 := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u a ih =>
    have h1 : w ++ (u ++ [a]) = (w ++ u) ++ [a] := by simp
    rw [h1, lowerCD_append]
    have h2 : (lowerCD (w ++ u)).2 ≤ (a:ℕ) * (lowerCD (w ++ u)).2 :=
      Nat.le_mul_of_pos_left _ a.pos
    omega

lemma cd_num_ge (w u : List ℕ+) (hu : u ≠ []) : (lowerCD w).2 ≤ (lowerCD (w ++ u)).1 := by
  induction u using List.reverseRecOn with
  | nil => exact absurd rfl hu
  | append_singleton u a _ =>
    have h1 : w ++ (u ++ [a]) = (w ++ u) ++ [a] := by simp
    rw [h1, lowerCD_append]
    exact cd_den_mono w u

lemma cd_den_ge2 (w u : List ℕ+) (hu : u ≠ []) :
    (lowerCD w).1 + (lowerCD w).2 ≤ (lowerCD (w ++ u)).2 := by
  induction u using List.reverseRecOn with
  | nil => exact absurd rfl hu
  | append_singleton u a _ =>
    have h1 : w ++ (u ++ [a]) = (w ++ u) ++ [a] := by simp
    rw [h1, lowerCD_append]
    have h2 : (lowerCD (w ++ u)).2 ≤ (a:ℕ) * (lowerCD (w ++ u)).2 :=
      Nat.le_mul_of_pos_left _ a.pos
    rcases eq_or_ne u ([] : List ℕ+) with rfl | hne
    · simp only [List.append_nil] at h2 ⊢
      omega
    · have h3 := cd_num_ge w u hne
      have h4 := cd_den_mono w u
      have h5 := cd_le w
      omega

lemma ineq_A2 (r : ℝ) (hr1 : 1/4 ≤ r) (hr2 : r ≤ 4/5) :
    (1 + r*0.440928)*(1 + r*0.559074) ≤ 1 + r^2 + 0.2637*(4*r - 3*r^2) := by nlinarith

lemma ineq_A5 (r : ℝ) (hr1 : 1/4 ≤ r) (hr2 : r ≤ 4/5) :
    (1 + r*0.36549)*(1 + r*0.440928) ≤ 1 + r^2 + 0.2637*(4*r - 3*r^2) := by nlinarith

lemma ineq_S2 (s : ℝ) (hs1 : 1/4 ≤ s) (hs2 : s ≤ 4/5) :
    (23/20)*s ≤ (37/50)*((1+s*0.576018)*(1+s*0.736055)) := by nlinarith

lemma ineq_S5 (s : ℝ) (hs1 : 1/4 ≤ s) (hs2 : s ≤ 4/5) :
    (23/20)*s < (279/500)*((1+s*0.440926)*(1+s*0.576018)) := by nlinarith

lemma prod_mono (r a b A B : ℝ) (hr : 0 ≤ r) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a ≤ A) (hb : b ≤ B) : (1 + r*a)*(1 + r*b) ≤ (1 + r*A)*(1 + r*B) := by
  have hA0 : 0 ≤ A := le_trans ha0 ha
  have h1 : 0 ≤ r*(A-a) := mul_nonneg hr (by linarith)
  have h2 : 0 ≤ r*(B-b) := mul_nonneg hr (by linarith)
  have h3 : 0 ≤ A*B - a*b := by nlinarith
  have h4 : 0 ≤ r^2*(A*B - a*b) := by positivity
  nlinarith [h1, h2, h4]

lemma div_chain {S X Y G D : ℝ} (hG : 0 < G) (hD : 0 < D) (hDG : D ≤ G)
    (hS : S ≤ Y / G) (hYX : Y ≤ X) (hX : 0 ≤ X) : S ≤ X / D := by
  have h2 : Y / G ≤ X / D := by
    rw [div_le_iff₀ hG, div_mul_eq_mul_div, le_div_iff₀ hD]
    nlinarith
  linarith

lemma div_chain_lt {S X Y G D : ℝ} (hG : 0 < G) (hD : 0 < D) (hDG : D ≤ G)
    (hS : S ≤ Y / G) (hYX : Y < X) (hX : 0 ≤ X) : S < X / D := by
  have h2 : Y / G < X / D := by
    rw [div_lt_iff₀ hG, div_mul_eq_mul_div, lt_div_iff₀ hD]
    nlinarith
  linarith

set_option maxHeartbeats 1000000 in
lemma tie_no01 (U V z : List ℕ+) (hz : z ≠ [])
    (htie : lowerWidth U = lowerWidth V)
    (hbox : lowerParameterBox (V ++ z, U)) :
    ¬ lowerH (V ++ z, U) 2 ∧ lowerH (V ++ z, U) 5 := by
  obtain ⟨hal, hau⟩ := alpha_bounds
  obtain ⟨⟨t63l, t63u⟩, ⟨t66l, t66u⟩, ⟨t90l, t90u⟩, ⟨t70l, t70u⟩, ⟨t35l, t35u⟩⟩ := theta_bounds
  obtain ⟨hs1, hs2, hr1, hr2⟩ := hbox
  have hwlt : lowerWidth (V ++ z) < lowerWidth U := by
    rw [htie]; exact width_append_lt V z hz
  have hnorm : lowerNormalize ((V ++ z, U) : LowerPair) = (U, V ++ z) := by
    rw [norm_eq, if_neg (not_le.mpr hwlt)]
  have hrho0 : (0:ℝ) ≤ lowerRatio V := param_nonneg V
  have hrho1 : lowerRatio V ≤ 1 := by
    rw [ratio_eq, div_le_one (cd_pos V).2]
    have := cd_le V
    simp only [rCD]
    exact_mod_cast this
  have hDU : (0:ℝ) < (rCD U).2 := (cd_pos U).2
  have hDV : (0:ℝ) < (rCD V).2 := (cd_pos V).2
  have hDZ : (0:ℝ) < (rCD (V ++ z)).2 := (cd_pos (V ++ z)).2
  have hEq : (rCD U).2^2 * gfun (lowerRatio U)
      = (rCD V).2^2 * gfun (lowerRatio V) := by
    rw [← E_eq U, ← E_eq V]; exact E_eq_of_width U V htie
  have hc1 : (rCD V).2 ≤ (rCD (V ++ z)).1 := by
    have h := cd_num_ge V z hz
    simp only [rCD]; exact_mod_cast h
  have hc2 : (rCD V).1 + (rCD V).2 ≤ (rCD (V ++ z)).2 := by
    have h := cd_den_ge2 V z hz
    simp only [rCD]; exact_mod_cast h
  have hsD : (rCD (V ++ z)).1 = lowerRatio (V ++ z) * (rCD (V ++ z)).2 := by
    rw [ratio_eq]; field_simp
  have hrhoD : (rCD V).1 = lowerRatio V * (rCD V).2 := by
    rw [ratio_eq]; field_simp
  have hgr : 0 < gfun (lowerRatio U) := gfun_pos _ (param_nonneg U)
  have hgv : 0 < gfun (lowerRatio V) := gfun_pos _ hrho0
  have hg : gfun (lowerRatio V) ≤ (23/20) * (1 + lowerRatio V) := by
    unfold gfun; nlinarith
  have hA1 : (rCD V).2 ≤ lowerRatio (V ++ z) * (rCD (V ++ z)).2 := by rw [← hsD]; exact hc1
  have hA2 : (rCD V).2 * (1 + lowerRatio V) ≤ (rCD (V ++ z)).2 := by
    rw [hrhoD] at hc2; nlinarith
  have hkey : (rCD U).2^2 * gfun (lowerRatio U)
      ≤ (23/20) * lowerRatio (V ++ z) * (rCD (V ++ z)).2^2 := by
    rw [hEq]
    have h1 : (rCD V).2 * gfun (lowerRatio V) ≤ (23/20) * (rCD (V ++ z)).2 := by
      nlinarith
    nlinarith [mul_nonneg (le_of_lt hDV) (le_of_lt hgv)]
  have hscale : lowerScale (lowerNormalize ((V ++ z, U) : LowerPair))
      = (rCD U).2^2 / (rCD (V ++ z)).2^2 := by rw [hnorm]; rfl
  have hsc : lowerScale (lowerNormalize ((V ++ z, U) : LowerPair))
      ≤ (23/20) * lowerRatio (V ++ z) / gfun (lowerRatio U) := by
    rw [hscale, div_le_iff₀ (by positivity : (0:ℝ) < (rCD (V ++ z)).2^2),
      div_mul_eq_mul_div, le_div_iff₀ hgr]
    nlinarith [hkey]
  have hthr : ∀ (c : ℝ) (i j k l : ℕ), lowerThreshold ((V ++ z, U) : LowerPair) c i j k l
      = c * ((1 + lowerRatio (V ++ z) * lowerTheta j) * (1 + lowerRatio (V ++ z) * lowerTheta l))
        / ((1 + lowerRatio U * lowerTheta i) * (1 + lowerRatio U * lowerTheta k)) := by
    intro c i j k l
    simp only [lowerThreshold, hnorm]
  have hgrge := gfun_ge (lowerRatio U) (param_nonneg U) hr2
  have hrU0 : (0:ℝ) ≤ lowerRatio U := param_nonneg U
  have hsZ0 : (0:ℝ) ≤ lowerRatio (V ++ z) := param_nonneg (V ++ z)
  have hpos63 : (0:ℝ) < 1 + lowerRatio U * lowerTheta 63 := by nlinarith
  have hpos66 : (0:ℝ) < 1 + lowerRatio U * lowerTheta 66 := by nlinarith
  have hpos35 : (0:ℝ) < 1 + lowerRatio U * lowerTheta 35 := by nlinarith
  refine ⟨?_, ?_⟩
  · show ¬ (lowerScale (lowerNormalize ((V ++ z, U) : LowerPair))
      > lowerThreshold ((V ++ z, U) : LowerPair) (37/50) 63 70 66 90)
    rw [not_lt, hthr]
    have hD2 : (0:ℝ) < (1 + lowerRatio U * lowerTheta 63) * (1 + lowerRatio U * lowerTheta 66) :=
      mul_pos hpos63 hpos66
    have hD2le : (1 + lowerRatio U * lowerTheta 63) * (1 + lowerRatio U * lowerTheta 66)
        ≤ gfun (lowerRatio U) := by
      have h1 := prod_mono (lowerRatio U) (lowerTheta 63) (lowerTheta 66) 0.440928 0.559074
        hrU0 (by linarith) (by linarith) t63u t66u
      have h2 := ineq_A2 (lowerRatio U) hr1 hr2
      linarith
    have hNle : (1+lowerRatio (V ++ z)*0.576018)*(1+lowerRatio (V ++ z)*0.736055)
        ≤ (1 + lowerRatio (V ++ z) * lowerTheta 70) * (1 + lowerRatio (V ++ z) * lowerTheta 90) :=
      prod_mono (lowerRatio (V ++ z)) 0.576018 0.736055 (lowerTheta 70) (lowerTheta 90)
        hsZ0 (by norm_num) (by norm_num) t70l t90l
    have hstep : (23/20) * lowerRatio (V ++ z)
        ≤ (37/50)*((1 + lowerRatio (V ++ z) * lowerTheta 70)
            * (1 + lowerRatio (V ++ z) * lowerTheta 90)) := by
      have h := ineq_S2 (lowerRatio (V ++ z)) hs1 hs2
      linarith
    exact div_chain hgr hD2 hD2le hsc hstep (by linarith [hstep, hsZ0])
  · show lowerScale (lowerNormalize ((V ++ z, U) : LowerPair))
      < lowerThreshold ((V ++ z, U) : LowerPair) (279/500) 35 63 63 70
    rw [hthr]
    have hD5 : (0:ℝ) < (1 + lowerRatio U * lowerTheta 35) * (1 + lowerRatio U * lowerTheta 63) :=
      mul_pos hpos35 hpos63
    have hD5le : (1 + lowerRatio U * lowerTheta 35) * (1 + lowerRatio U * lowerTheta 63)
        ≤ gfun (lowerRatio U) := by
      have h1 := prod_mono (lowerRatio U) (lowerTheta 35) (lowerTheta 63) 0.36549 0.440928
        hrU0 (by linarith) (by linarith) t35u t63u
      have h2 := ineq_A5 (lowerRatio U) hr1 hr2
      linarith
    have hNle : (1+lowerRatio (V ++ z)*0.440926)*(1+lowerRatio (V ++ z)*0.576018)
        ≤ (1 + lowerRatio (V ++ z) * lowerTheta 63) * (1 + lowerRatio (V ++ z) * lowerTheta 70) :=
      prod_mono (lowerRatio (V ++ z)) 0.440926 0.576018 (lowerTheta 63) (lowerTheta 70)
        hsZ0 (by norm_num) (by norm_num) t63l t70l
    have hstep : (23/20) * lowerRatio (V ++ z)
        < (279/500)*((1 + lowerRatio (V ++ z) * lowerTheta 63)
            * (1 + lowerRatio (V ++ z) * lowerTheta 70)) := by
      have h := ineq_S5 (lowerRatio (V ++ z)) hs1 hs2
      linarith
    exact div_chain_lt hgr hD5 hD5le hsc hstep (by linarith [hstep, hsZ0])

/-! ## Part G: assembling the fairness statement -/

lemma offered_head (p : LowerPair) (l : LowerLabel) (hl : lowerOffered p l) :
    l.1 ≠ [] ∨ (l = ([], [1]) ∧ lowerMixed p ∧ (lowerH p 2 ∨ ¬ lowerH p 5)) := by
  rcases hl with hm | ⟨_, k, hk, hlk⟩
  · by_cases hmx : lowerMixed p
    · rw [if_pos hmx] at hm
      rcases neh_mixed p l hm with hq | hq
      · exact Or.inl hq
      · refine Or.inr ⟨hq, hmx, ?_⟩
        by_contra hc
        push_neg at hc
        exact mixed_no01 p hc.1 hc.2 l hm (by rw [hq])
    · rw [if_neg hmx] at hm
      exact Or.inl (neh_equal p l hm)
  · left
    subst hlk
    intro hc
    have hlen : (List.replicate k (3:ℕ+)).length = 0 := by rw [show List.replicate k (3:ℕ+) = [] from hc]; rfl
    rw [List.length_replicate] at hlen
    omega

lemma not_mixed_succ (p : LowerPair) (hm : lowerMixed p) :
    ¬ lowerMixed (lowerChild p (([], [1]) : LowerLabel)) := by
  have hq : (lowerNormalize p).1.length % 2 ≠ (lowerNormalize p).2.length % 2 := by
    rw [norm_eq]
    split_ifs
    · exact hm
    · exact fun hc => hm hc.symm
  unfold lowerMixed
  rw [child_eq]
  simp only [List.reverse_nil, List.append_nil, List.length_append, List.length_cons,
    List.length_nil]
  omega

lemma len_pos_of_ne (u : List ℕ+) (h : u ≠ []) : 0 < u.length :=
  Nat.pos_of_ne_zero (fun hc => h (List.eq_nil_of_length_eq_zero hc))

lemma grow_l (h : ℕ → LowerPair) (n : ℕ) (l : LowerLabel)
    (hs : h (n+1) = lowerChild (h n) l) (ho : lowerOrientation h (n+1) = false)
    (hne : l.1 ≠ []) :
    (lowerPhysicalPath h n).1.length < (lowerPhysicalPath h (n+1)).1.length := by
  rw [step_left h n l hs ho]
  have h0 := len_pos_of_ne l.1 hne
  simp only [List.length_append, List.length_reverse]
  omega

lemma grow_r (h : ℕ → LowerPair) (n : ℕ) (l : LowerLabel)
    (hs : h (n+1) = lowerChild (h n) l) (ho : lowerOrientation h (n+1) = true)
    (hne : l.1 ≠ []) :
    (lowerPhysicalPath h n).2.length < (lowerPhysicalPath h (n+1)).2.length := by
  rw [step_right h n l hs ho]
  have h0 := len_pos_of_ne l.1 hne
  simp only [List.length_append, List.length_reverse]
  omega

lemma delay_l (h : ℕ → LowerPair) (n : ℕ) (m : LowerLabel)
    (hsm : h (n+2) = lowerChild (h (n+1)) m) (hmne : m.1 ≠ [])
    (heqlen : (lowerPhysicalPath h (n+1)).1 = (lowerPhysicalPath h n).1)
    (hwid : lowerWidth (lowerPhysicalPath h (n+1)).2
      < lowerWidth (lowerPhysicalPath h (n+1)).1) :
    (lowerPhysicalPath h n).1.length < (lowerPhysicalPath h (n+2)).1.length := by
  have hgrow := grow_l h (n+1) m hsm (orient_of_lt h (n+1) hwid) hmne
  rw [heqlen] at hgrow
  exact hgrow

lemma delay_r (h : ℕ → LowerPair) (n : ℕ) (m : LowerLabel)
    (hsm : h (n+2) = lowerChild (h (n+1)) m) (hmne : m.1 ≠ [])
    (heqlen : (lowerPhysicalPath h (n+1)).2 = (lowerPhysicalPath h n).2)
    (hwid : lowerWidth (lowerPhysicalPath h (n+1)).1
      < lowerWidth (lowerPhysicalPath h (n+1)).2) :
    (lowerPhysicalPath h n).2.length < (lowerPhysicalPath h (n+2)).2.length := by
  have hgrow := grow_r h (n+1) m hsm (orient_of_gt h (n+1) hwid) hmne
  rw [heqlen] at hgrow
  exact hgrow

theorem fairness (t : ℝ) (h : ℕ → LowerPair) (hh : lowerPath t h) :
    lowerWithinTwo (lowerPhysicalPath h) := by
  have hlab : ∀ k, ∃ l, lowerOffered (h k) l ∧ h (k+1) = lowerChild (h k) l := by
    intro k
    obtain ⟨_, _, hstep⟩ := hh (k+1)
    obtain ⟨l, ho, _, he⟩ := hstep k (Nat.lt_succ_self k)
    exact ⟨l, ho, he⟩
  have hstate : ∀ k, lowerState t (h k) := fun k => (hh k).2.1 k (le_refl k)
  intro n
  obtain ⟨l, hol, hsl⟩ := hlab n
  obtain ⟨m, hom, hsm⟩ := hlab (n+1)
  have hmono1 : (lowerPhysicalPath h (n+1)).1.length ≤ (lowerPhysicalPath h (n+2)).1.length :=
    (len_mono h (n+1) m hsm).1
  have hmono2 : (lowerPhysicalPath h (n+1)).2.length ≤ (lowerPhysicalPath h (n+2)).2.length :=
    (len_mono h (n+1) m hsm).2
  have hmhead := offered_head (h (n+1)) m hom
  constructor
  · intro hw
    cases hq : lowerOrientation h (n+1) with
    | false =>
      have hstep1 := step_left h n l hsl hq
      rcases offered_head (h n) l hol with hne | ⟨h01, hmix, _⟩
      · have := grow_l h n l hsl hq hne
        omega
      · subst h01
        have heqlen : (lowerPhysicalPath h (n+1)).1 = (lowerPhysicalPath h n).1 := by
          rw [hstep1]; simp
        have hwid : lowerWidth (lowerPhysicalPath h (n+1)).2
            < lowerWidth (lowerPhysicalPath h (n+1)).1 := by
          rw [hstep1]
          dsimp only
          rw [List.reverse_nil, List.append_nil]
          have := width_append_lt (lowerPhysicalPath h n).2 [1] (by simp)
          linarith
        have hnm : ¬ lowerMixed (h (n+1)) := by
          rw [hsl]; exact not_mixed_succ (h n) hmix
        have hmne : m.1 ≠ [] := by
          rcases hmhead with hq2 | ⟨_, hq2, _⟩
          · exact hq2
          · exact absurd hq2 hnm
        exact delay_l h n m hsm hmne heqlen hwid
    | true =>
      have heq : lowerWidth (lowerPhysicalPath h n).2 = lowerWidth (lowerPhysicalPath h n).1 := by
        rcases lt_or_eq_of_le hw with hlt | heq
        · exact absurd (orient_of_lt h n hlt) (by rw [hq]; simp)
        · exact heq
      have hstep1 := step_right h n l hsl hq
      by_cases hl2 : l.2 = []
      · have hne : l.1 ≠ [] := by
          rcases offered_head (h n) l hol with hne | ⟨h01, _, _⟩
          · exact hne
          · rw [h01] at hl2; simp at hl2
        have heqlen : (lowerPhysicalPath h (n+1)).1 = (lowerPhysicalPath h n).1 := by
          rw [hstep1]; dsimp only; rw [hl2, List.append_nil]
        have hwid : lowerWidth (lowerPhysicalPath h (n+1)).2
            < lowerWidth (lowerPhysicalPath h (n+1)).1 := by
          rw [hstep1]
          dsimp only
          rw [hl2, List.append_nil, ← heq]
          exact width_append_lt (lowerPhysicalPath h n).2 l.1.reverse (by simpa using hne)
        have hform : h (n+1)
            = ((lowerPhysicalPath h n).2 ++ l.1.reverse, (lowerPhysicalPath h n).1) := by
          rw [hsl, child_eq, (norm_phys h n).2 hq, hl2]
          simp
        have hbox : lowerParameterBox
            ((lowerPhysicalPath h n).2 ++ l.1.reverse, (lowerPhysicalPath h n).1) := by
          have hb := (hstate (n+1)).2.2.2
          rwa [hform] at hb
        have hno := tie_no01 (lowerPhysicalPath h n).1 (lowerPhysicalPath h n).2
          l.1.reverse (by simpa using hne) heq.symm hbox
        have hmne : m.1 ≠ [] := by
          rcases hmhead with hq2 | ⟨_, _, hq2⟩
          · exact hq2
          · rw [hform] at hq2
            rcases hq2 with hq2 | hq2
            · exact absurd hq2 hno.1
            · exact absurd hno.2 hq2
        exact delay_l h n m hsm hmne heqlen hwid
      · have hgrow : (lowerPhysicalPath h n).1.length
            < (lowerPhysicalPath h (n+1)).1.length := by
          rw [hstep1]
          dsimp only
          have h0 := len_pos_of_ne l.2 hl2
          simp only [List.length_append]
          omega
        omega
  · intro hw
    have ho := orient_of_gt h n hw
    rcases offered_head (h n) l hol with hne | ⟨h01, hmix, _⟩
    · have := grow_r h n l hsl ho hne
      omega
    · subst h01
      have hstep1 := step_left h n (([], [1]) : LowerLabel) hsl
      have hstep2 := step_right h n (([], [1]) : LowerLabel) hsl ho
      have heqlen : (lowerPhysicalPath h (n+1)).2 = (lowerPhysicalPath h n).2 := by
        rw [hstep2]; dsimp only; rw [List.reverse_nil, List.append_nil]
      have hwid : lowerWidth (lowerPhysicalPath h (n+1)).1
          < lowerWidth (lowerPhysicalPath h (n+1)).2 := by
        rw [hstep2]
        dsimp only
        rw [List.reverse_nil, List.append_nil]
        have := width_append_lt (lowerPhysicalPath h n).1 [1] (by simp)
        linarith
      have hnm : ¬ lowerMixed (h (n+1)) := by
        rw [hsl]; exact not_mixed_succ (h n) hmix
      have hmne : m.1 ≠ [] := by
        rcases hmhead with hq2 | ⟨_, hq2, _⟩
        · exact hq2
        · exact absurd hq2 hnm
      exact delay_r h n m hsm hmne heqlen hwid

end FairCore

theorem solution (hf : ∀ (p : LowerPair), lowerGood p → lowerParameterBox p → let q := lowerNormalize p; lowerWidth (q.1 ++ [2]) < lowerWidth q.2 ∧ lowerWidth (q.1 ++ [3]) < lowerWidth q.2 ∧ lowerWidth (q.1 ++ [1,1]) < lowerWidth q.2 ∧ lowerWidth (q.2 ++ [1]) < lowerWidth q.1)
    (t : ℝ) (h : ℕ → LowerPair) (hh : lowerPath t h) : lowerWithinTwo (lowerPhysicalPath h) :=
  FairCore.fairness t h hh

#print axioms solution
