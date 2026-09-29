-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_tie2_relaxation
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T17:11:57.04139+00:00
-- url     : https://prove2.me/submissions/298b88fc-c3f0-48a0-a705-0f1a835da63c

import Definitions.Def_Freiman_lowerCover
import Mathlib.Tactic
import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_prefixEval_difference
import Theorems.Thm_Freiman_continuant_denominator_pos
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_append
import Theorems.Thm_Freiman_prefixEval_mobius
import Theorems.Thm_Freiman_continuant_determinant
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_range
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_swap_nontie


open Freiman
namespace CDUnique15

private def GoodHead : List ℕ+ → Prop
  | [] => True
  | a :: _ => 2 ≤ (a : ℕ)

private theorem goodHead_prefix (u v : List ℕ+) (h : GoodHead (u ++ v)) : GoodHead u := by
  cases u with
  | nil => trivial
  | cons a u => exact h

private theorem goodHead_append (u v : List ℕ+) (hu : GoodHead u) (hne : u ≠ []) :
    GoodHead (u ++ v) := by
  cases u with
  | nil => exact (hne rfl).elim
  | cons a u => exact hu

private theorem cd_snoc (w : List ℕ+) (a : ℕ+) :
    lowerCD (w ++ [a]) =
      ((lowerCD w).2, (lowerCD w).1 + (a : ℕ) * (lowerCD w).2) := by
  unfold lowerCD
  simp [List.foldl_append]

private theorem snd_pos (w : List ℕ+) : 0 < (lowerCD w).2 := by
  induction w using List.reverseRecOn with
  | nil => decide
  | append_singleton w a ih =>
      rw [cd_snoc]
      have hp := Nat.mul_pos a.pos ih
      dsimp only
      omega

private theorem fst_pos (w : List ℕ+) (h : w ≠ []) : 0 < (lowerCD w).1 := by
  induction w using List.reverseRecOn with
  | nil => exact (h rfl).elim
  | append_singleton w a ih =>
      rw [cd_snoc]
      exact snd_pos w

private theorem cd_strict (w : List ℕ+) (h : GoodHead w) : (lowerCD w).1 < (lowerCD w).2 := by
  induction w using List.reverseRecOn with
  | nil => decide
  | append_singleton w a ih =>
      rw [cd_snoc]
      dsimp only
      by_cases hw : w = []
      · subst w
        have ha : 2 ≤ (a : ℕ) := h
        simpa [lowerCD] using (show 1 < (a : ℕ) by omega)
      · have hp := fst_pos w hw
        have hm := Nat.le_mul_of_pos_left (lowerCD w).2 a.pos
        omega

private theorem injective (u v : List ℕ+) (hu : GoodHead u) (hv : GoodHead v)
    (heq : lowerCD u = lowerCD v) : u = v := by
  induction u using List.reverseRecOn generalizing v with
  | nil =>
      by_cases hn : v = []
      · exact hn.symm
      · have hp := fst_pos v hn
        have hz := congrArg Prod.fst heq
        change 0 = (lowerCD v).1 at hz
        omega
  | append_singleton u a ih =>
      rcases List.eq_nil_or_concat' v with rfl | ⟨v,b,rfl⟩
      · have hz := congrArg Prod.fst heq
        rw [cd_snoc] at hz
        have hp := snd_pos u
        change (lowerCD u).2 = 0 at hz
        omega
      · have hgu := goodHead_prefix u [a] hu
        have hgv := goodHead_prefix v [b] hv
        have hdu := cd_strict u hgu
        have hdv := cd_strict v hgv
        have hs := congrArg Prod.fst heq
        have ht := congrArg Prod.snd heq
        rw [cd_snoc,cd_snoc] at hs ht
        dsimp only at hs ht
        have hm := congrArg (fun z : ℕ × ℕ => z.2 % z.1) heq
        rw [cd_snoc,cd_snoc] at hm
        simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hdu,
          Nat.mod_eq_of_lt hdv] at hm
        have hc : lowerCD u = lowerCD v := Prod.ext hm hs
        have huv := ih v hgu hgv hc
        subst v
        have hab : (a : ℕ) = (b : ℕ) := by
          apply Nat.eq_of_mul_eq_mul_right (snd_pos u)
          exact Nat.add_left_cancel ht
        have hab' : a = b := Subtype.ext hab
        rw [hab']

private theorem core_append_head (c : LowerPair) (hc : c ∈ lowerCores)
    (u v : List ℕ+) : GoodHead (c.1 ++ u) ∧ GoodHead (c.2 ++ v) := by
  simp only [lowerCores, List.mem_append, List.mem_map] at hc
  rcases hc with hc | ⟨d,hd,rfl⟩
  · simp only [lowerBaseCores, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [GoodHead]
  · simp only [lowerBaseCores, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [GoodHead]

private theorem admissible_goodHead (p : LowerPair) (hp : lowerAdmissible p) :
    GoodHead p.1 ∧ GoodHead p.2 := by
  rcases hp.1 with ⟨c,hc,u,v,rfl,hu,hv⟩
  exact core_append_head c hc u v

end CDUnique15


namespace TieAlgebra14

private def A (c d : ℝ) : ℝ := 4*c*d - 3*c^2
private def B (c d : ℝ) : ℝ := 2*d^2 - 4*c*d + 5*c^2
private def cross (c1 d1 c2 d2 : ℝ) : ℝ := c1*d2 - c2*d1
private def factor (c1 d1 c2 d2 : ℝ) : ℝ :=
  4*c1*c2 + 3*c1*d2 + 3*c2*d1 - 4*d1*d2

private theorem resultant {c1 d1 c2 d2 : ℝ}
    (hA : A c1 d1 = A c2 d2) (hB : B c1 d1 = B c2 d2) :
    cross c1 d1 c2 d2 * factor c1 d1 c2 d2 = 0 := by
  have h : A c1 d1 * B c2 d2 - A c2 d2 * B c1 d1 = 0 := by rw [hA, hB]; ring
  have hid : A c1 d1 * B c2 d2 - A c2 d2 * B c1 d1 =
      -2 * cross c1 d1 c2 d2 * factor c1 d1 c2 d2 := by
    simp only [A, B, cross, factor]
    ring
  rw [hid] at h
  nlinarith

private theorem finish {c1 d1 c2 d2 : ℝ}
    (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hB : B c1 d1 = B c2 d2)
    (hcross : cross c1 d1 c2 d2 = 0) : c1 = c2 ∧ d1 = d2 := by
  have hid : B c1 d1 * d2^2 - B c2 d2 * d1^2 =
      cross c1 d1 c2 d2 *
        (-4*d1*d2 + 5*c1*d2 + 5*c2*d1) := by
    simp only [B, cross]
    ring
  rw [hcross] at hid
  have hweighted : B c1 d1 * d2^2 = B c2 d2 * d1^2 := by
    linarith
  have hsame : B c2 d2 * d1^2 = B c2 d2 * d2^2 := by
    calc
      B c2 d2 * d1^2 = B c1 d1 * d2^2 := hweighted.symm
      _ = B c2 d2 * d2^2 := by rw [hB]
  have hBpos : 0 < B c2 d2 := by
    have hs : 0 < d2^2 := sq_pos_of_pos hd2
    have h1 := sq_nonneg (d2 - 2*c2)
    have h2 := sq_nonneg c2
    simp only [B]
    nlinarith
  have hdsq : d1^2 = d2^2 := by nlinarith [hsame]
  have hd : d1 = d2 := by nlinarith
  have hcprod : (c1-c2)*d2 = 0 := by
    simp only [cross] at hcross
    rw [hd] at hcross
    nlinarith
  have hc : c1 = c2 := by
    rcases mul_eq_zero.mp hcprod with h | h
    · linarith
    · exact (ne_of_gt hd2 h).elim
  exact ⟨hc, hd⟩

private theorem injective_below_twice
    {c1 d1 c2 d2 : ℝ}
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hA : 4*c1*d1 - 3*c1^2 = 4*c2*d2 - 3*c2^2)
    (hB : 2*d1^2 - 4*c1*d1 + 5*c1^2 = 2*d2^2 - 4*c2*d2 + 5*c2^2)
    (h1 : d1 < 2*c1) (h2 : d2 < 2*c2) : c1 = c2 ∧ d1 = d2 := by
  have hres := resultant (c1 := c1) (d1 := d1) (c2 := c2) (d2 := d2) hA hB
  have hg1 : 0 < 2*c1-d1 := by linarith
  have hg2 : 0 < 2*c2-d2 := by linarith
  have hp1 : 0 < (2*c1-d1)*(2*c2-d2) := mul_pos hg1 hg2
  have hp2 : 0 < (2*c1-d1)*d2 := mul_pos hg1 hd2
  have hp3 : 0 < (2*c2-d2)*d1 := mul_pos hg2 hd1
  have hfac : 0 < factor c1 d1 c2 d2 := by
    simp only [factor]
    nlinarith
  have hcross : cross c1 d1 c2 d2 = 0 :=
    (mul_eq_zero.mp hres).resolve_right (ne_of_gt hfac)
  exact finish hd1 hd2 hB hcross

private theorem injective_above_twice
    {c1 d1 c2 d2 : ℝ}
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hA : 4*c1*d1 - 3*c1^2 = 4*c2*d2 - 3*c2^2)
    (hB : 2*d1^2 - 4*c1*d1 + 5*c1^2 = 2*d2^2 - 4*c2*d2 + 5*c2^2)
    (h1 : 2*c1 < d1) (h2 : 2*c2 < d2) : c1 = c2 ∧ d1 = d2 := by
  have hres := resultant (c1 := c1) (d1 := d1) (c2 := c2) (d2 := d2) hA hB
  have hg1 : 0 < d1-2*c1 := by linarith
  have hg2 : 0 < d2-2*c2 := by linarith
  have hp : 0 < (d1-2*c1)*(d2-2*c2) := mul_pos hg1 hg2
  have hle1 : d1-2*c1 ≤ d1 := by linarith
  have hle2 : d2-2*c2 ≤ d2 := by linarith
  have hp1 : (d1-2*c1)*(d2-2*c2) ≤ (d1-2*c1)*d2 :=
    mul_le_mul_of_nonneg_left hle2 hg1.le
  have hp2 : (d1-2*c1)*(d2-2*c2) ≤ (d2-2*c2)*d1 := by
    nlinarith [mul_le_mul_of_nonneg_right hle1 hg2.le]
  have hfac : factor c1 d1 c2 d2 < 0 := by
    simp only [factor]
    nlinarith
  have hcross : cross c1 d1 c2 d2 = 0 :=
    (mul_eq_zero.mp hres).resolve_right (ne_of_lt hfac)
  exact finish hd1 hd2 hB hcross


end TieAlgebra14


open Freiman
namespace M7TieWidth14
private theorem cd_eq (w : List ℕ+) :
    lowerCD w = (wordContinuantPrevQ w, wordContinuantQ w) := by
  have h : ∀ (v : List ℕ) (m : (ℕ × ℕ) × (ℕ × ℕ)),
      (v.foldl (fun d a => ((d.1.2, (a : ℕ) * d.1.2 + d.1.1),
        (d.2.2, (a : ℕ) * d.2.2 + d.2.1))) m).2 =
      v.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) m.2 := by
    intro v
    induction v with
    | nil => intro m; rfl
    | cons a v ih =>
      intro m
      simp only [List.foldl_cons]
      rw [ih]
      simp only [Nat.add_comm]
  simpa [lowerCD, wordContinuantPrevQ, wordContinuantQ, wordContinuantData]
    using (h (w.flatMap fun a => [(a : ℕ)]) ((1,0),(0,1))).symm

private theorem q_pos (w : List ℕ+) : 0 < ((lowerCD w).2 : ℝ) := by
  rw [cd_eq]
  exact_mod_cast continuant_denominator_pos w

private theorem tails :
    lowerAlpha ∈ Set.Icc (0 : ℝ) 1 ∧
    lowerBeta ∈ Set.Icc (0 : ℝ) 1 ∧ lowerAlpha < lowerBeta := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  have hlo : 3 < Real.sqrt (21 : ℝ) := by nlinarith
  have hhi : Real.sqrt (21 : ℝ) < 5 := by nlinarith
  dsimp [lowerAlpha, lowerBeta, Set.mem_Icc]
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  · linarith

private noncomputable def den (w : List ℕ+) : ℝ :=
  (((lowerCD w).2 : ℝ) + lowerBeta * (lowerCD w).1) *
    (((lowerCD w).2 : ℝ) + lowerAlpha * (lowerCD w).1)

private def coeffA (w : List ℕ+) : ℚ :=
  4 * ((lowerCD w).1 : ℚ) * (lowerCD w).2 - 3 * ((lowerCD w).1 : ℚ)^2
private def coeffB (w : List ℕ+) : ℚ :=
  2 * ((lowerCD w).2 : ℚ)^2 - 4 * ((lowerCD w).1 : ℚ) * (lowerCD w).2 +
    5 * ((lowerCD w).1 : ℚ)^2

private theorem width_eq (w : List ℕ+) : lowerWidth w = (lowerBeta-lowerAlpha) / den w := by
  unfold lowerWidth
  rw [prefixEval_difference w lowerBeta lowerAlpha tails.2.1 tails.1,
    abs_of_pos (sub_pos.mpr tails.2.2)]
  simp only [den, cd_eq]

private theorem den_coefficients (w : List ℕ+) :
    den w = (3 * (coeffB w : ℝ) + Real.sqrt 21 * (coeffA w : ℝ)) / 6 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  simp only [den, coeffA, coeffB, lowerAlpha, lowerBeta]
  push_cast
  linear_combination (((lowerCD w).1 : ℝ)^2 / 12) * hs

private theorem rational_coefficients (a b : ℚ)
    (h : (a : ℝ) + Real.sqrt 21 * (b : ℝ) = 0) : a = 0 ∧ b = 0 := by
  have hi : Irrational (Real.sqrt (21:ℝ)) := by norm_num
  by_cases hb : b = 0
  · subst b
    simp only [Rat.cast_zero, mul_zero, add_zero] at h
    exact ⟨by exact_mod_cast h,rfl⟩
  · exfalso
    apply hi
    refine ⟨-a/b, ?_⟩
    push_cast
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    apply (div_eq_iff hb').mpr
    linarith

private theorem coefficients_of_width (u v : List ℕ+) (hw : lowerWidth u = lowerWidth v) :
    coeffA u = coeffA v ∧ coeffB u = coeffB v := by
  have hd : den u = den v := by
    apply inv_injective
    apply mul_left_cancel₀ (ne_of_gt (sub_pos.mpr tails.2.2))
    simpa only [width_eq, div_eq_mul_inv] using hw
  rw [den_coefficients,den_coefficients] at hd
  have hlin : ((3*(coeffB u-coeffB v) : ℚ) : ℝ) +
      Real.sqrt 21 * ((coeffA u-coeffA v : ℚ) : ℝ) = 0 := by
    push_cast
    linarith
  obtain ⟨hb,ha⟩ := rational_coefficients _ _ hlin
  constructor <;> linarith

private theorem cd_eq_of_width_same_side (u v : List ℕ+) (hw : lowerWidth u = lowerWidth v)
    (hside : ((1/2:ℝ) < lowerRatio u ∧ (1/2:ℝ) < lowerRatio v) ∨
      (lowerRatio u < (1/2:ℝ) ∧ lowerRatio v < (1/2:ℝ))) :
    lowerCD u = lowerCD v := by
  have hcoeff := coefficients_of_width u v hw
  have hA : 4*((lowerCD u).1:ℝ)*(lowerCD u).2-3*((lowerCD u).1:ℝ)^2 =
      4*((lowerCD v).1:ℝ)*(lowerCD v).2-3*((lowerCD v).1:ℝ)^2 := by
    have h := hcoeff.1
    dsimp only [coeffA] at h
    exact_mod_cast h
  have hB : 2*((lowerCD u).2:ℝ)^2-4*((lowerCD u).1:ℝ)*(lowerCD u).2+5*((lowerCD u).1:ℝ)^2 =
      2*((lowerCD v).2:ℝ)^2-4*((lowerCD v).1:ℝ)*(lowerCD v).2+5*((lowerCD v).1:ℝ)^2 := by
    have h := hcoeff.2
    dsimp only [coeffB] at h
    exact_mod_cast h
  have heq : ((lowerCD u).1:ℝ) = ((lowerCD v).1:ℝ) ∧
      ((lowerCD u).2:ℝ) = ((lowerCD v).2:ℝ) := by
    rcases hside with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · apply TieAlgebra14.injective_below_twice (q_pos u) (q_pos v)
        (Nat.cast_nonneg _) (Nat.cast_nonneg _) hA hB
      · have hx := (lt_div_iff₀ (q_pos u)).mp hu
        linarith
      · have hx := (lt_div_iff₀ (q_pos v)).mp hv
        linarith
    · apply TieAlgebra14.injective_above_twice (q_pos u) (q_pos v)
        (Nat.cast_nonneg _) (Nat.cast_nonneg _) hA hB
      · have hx := (div_lt_iff₀ (q_pos u)).mp hu
        linarith
      · have hx := (div_lt_iff₀ (q_pos v)).mp hv
        linarith
  apply Prod.ext
  · exact_mod_cast heq.1
  · exact_mod_cast heq.2

end M7TieWidth14


open Freiman
namespace CDUnique15

private theorem ratio_pos (w : List ℕ+) (hw : w ≠ []) : 0 < lowerRatio w := by
  unfold lowerRatio
  exact div_pos (by exact_mod_cast fst_pos w hw) (by exact_mod_cast snd_pos w)

private theorem ratio_two_lt_half (w : List ℕ+) (hw : w ≠ []) :
    lowerRatio (w ++ [2]) < (1 / 2 : ℝ) := by
  rw [lowerEarlyTerminal_ratio_append]
  change 1 / (2 + lowerRatio w) < 1 / 2
  have hr := ratio_pos w hw
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith

private theorem width_ne_same_side_of_parity (u v : List ℕ+) (hu : GoodHead u)
    (hv : GoodHead v) (hp : u.length % 2 ≠ v.length % 2)
    (hside : ((1 / 2 : ℝ) < lowerRatio u ∧ (1 / 2 : ℝ) < lowerRatio v) ∨
      (lowerRatio u < (1 / 2 : ℝ) ∧ lowerRatio v < (1 / 2 : ℝ))) :
    lowerWidth u ≠ lowerWidth v := by
  intro hw
  have hcd := M7TieWidth14.cd_eq_of_width_same_side u v hw hside
  have heq := injective u v hu hv hcd
  exact hp (congrArg (fun w : List ℕ+ => w.length % 2) heq)

private theorem width_ne_append_two (u v : List ℕ+) (hu : GoodHead u) (hv : GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ []) (hp : u.length % 2 ≠ v.length % 2) :
    lowerWidth (u ++ [2]) ≠ lowerWidth (v ++ [2]) := by
  apply width_ne_same_side_of_parity _ _
    (goodHead_append _ _ hu hnu) (goodHead_append _ _ hv hnv)
  · simp only [List.length_append, List.length_singleton]
    omega
  · exact Or.inr ⟨ratio_two_lt_half u hnu, ratio_two_lt_half v hnv⟩

end CDUnique15


open Freiman
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Cross16

private theorem cd_eq (w : List ℕ+) :
    lowerCD w = (wordContinuantPrevQ w, wordContinuantQ w) := by
  have h : ∀ (v : List ℕ) (m : (ℕ × ℕ) × (ℕ × ℕ)),
      (v.foldl (fun d a => ((d.1.2, (a : ℕ) * d.1.2 + d.1.1),
        (d.2.2, (a : ℕ) * d.2.2 + d.2.1))) m).2 =
      v.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) m.2 := by
    intro v
    induction v with
    | nil => intro m; rfl
    | cons a v ih =>
      intro m
      simp only [List.foldl_cons]
      rw [ih]
      simp only [Nat.add_comm]
  simpa [lowerCD, wordContinuantPrevQ, wordContinuantQ, wordContinuantData]
    using (h (w.flatMap fun a => [(a : ℕ)]) ((1,0),(0,1))).symm

private theorem q_pos (w : List ℕ+) : 0 < ((lowerCD w).2 : ℝ) := by
  rw [cd_eq]
  exact_mod_cast continuant_denominator_pos w

private theorem algebra_classify {c d C D : ℝ}
    (hd : 0 < d) (hD : 0 < D) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hA : 4*c*d-3*c^2 = 4*C*D-3*C^2)
    (hB : 2*d^2-4*c*d+5*c^2 = 2*D^2-4*C*D+5*C^2) :
    (c = C ∧ d = D) ∨ (5*C = -3*c+4*d ∧ 5*D = 4*c+3*d) := by
  have hres : (c*D-C*d) * (4*c*C+3*c*D+3*C*d-4*d*D) = 0 := by
    have hz : (4*c*d-3*c^2)*(2*D^2-4*C*D+5*C^2) -
        (4*C*D-3*C^2)*(2*d^2-4*c*d+5*c^2) = 0 := by rw [hA,hB]; ring
    nlinarith [hz]
  rcases mul_eq_zero.mp hres with hcross | hfac
  · left
    have hid : (2*d^2-4*c*d+5*c^2)*D^2 -
        (2*D^2-4*C*D+5*C^2)*d^2 =
        (c*D-C*d)*(-4*d*D+5*c*D+5*C*d) := by ring
    rw [hcross] at hid
    have hsame : (2*D^2-4*C*D+5*C^2)*d^2 =
        (2*D^2-4*C*D+5*C^2)*D^2 := by nlinarith [hid]
    have hBp : 0 < 2*D^2-4*C*D+5*C^2 := by
      nlinarith [sq_pos_of_pos hD, sq_nonneg (D-2*C), sq_nonneg C]
    have hde : d = D := by nlinarith [hsame]
    have hce : c = C := by
      rw [hde] at hcross
      nlinarith
    exact ⟨hce,hde⟩
  · right
    have hcubic : D*(25*D^2-16*c^2-24*c*d-9*d^2) = 0 := by
      linear_combination (10*C-31/2*D)*hA + (6*C-25/2*D)*hB - 4*d*hfac
    have hsquare : (5*D)^2 = (4*c+3*d)^2 := by
      have hn : D ≠ 0 := ne_of_gt hD
      apply (mul_left_cancel₀ hn)
      nlinarith [hcubic]
    have hDe : 5*D = 4*c+3*d := by
      have hp : 0 < 4*c+3*d := by positivity
      nlinarith
    have hCe : 5*C = -3*c+4*d := by
      have hprod : D*(5*C+3*c-4*d) = 0 := by
        calc
          D*(5*C+3*c-4*d) = C*(5*D)+D*(3*c-4*d) := by ring
          _ = C*(4*c+3*d)+D*(3*c-4*d) := by rw [hDe]
          _ = 0 := by nlinarith [hfac]
      have := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hD)
      linarith
    exact ⟨hCe,hDe⟩

private theorem cd_classify (u v : List ℕ+) (hw : lowerWidth u = lowerWidth v) :
    lowerCD u = lowerCD v ∨
      (5*((lowerCD v).1:ℝ) = -3*((lowerCD u).1:ℝ)+4*(lowerCD u).2 ∧
       5*((lowerCD v).2:ℝ) = 4*((lowerCD u).1:ℝ)+3*(lowerCD u).2) := by
  have hh := M7TieWidth14.coefficients_of_width u v hw
  have hA : 4*((lowerCD u).1:ℝ)*(lowerCD u).2-3*((lowerCD u).1:ℝ)^2 =
      4*((lowerCD v).1:ℝ)*(lowerCD v).2-3*((lowerCD v).1:ℝ)^2 := by
    have h := hh.1
    dsimp [M7TieWidth14.coeffA] at h
    exact_mod_cast h
  have hB : 2*((lowerCD u).2:ℝ)^2-4*((lowerCD u).1:ℝ)*(lowerCD u).2+5*((lowerCD u).1:ℝ)^2 =
      2*((lowerCD v).2:ℝ)^2-4*((lowerCD v).1:ℝ)*(lowerCD v).2+5*((lowerCD v).1:ℝ)^2 := by
    have h := hh.2
    dsimp [M7TieWidth14.coeffB] at h
    exact_mod_cast h
  rcases algebra_classify (q_pos u) (q_pos v) (by positivity) (by positivity) hA hB with h | h
  · left
    apply Prod.ext
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  · exact Or.inr h


private theorem two_virtual_nontie (u v : List ℕ+) (hu : lowerEnds u [3,1]) :
    lowerWidth ((u++[2])++[1]) ≠ lowerWidth (v++[2]) := by
  intro ht
  obtain ⟨P,rfl⟩ := hu
  have hP := q_pos P
  have hv := (lowerEarlyTerminal_ratio_range v).2
  have hvc : ((lowerCD v).1:ℝ) ≤ (lowerCD v).2 := by
    rw [lowerRatio, div_le_one (q_pos v)] at hv
    exact hv
  have hvp := q_pos v
  have hpc : (0:ℝ) ≤ (lowerCD P).1 := by positivity
  have he1 : lowerCD (((P++[3,1])++[2])++[1]) =
      (3*(lowerCD P).1+11*(lowerCD P).2,
       4*(lowerCD P).1+15*(lowerCD P).2) := by
    simp [lowerCD,List.foldl_append]
    omega
  have he2 : lowerCD (v++[2]) = ((lowerCD v).2,(lowerCD v).1+2*(lowerCD v).2) := by
    simp [lowerCD,List.foldl_append]
  rcases cd_classify _ _ ht with he | he
  · rw [he1,he2] at he
    have h1 : (3*((lowerCD P).1:ℝ)+11*(lowerCD P).2) = (lowerCD v).2 := by exact_mod_cast congrArg Prod.fst he
    have h2 : (4*((lowerCD P).1:ℝ)+15*(lowerCD P).2) = (lowerCD v).1+2*(lowerCD v).2 := by exact_mod_cast congrArg Prod.snd he
    nlinarith
  · rw [he1,he2] at he
    simp only [Prod.fst,Prod.snd] at he
    push_cast at he
    nlinarith [he.1,he.2]
end Cross16
namespace Cross16
private theorem equal_endpoint_swap (x y : List ℕ+) (h : lowerWidth x ≠ lowerWidth y)
    (upper : Bool) :
    (let w := lowerEqualWords (x,y) upper;
      4+prefixEval w.1 lowerTau+prefixEval w.2 lowerTau) =
    (let w := lowerEqualWords (y,x) upper;
      4+prefixEval w.1 lowerTau+prefixEval w.2 lowerTau) := by
  have hn : lowerNormalize (y,x) = lowerNormalize (x,y) := by
    unfold lowerNormalize
    by_cases hw : lowerWidth y ≤ lowerWidth x
    · have hn : ¬ lowerWidth x ≤ lowerWidth y := fun hh => h (le_antisymm hh hw)
      simp [hw,hn]
    · have hh := (lt_of_not_ge hw).le
      simp [hw,hh]
  unfold lowerEqualWords
  rw [hn]
  by_cases hw : lowerWidth y ≤ lowerWidth x
  · have hh : ¬ lowerWidth x ≤ lowerWidth y := fun hh => h (le_antisymm hh hw)
    simp [hw,hh]
    ring
  · have hh := (lt_of_not_ge hw).le
    simp [hw,hh]
    ring

private theorem mixed_partial_swap (x y : List ℕ+)
    (hp : x.length%2 ≠ y.length%2)
    (hne : lowerWidth x ≠ lowerWidth y)
    (hnx : lowerWidth (x++[1]) ≠ lowerWidth y)
    (upper : Bool) (hu : upper = decide (x.length%2=0)) :
    lowerEndpoint (x,y) upper = lowerEndpoint (y,x) upper := by
  have hu' : upper ≠ decide (y.length%2=0) := by
    subst upper
    rcases Nat.mod_two_eq_zero_or_one x.length with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y.length with hy | hy <;> simp_all
  unfold lowerEndpoint lowerEndpointWords
  simp only [Prod.fst,Prod.snd,if_neg hp,if_neg hp.symm]
  by_cases hw : lowerWidth y ≤ lowerWidth x
  · have hh : ¬ lowerWidth x ≤ lowerWidth y := fun hh => hne (le_antisymm hh hw)
    simp only [hw,hh,if_true,if_false,hu]
    exact equal_endpoint_swap (x++[1]) y hnx (decide (x.length%2=0))
  · have hh := (lt_of_not_ge hw).le
    simp only [hw,hh,if_true,if_false,if_neg hu']
    unfold lowerNaturalWords
    ring

private theorem two_complementary_swap (u v : List ℕ+)
    (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ []) (hp : u.length%2 ≠ v.length%2)
    (he : lowerEnds u [3,1]) :
    (if v.length%2=0 then
      lowerEndpoint (u++[2],v++[2]) true = lowerEndpoint (v++[2],u++[2]) true
    else lowerEndpoint (u++[2],v++[2]) false = lowerEndpoint (v++[2],u++[2]) false) := by
  have hn := CDUnique15.width_ne_append_two u v hu hv hnu hnv hp
  have hnx := two_virtual_nontie u v he
  have hpar : (u++[2]).length%2 ≠ (v++[2]).length%2 := by simp; omega
  split_ifs with hv0
  · apply mixed_partial_swap _ _ hpar hn hnx
    have hu1 : u.length%2=1 := by omega
    simp [hu1,Nat.add_mod]
  · apply mixed_partial_swap _ _ hpar hn hnx
    have hu0 : u.length%2=0 := by omega
    simp [hu0,Nat.add_mod]
end Cross16
namespace Cross16

private theorem two_virtual_nontie_of_ratio (u v : List ℕ+)
    (hu : (1/4:ℝ) ≤ lowerRatio u) (hv : CDUnique15.GoodHead v) :
    lowerWidth ((u++[2])++[1]) ≠ lowerWidth (v++[2]) := by
  intro ht
  have hU := q_pos u
  have hV := q_pos v
  have huc : (0:ℝ) ≤ (lowerCD u).1 := by positivity
  have hvc : ((lowerCD v).1:ℝ) < (lowerCD v).2 := by
    exact_mod_cast CDUnique15.cd_strict v hv
  have hbound : ((lowerCD u).2:ℝ) ≤ 4*(lowerCD u).1 := by
    rw [lowerRatio,le_div_iff₀ hU] at hu
    linarith
  have he1 : lowerCD ((u++[2])++[1]) =
      ((lowerCD u).1+2*(lowerCD u).2,(lowerCD u).1+3*(lowerCD u).2) := by
    simp [lowerCD,List.foldl_append]; omega
  have he2 : lowerCD (v++[2]) = ((lowerCD v).2,(lowerCD v).1+2*(lowerCD v).2) := by
    simp [lowerCD,List.foldl_append]
  rcases cd_classify _ _ ht with he | he
  · rw [he1,he2] at he
    have h1 : ((lowerCD u).1:ℝ)+2*(lowerCD u).2=(lowerCD v).2 := by
      exact_mod_cast congrArg Prod.fst he
    have h2 : ((lowerCD u).1:ℝ)+3*(lowerCD u).2=(lowerCD v).1+2*(lowerCD v).2 := by
      exact_mod_cast congrArg Prod.snd he
    have hz : (0:ℝ) ≤ (lowerCD v).1 := by positivity
    linarith
  · rw [he1,he2] at he
    simp only [Prod.fst,Prod.snd] at he
    push_cast at he
    linarith [he.1,he.2]

private theorem two_complementary_swap_of_ratio (u v : List ℕ+)
    (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ []) (hp : u.length%2 ≠ v.length%2)
    (he : (1/4:ℝ) ≤ lowerRatio u) :
    (if v.length%2=0 then
      lowerEndpoint (u++[2],v++[2]) true = lowerEndpoint (v++[2],u++[2]) true
    else lowerEndpoint (u++[2],v++[2]) false = lowerEndpoint (v++[2],u++[2]) false) := by
  have hn := CDUnique15.width_ne_append_two u v hu hv hnu hnv hp
  have hnx := two_virtual_nontie_of_ratio u v he hv
  have hpar : (u++[2]).length%2 ≠ (v++[2]).length%2 := by simp; omega
  split_ifs with hv0
  · apply mixed_partial_swap _ _ hpar hn hnx
    have hu1 : u.length%2=1 := by omega
    simp [hu1,Nat.add_mod]
  · apply mixed_partial_swap _ _ hpar hn hnx
    have hu0 : u.length%2=0 := by omega
    simp [hu0,Nat.add_mod]
end Cross16

open Freiman
set_option maxHeartbeats 0

namespace P97Child

private theorem reflected_cross_of_nonties (a b : List ℕ+)
    (hn1 : LowerEarlyTerminalNoTies (a,b++[1]))
    (hn2 : LowerEarlyTerminalNoTies (a,b++[2]))
    (h12 : lowerEndpoint (a,b++[2]) false < lowerEndpoint (a,b++[1]) true)
    (h21 : lowerEndpoint (a,b++[1]) false < lowerEndpoint (a,b++[2]) true) :
    lowerEndpoint (b++[2],a) false < lowerEndpoint (b++[1],a) true ∧
    lowerEndpoint (b++[1],a) false < lowerEndpoint (b++[2],a) true := by
  have h1f := lowerEarlyTerminal_endpoint_swap_nontie (a,b++[1]) hn1 false
  have h1t := lowerEarlyTerminal_endpoint_swap_nontie (a,b++[1]) hn1 true
  have h2f := lowerEarlyTerminal_endpoint_swap_nontie (a,b++[2]) hn2 false
  have h2t := lowerEarlyTerminal_endpoint_swap_nontie (a,b++[2]) hn2 true
  constructor
  · simpa [h2f, h1t] using h12
  · simpa [h1f, h2t] using h21

end P97Child

open Freiman
namespace Cross16
set_option maxHeartbeats 0

private theorem ratio_one_gt_half (u : List ℕ+) (hu : CDUnique15.GoodHead u) :
    (1/2:ℝ) < lowerRatio (u++[1]) := by
  have hs := CDUnique15.cd_strict u hu
  have hd := CDUnique15.snd_pos u
  have hr : lowerRatio u < 1 := by
    rw [lowerRatio,div_lt_one (by exact_mod_cast hd)]
    exact_mod_cast hs
  have hr0 : 0 ≤ lowerRatio u := by unfold lowerRatio; positivity
  rw [lowerEarlyTerminal_ratio_append]
  norm_num only [List.reverse_singleton, prefixEval, PNat.val_ofNat, Nat.cast_one]
  rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
  linarith

private theorem one_nonties (u v : List ℕ+)
    (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ []) (hp : u.length%2 ≠ v.length%2)
    (hwu : lowerWidth (u++[1]) < lowerWidth v)
    (hwv : lowerWidth (v++[1]) < lowerWidth u) :
    LowerEarlyTerminalNoTies (u++[1],v++[1]) := by
  have hgu := CDUnique15.goodHead_append u [1] hu hnu
  have hgv := CDUnique15.goodHead_append v [1] hv hnv
  have hguu := CDUnique15.goodHead_append (u++[1]) [1] hgu (by simp)
  have hgvv := CDUnique15.goodHead_append (v++[1]) [1] hgv (by simp)
  refine ⟨?_, fun _ => ⟨?_, ?_⟩⟩
  · apply CDUnique15.width_ne_same_side_of_parity _ _ hgu hgv
    · simp only [List.length_append,List.length_singleton]; omega
    · exact Or.inl ⟨ratio_one_gt_half u hu,ratio_one_gt_half v hv⟩
  · intro ht
    have hc := M7TieWidth14.cd_eq_of_width_same_side _ _ ht
      (Or.inl ⟨ratio_one_gt_half (u++[1]) hgu,ratio_one_gt_half v hv⟩)
    have he := CDUnique15.injective _ _ hguu hgv hc
    have he' : u++[1] = v := List.append_cancel_right he
    exact hwu.ne (congrArg lowerWidth he')
  · intro ht
    have hc := M7TieWidth14.cd_eq_of_width_same_side _ _ ht
      (Or.inl ⟨ratio_one_gt_half u hu,ratio_one_gt_half (v++[1]) hgv⟩)
    have he := CDUnique15.injective _ _ hgu hgvv hc
    have he' : u = v++[1] := List.append_cancel_right he
    exact hwv.ne (congrArg lowerWidth he'.symm)
end Cross16
namespace Cross16

private theorem one_two_other_virtual_nontie (u v : List ℕ+)
    (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ []) (he : lowerEnds u [1]) :
    lowerWidth (u++[1]) ≠ lowerWidth ((v++[2])++[1]) := by
  intro ht
  have hgu := CDUnique15.goodHead_append u [1] hu hnu
  have hgv := CDUnique15.goodHead_append v [2] hv hnv
  have hgvv := CDUnique15.goodHead_append (v++[2]) [1] hgv (by simp)
  have hc := M7TieWidth14.cd_eq_of_width_same_side _ _ ht
    (Or.inl ⟨ratio_one_gt_half u hu,ratio_one_gt_half (v++[2]) hgv⟩)
  have hsame := CDUnique15.injective _ _ hgu hgvv hc
  have heq : u=v++[2] := List.append_cancel_right hsame
  rw [heq] at he
  simpa [lowerEnds, ← List.reverse_prefix] using he
end Cross16
namespace Cross16

private theorem two_one_virtual_nontie (u v : List ℕ+)
    (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ [])
    (hw : lowerWidth (u++[2]) < lowerWidth v) :
    lowerWidth ((u++[2])++[1]) ≠ lowerWidth (v++[1]) := by
  intro ht
  have hgu := CDUnique15.goodHead_append u [2] hu hnu
  have hguu := CDUnique15.goodHead_append (u++[2]) [1] hgu (by simp)
  have hgv := CDUnique15.goodHead_append v [1] hv hnv
  have hc := M7TieWidth14.cd_eq_of_width_same_side _ _ ht
    (Or.inl ⟨ratio_one_gt_half (u++[2]) hgu,ratio_one_gt_half v hv⟩)
  have hsame := CDUnique15.injective _ _ hguu hgv hc
  have heq : u++[2]=v := List.append_cancel_right hsame
  exact hw.ne (congrArg lowerWidth heq)
end Cross16


open Freiman
namespace Mixed15

-- This is an internal interface. Its proof is required before submitting the
-- original comparison-transfer theorem.
private def LowTieLaw : Prop :=
  ∀ (u v : List ℕ+), CDUnique15.GoodHead u → CDUnique15.GoodHead v →
    u ≠ [] → v ≠ [] → lowerEnds u [1] → lowerEnds v [2] →
    u.length % 2 = v.length % 2 → lowerWidth u = lowerWidth v →
    (if u.length % 2 = 0 then
      lowerEndpoint (u,v) false ≤ lowerEndpoint (v,u) false
    else lowerEndpoint (v,u) true ≤ lowerEndpoint (u,v) true)

private theorem alignment (hlow : LowTieLaw)
    (u v : List ℕ+) (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ []) (hp : u.length % 2 ≠ v.length % 2) :
    (if v.length % 2 = 0 then
      lowerEndpoint (v++[2],u++[2]) false ≤ lowerEndpoint (u++[2],v++[2]) false
    else lowerEndpoint (u++[2],v++[2]) true ≤ lowerEndpoint (v++[2],u++[2]) true) := by
  classical
  let x := u ++ [2]
  let y := v ++ [2]
  have hxy : lowerWidth x ≠ lowerWidth y :=
    CDUnique15.width_ne_append_two u v hu hv hnu hnv hp
  have hxg : CDUnique15.GoodHead x := CDUnique15.goodHead_append _ _ hu hnu
  have hyg : CDUnique15.GoodHead y := CDUnique15.goodHead_append _ _ hv hnv
  have hy1g : CDUnique15.GoodHead (y++[1]) :=
    CDUnique15.goodHead_append _ _ hyg (by simp [y])
  rcases Nat.mod_two_eq_zero_or_one v.length with hve | hvo
  · rw [if_pos hve]
    change lowerEndpoint (y,x) false ≤ lowerEndpoint (x,y) false
    have hx : x.length % 2 = 0 := by simp only [x,List.length_append,List.length_singleton]; omega
    have hy : y.length % 2 = 1 := by simp only [y,List.length_append,List.length_singleton]; omega
    have hy1 : (y++[1]).length % 2 = 0 := by simp only [List.length_append,List.length_singleton]; omega
    have hpv : (y++[1]).length % 2 = x.length % 2 := hy1.trans hx.symm
    by_cases hwide : lowerWidth x ≤ lowerWidth y
    · have hnot : ¬ lowerWidth y ≤ lowerWidth x := fun h => hxy (le_antisymm hwide h)
      have he1 : lowerEndpoint (y,x) false = lowerEndpoint (y++[1],x) false := by
        simp [lowerEndpoint,lowerEndpointWords,hx,hy,hy1,hwide,hnot,List.length_append,Nat.add_mod]
      have he2 : lowerEndpoint (x,y) false = lowerEndpoint (x,y++[1]) false := by
        simp [lowerEndpoint,lowerEndpointWords,hx,hy,hy1,hwide,hnot,List.length_append,Nat.add_mod]
      rw [he1,he2]
      by_cases ht : lowerWidth (y++[1]) = lowerWidth x
      · have hh := hlow (y++[1]) x hy1g hxg (by simp) (by simp [x])
          ⟨y,rfl⟩ ⟨u,rfl⟩ hpv ht
        simpa only [hy1,if_true] using hh
      · have hn : LowerEarlyTerminalNoTies (y++[1],x) :=
          ⟨ht,fun h => (h hpv).elim⟩
        exact (lowerEarlyTerminal_endpoint_swap_nontie _ hn false).le
    · have hle : lowerWidth y ≤ lowerWidth x := (not_le.mp hwide).le
      apply le_of_eq
      simp [lowerEndpoint,lowerEndpointWords,lowerNaturalWords,hx,hy,hwide,hle]
      ring
  · rw [if_neg (by omega : ¬ v.length % 2 = 0)]
    change lowerEndpoint (x,y) true ≤ lowerEndpoint (y,x) true
    have hx : x.length % 2 = 1 := by simp only [x,List.length_append,List.length_singleton]; omega
    have hy : y.length % 2 = 0 := by simp only [y,List.length_append,List.length_singleton]; omega
    have hy1 : (y++[1]).length % 2 = 1 := by simp only [List.length_append,List.length_singleton]; omega
    have hpv : (y++[1]).length % 2 = x.length % 2 := hy1.trans hx.symm
    by_cases hwide : lowerWidth x ≤ lowerWidth y
    · have hnot : ¬ lowerWidth y ≤ lowerWidth x := fun h => hxy (le_antisymm hwide h)
      have he1 : lowerEndpoint (y,x) true = lowerEndpoint (y++[1],x) true := by
        simp [lowerEndpoint,lowerEndpointWords,hx,hy,hy1,hwide,hnot,List.length_append,Nat.add_mod]
      have he2 : lowerEndpoint (x,y) true = lowerEndpoint (x,y++[1]) true := by
        simp [lowerEndpoint,lowerEndpointWords,hx,hy,hy1,hwide,hnot,List.length_append,Nat.add_mod]
      rw [he1,he2]
      by_cases ht : lowerWidth (y++[1]) = lowerWidth x
      · have hh := hlow (y++[1]) x hy1g hxg (by simp) (by simp [x])
          ⟨y,rfl⟩ ⟨u,rfl⟩ hpv ht
        simpa only [hy1,show ¬ (1:ℕ)=0 by omega,if_false] using hh
      · have hn : LowerEarlyTerminalNoTies (y++[1],x) :=
          ⟨ht,fun h => (h hpv).elim⟩
        exact (lowerEarlyTerminal_endpoint_swap_nontie _ hn true).symm.le
    · have hle : lowerWidth y ≤ lowerWidth x := (not_le.mp hwide).le
      apply le_of_eq
      simp [lowerEndpoint,lowerEndpointWords,lowerNaturalWords,hx,hy,hwide,hle]
      ring

end Mixed15


open Freiman
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Cross16Bounds

private theorem cd_eq (w : List ℕ+) :
    lowerCD w = (wordContinuantPrevQ w, wordContinuantQ w) := by
  have h : ∀ (v : List ℕ) (m : (ℕ × ℕ) × (ℕ × ℕ)),
      (v.foldl (fun d a => ((d.1.2, (a : ℕ) * d.1.2 + d.1.1),
        (d.2.2, (a : ℕ) * d.2.2 + d.2.1))) m).2 =
      v.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) m.2 := by
    intro v
    induction v with
    | nil => intro m; rfl
    | cons a v ih =>
      intro m
      simp only [List.foldl_cons]
      rw [ih]
      simp only [Nat.add_comm]
  simpa [lowerCD, wordContinuantPrevQ, wordContinuantQ, wordContinuantData]
    using (h (w.flatMap fun a => [(a : ℕ)]) ((1,0),(0,1))).symm

private theorem q_pos (w : List ℕ+) : 0 < ((lowerCD w).2 : ℝ) := by
  rw [cd_eq]
  exact_mod_cast continuant_denominator_pos w

private theorem tails :
    lowerAlpha ∈ Set.Icc (0 : ℝ) 1 ∧
    lowerBeta ∈ Set.Icc (0 : ℝ) 1 ∧ lowerAlpha < lowerBeta := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  have hlo : 3 < Real.sqrt (21 : ℝ) := by nlinarith
  have hhi : Real.sqrt (21 : ℝ) < 5 := by nlinarith
  dsimp [lowerAlpha, lowerBeta, Set.mem_Icc]
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  · linarith

private theorem width_formula (w : List ℕ+) :
    lowerWidth w = (lowerBeta - lowerAlpha) /
      ((((lowerCD w).1 : ℝ) * lowerAlpha + (lowerCD w).2) *
       (((lowerCD w).1 : ℝ) * lowerBeta + (lowerCD w).2)) := by
  unfold lowerWidth
  rw [prefixEval_difference w lowerBeta lowerAlpha tails.2.1 tails.1]
  rw [abs_of_pos (sub_pos.mpr tails.2.2), cd_eq]
  ring


private theorem denom_pos (w : List ℕ+) :
    0 < ((((lowerCD w).1:ℝ)*lowerAlpha+(lowerCD w).2)*
       (((lowerCD w).1:ℝ)*lowerBeta+(lowerCD w).2)) := by
  have ha := tails.1.1
  have hb := tails.2.1.1
  have hq := q_pos w
  positivity

private theorem denom_bounds (c d : ℝ) (hc : 0 ≤ c) (hd : 0 < d) :
    2*((d*lowerAlpha+c+3*d)*(d*lowerBeta+c+3*d)) <
      25*((c*lowerAlpha+d)*(c*lowerBeta+d)) ∧
    18*((c*lowerAlpha+d)*(c*lowerBeta+d)) <
      (((c+d)*lowerAlpha+3*c+4*d)*((c+d)*lowerBeta+3*c+4*d)) := by
  have hz := Real.sq_sqrt (by norm_num : (0:ℝ)≤21)
  have hz0 := Real.sqrt_nonneg (21:ℝ)
  have hlo : 4 < Real.sqrt (21:ℝ) := by nlinarith
  have hhi : Real.sqrt (21:ℝ) < (14/3:ℝ) := by nlinarith
  have hs1 : 0 < (14-3*Real.sqrt 21)*d^2 :=
    mul_pos (by linarith) (sq_pos_of_pos hd)
  have hs2 : 0 ≤ ((121-25*Real.sqrt 21)/2)*c^2 :=
    mul_nonneg (by linarith) (sq_nonneg c)
  have hs3 : 0 ≤ ((46*Real.sqrt 21-174)/3)*c*d :=
    mul_nonneg (mul_nonneg (by linarith) hc) hd.le
  have ht1 : 0 < ((13*Real.sqrt 21-45)/6)*d^2 :=
    mul_pos (by linarith) (sq_pos_of_pos hd)
  have ht2 : 0 ≤ ((21*Real.sqrt 21-79)/2)*c^2 :=
    mul_nonneg (by linarith) (sq_nonneg c)
  have ht3 : 0 ≤ ((153-25*Real.sqrt 21)/3)*c*d :=
    mul_nonneg (mul_nonneg (by linarith) hc) hd.le
  have hid1 :
      25*((c*lowerAlpha+d)*(c*lowerBeta+d)) -
      2*((d*lowerAlpha+c+3*d)*(d*lowerBeta+c+3*d)) =
      ((121-25*Real.sqrt 21)/2)*c^2 +
      ((46*Real.sqrt 21-174)/3)*c*d +(14-3*Real.sqrt 21)*d^2 := by
    dsimp [lowerAlpha,lowerBeta]
    linear_combination ((25*c^2-2*d^2)/12)*hz
  have hid2 :
      (((c+d)*lowerAlpha+3*c+4*d)*((c+d)*lowerBeta+3*c+4*d)) -
      18*((c*lowerAlpha+d)*(c*lowerBeta+d)) =
      ((21*Real.sqrt 21-79)/2)*c^2 +
      ((153-25*Real.sqrt 21)/3)*c*d +((13*Real.sqrt 21-45)/6)*d^2 := by
    dsimp [lowerAlpha,lowerBeta]
    linear_combination ((-17*c^2+2*c*d+d^2)/12)*hz
  constructor <;> nlinarith [hid1,hid2]

private theorem width_bounds (w : List ℕ+) :
    2*lowerWidth w < 25*lowerWidth (w++[3]) ∧
    18*lowerWidth (w++[1,3]) < lowerWidth w := by
  have hw := denom_bounds ((lowerCD w).1:ℝ) (lowerCD w).2 (by positivity) (q_pos w)
  have hnum := sub_pos.mpr tails.2.2
  have hd := denom_pos w
  have hd3 := denom_pos (w++[3])
  have hd13 := denom_pos (w++[1,3])
  have he3 : lowerCD (w++[3]) = ((lowerCD w).2,(lowerCD w).1+3*(lowerCD w).2) := by simp [lowerCD,List.foldl_append]
  have he13 : lowerCD (w++[1,3]) = ((lowerCD w).1+(lowerCD w).2,3*(lowerCD w).1+4*(lowerCD w).2) := by
    simp [lowerCD,List.foldl_append]; omega
  constructor
  · rw [width_formula,width_formula,← mul_div_assoc,← mul_div_assoc]
    apply (div_lt_div_iff₀ hd hd3).2
    rw [he3]
    simp only [Prod.fst,Prod.snd,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    have hh := mul_pos hnum (sub_pos.mpr hw.1)
    nlinarith
  · rw [width_formula,width_formula,← mul_div_assoc]
    apply (div_lt_div_iff₀ hd13 hd).2
    rw [he13]
    simp only [Prod.fst,Prod.snd,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    have hh := mul_pos hnum (sub_pos.mpr hw.2)
    nlinarith

private theorem tied_three_threshold (u v : List ℕ+) (ht : lowerWidth u=lowerWidth v) :
    (7/5:ℝ)*lowerWidth (u++[1,3]) < lowerWidth (v++[3]) := by
  have hu := width_bounds u
  have hv := width_bounds v
  have hw : 0 ≤ lowerWidth u := abs_nonneg _
  nlinarith [hu.2,hv.1,ht]

private theorem append_one_lt (w : List ℕ+) : lowerWidth (w++[1]) < lowerWidth w := by
  have hnum := sub_pos.mpr tails.2.2
  have hd := denom_pos w
  have hde := denom_pos (w++[1])
  have hq := q_pos w
  have hc : (0:ℝ) ≤ (lowerCD w).1 := by positivity
  have hz := Real.sq_sqrt (by norm_num : (0:ℝ)≤21)
  have hz0 := Real.sqrt_nonneg (21:ℝ)
  have hzlo : 3 < Real.sqrt (21:ℝ) := by nlinarith
  have ha : 0 < lowerAlpha := by dsimp [lowerAlpha]; linarith
  have hb : 0 < lowerBeta := by dsimp [lowerBeta]; linarith
  have ha1 := tails.1.2
  have hb1 := tails.2.1.2
  rw [width_formula,width_formula]
  apply div_lt_div_of_pos_left hnum hd
  have he : lowerCD (w++[1]) = ((lowerCD w).2,(lowerCD w).1+(lowerCD w).2) := by
    simp [lowerCD,List.foldl_append]
  rw [he]
  simp only [Prod.fst,Prod.snd,Nat.cast_add]
  have hA : ((lowerCD w).1:ℝ)*lowerAlpha+(lowerCD w).2 <
      ((lowerCD w).2:ℝ)*lowerAlpha+((lowerCD w).1+(lowerCD w).2) := by
    nlinarith [mul_pos hq ha,mul_nonneg hc (sub_nonneg.mpr ha1)]
  have hB : ((lowerCD w).1:ℝ)*lowerBeta+(lowerCD w).2 <
      ((lowerCD w).2:ℝ)*lowerBeta+((lowerCD w).1+(lowerCD w).2) := by
    nlinarith [mul_pos hq hb,mul_nonneg hc (sub_nonneg.mpr hb1)]
  apply mul_lt_mul hA hB.le <;> positivity

end Cross16Bounds


namespace Cross16Bounds
private theorem append_digit_lt (w : List ℕ+) (k : ℕ+) : lowerWidth (w++[k]) < lowerWidth w := by
  have hnum := sub_pos.mpr tails.2.2
  have hd := denom_pos w
  have hde := denom_pos (w++[k])
  have hq := q_pos w
  have hk : (1:ℝ) ≤ (k:ℕ) := by exact_mod_cast k.property
  have hk0 : 0 ≤ ((k:ℕ):ℝ)-1 := by linarith
  have hc : (0:ℝ) ≤ (lowerCD w).1 := by positivity
  have hz := Real.sq_sqrt (by norm_num : (0:ℝ)≤21)
  have hz0 := Real.sqrt_nonneg (21:ℝ)
  have hzlo : 3 < Real.sqrt (21:ℝ) := by nlinarith
  have ha : 0 < lowerAlpha := by dsimp [lowerAlpha]; linarith
  have hb : 0 < lowerBeta := by dsimp [lowerBeta]; linarith
  have ha1 := tails.1.2
  have hb1 := tails.2.1.2
  rw [width_formula,width_formula]
  apply div_lt_div_of_pos_left hnum hd
  have he : lowerCD (w++[k]) = ((lowerCD w).2,(lowerCD w).1+(k:ℕ)*(lowerCD w).2) := by
    simp [lowerCD,List.foldl_append]
  rw [he]
  simp only [Prod.fst,Prod.snd,Nat.cast_add,Nat.cast_mul]
  have hA : ((lowerCD w).1:ℝ)*lowerAlpha+(lowerCD w).2 <
      ((lowerCD w).2:ℝ)*lowerAlpha+((lowerCD w).1+((k:ℕ):ℝ)*(lowerCD w).2) := by
    nlinarith [mul_pos hq ha,mul_nonneg hc (sub_nonneg.mpr ha1),mul_nonneg hk0 hq.le]
  have hB : ((lowerCD w).1:ℝ)*lowerBeta+(lowerCD w).2 <
      ((lowerCD w).2:ℝ)*lowerBeta+((lowerCD w).1+((k:ℕ):ℝ)*(lowerCD w).2) := by
    nlinarith [mul_pos hq hb,mul_nonneg hc (sub_nonneg.mpr hb1),mul_nonneg hk0 hq.le]
  apply mul_lt_mul hA hB.le <;> positivity

private theorem width_lt_of_cd (a b : List ℕ+)
    (hc : ((lowerCD a).1:ℝ) ≤ (lowerCD b).1)
    (hd : ((lowerCD a).2:ℝ) < (lowerCD b).2) :
    lowerWidth b < lowerWidth a := by
  rw [width_formula,width_formula]
  apply div_lt_div_of_pos_left (sub_pos.mpr tails.2.2) (denom_pos a)
  have h1 := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_right hc tails.1.1) hd
  have h2 := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_right hc tails.2.1.1) hd
  apply mul_lt_mul h1 h2.le
  · have ha := tails.1.1
    have hb := tails.2.1.1
    have hq := q_pos a
    positivity
  · have ha := tails.1.1
    have hb := tails.2.1.1
    have hq := q_pos b
    positivity

end Cross16Bounds


open Freiman
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace M7LowTies15

private theorem cd_eq (w : List ℕ+) :
    lowerCD w = (wordContinuantPrevQ w, wordContinuantQ w) := by
  have h : ∀ (v : List ℕ) (m : (ℕ × ℕ) × (ℕ × ℕ)),
      (v.foldl (fun d a => ((d.1.2, (a : ℕ) * d.1.2 + d.1.1),
        (d.2.2, (a : ℕ) * d.2.2 + d.2.1))) m).2 =
      v.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) m.2 := by
    intro v
    induction v with
    | nil => intro m; rfl
    | cons a v ih =>
      intro m
      simp only [List.foldl_cons]
      rw [ih]
      simp only [Nat.add_comm]
  simpa [lowerCD, wordContinuantPrevQ, wordContinuantQ, wordContinuantData]
    using (h (w.flatMap fun a => [(a : ℕ)]) ((1,0),(0,1))).symm

private theorem q_pos (w : List ℕ+) : 0 < ((lowerCD w).2 : ℝ) := by
  rw [cd_eq]
  exact_mod_cast continuant_denominator_pos w

private theorem tails :
    lowerAlpha ∈ Set.Icc (0 : ℝ) 1 ∧
    lowerBeta ∈ Set.Icc (0 : ℝ) 1 ∧ lowerAlpha < lowerBeta := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  have hlo : 3 < Real.sqrt (21 : ℝ) := by nlinarith
  have hhi : Real.sqrt (21 : ℝ) < 5 := by nlinarith
  dsimp [lowerAlpha, lowerBeta, Set.mem_Icc]
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  · linarith

private theorem width_formula (w : List ℕ+) :
    lowerWidth w = (lowerBeta - lowerAlpha) /
      ((((lowerCD w).1 : ℝ) * lowerAlpha + (lowerCD w).2) *
       (((lowerCD w).1 : ℝ) * lowerBeta + (lowerCD w).2)) := by
  unfold lowerWidth
  rw [prefixEval_difference w lowerBeta lowerAlpha tails.2.1 tails.1]
  rw [abs_of_pos (sub_pos.mpr tails.2.2), cd_eq]
  ring

private theorem width_pos (w : List ℕ+) : 0 < lowerWidth w := by
  rw [width_formula]
  have ha := tails.1.1
  have hb := tails.2.1.1
  have hq := q_pos w
  exact div_pos (sub_pos.mpr tails.2.2) (mul_pos (by positivity) (by positivity))

private theorem width_eq_of_cd (u v : List ℕ+) (h : lowerCD u = lowerCD v) :
    lowerWidth u = lowerWidth v := by rw [width_formula, width_formula, h]

private theorem pe_append : ∀ (u v : List ℕ+) (x : ℝ),
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x)
  | [], _, _ => rfl
  | _ :: u, v, x => by simp only [List.cons_append, prefixEval, pe_append u v x]

private theorem radical3 :
    let s := Real.sqrt (3 : ℝ)
    s^2 = 3 ∧ 0 < s ∧ s < 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  dsimp
  refine ⟨hs, by nlinarith, by nlinarith⟩

private theorem endpoint_tails :
    let E := prefixEval [3] lowerTau
    let F := prefixEval [2,1,3] lowerTau
    E = 2 - Real.sqrt 3 ∧ F = (15 - Real.sqrt 3) / 37 ∧
      E < F ∧ E ∈ Set.Icc (0 : ℝ) 1 ∧ F ∈ Set.Icc (0 : ℝ) 1 := by
  have hs := radical3.1
  have hp := radical3.2.1
  have hh := radical3.2.2
  have hE : prefixEval [3] lowerTau = 2 - Real.sqrt 3 := by
    dsimp [lowerTau, prefixEval]
    norm_num only [PNat.val_ofNat, Nat.cast_ofNat]
    field_simp [show (3:ℝ) + (Real.sqrt 3 - 1) ≠ 0 by nlinarith]
    nlinarith
  have hF : prefixEval [2,1,3] lowerTau = (15 - Real.sqrt 3) / 37 := by
    dsimp [lowerTau, prefixEval]
    norm_num only [PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat]
    have h3 : (1:ℝ) / (3 + (Real.sqrt 3 - 1)) = 2 - Real.sqrt 3 := by
      field_simp [show (3:ℝ) + (Real.sqrt 3 - 1) ≠ 0 by nlinarith]
      nlinarith
    rw [h3]
    have h1 : (1:ℝ) / (1 + (2 - Real.sqrt 3)) = (3 + Real.sqrt 3) / 6 := by
      field_simp [show (1:ℝ) + (2 - Real.sqrt 3) ≠ 0 by nlinarith]
      nlinarith
    rw [h1]
    field_simp [show (2:ℝ) + (3 + Real.sqrt 3) / 6 ≠ 0 by nlinarith]
    nlinarith
  rw [hE,hF]
  refine ⟨rfl,rfl,by nlinarith,⟨by nlinarith,by nlinarith⟩,⟨by nlinarith,by nlinarith⟩⟩

private theorem cd_append_one (w : List ℕ+) :
    lowerCD (w ++ [1]) = ((lowerCD w).2, (lowerCD w).1 + (lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]

private theorem cd_append_two (w : List ℕ+) :
    lowerCD (w ++ [2]) = ((lowerCD w).2, (lowerCD w).1 + 2*(lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]

private theorem cd_append_low (w : List ℕ+) :
    lowerCD (w ++ [3]) = ((lowerCD w).2,
      (lowerCD w).1 + 3*(lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]

private theorem endpoint_den_pos (w : List ℕ+) (z : ℝ) (hz : 0 ≤ z) :
    0 < ((lowerCD w).2 : ℝ) + z * (lowerCD w).1 := by
  have hq := q_pos w
  positivity

private theorem pe_signed_difference (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    prefixEval w x - prefixEval w y =
      (x-y) * ((-1 : ℝ)^w.length) /
        ((((lowerCD w).2 : ℝ) + x*(lowerCD w).1) *
         (((lowerCD w).2 : ℝ) + y*(lowerCD w).1)) := by
  rw [prefixEval_mobius w x hx, prefixEval_mobius w y hy]
  have hc := cd_eq w
  have hd : (wordContinuantPrevP w : ℝ) * wordContinuantQ w -
      (wordContinuantP w : ℝ) * wordContinuantPrevQ w = (-1 : ℝ)^w.length := by
    exact_mod_cast continuant_determinant w
  have hqx : (wordContinuantQ w : ℝ) + x * wordContinuantPrevQ w ≠ 0 := by
    have hq : (0:ℝ) < wordContinuantQ w := by exact_mod_cast continuant_denominator_pos w
    positivity
  have hqy : (wordContinuantQ w : ℝ) + y * wordContinuantPrevQ w ≠ 0 := by
    have hq : (0:ℝ) < wordContinuantQ w := by exact_mod_cast continuant_denominator_pos w
    positivity
  rw [hc]
  dsimp only [Prod.fst, Prod.snd]
  rw [div_sub_div _ _ hqx hqy]
  congr 1
  linear_combination (x-y) * hd

private theorem pe_delta_abs (w : List ℕ+) :
    let E := prefixEval [3] lowerTau
    let F := prefixEval [2,1,3] lowerTau
    |prefixEval w E - prefixEval w F| =
      (F-E) / ((((lowerCD w).2:ℝ)+E*(lowerCD w).1) *
        (((lowerCD w).2:ℝ)+F*(lowerCD w).1)) := by
  dsimp only
  rw [prefixEval_difference w _ _ endpoint_tails.2.2.2.1 endpoint_tails.2.2.2.2]
  rw [abs_of_neg (sub_neg.mpr endpoint_tails.2.2.1), cd_eq]
  ring

end M7LowTies15

namespace M7LowTies15

private theorem algebra_classify {c d C D : ℝ}
    (hd : 0 < d) (hD : 0 < D) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hA : 4*c*d-3*c^2 = 4*C*D-3*C^2)
    (hB : 2*d^2-4*c*d+5*c^2 = 2*D^2-4*C*D+5*C^2) :
    (c = C ∧ d = D) ∨ (5*C = -3*c+4*d ∧ 5*D = 4*c+3*d) := by
  have hres : (c*D-C*d) * (4*c*C+3*c*D+3*C*d-4*d*D) = 0 := by
    have hz : (4*c*d-3*c^2)*(2*D^2-4*C*D+5*C^2) -
        (4*C*D-3*C^2)*(2*d^2-4*c*d+5*c^2) = 0 := by rw [hA,hB]; ring
    nlinarith [hz]
  rcases mul_eq_zero.mp hres with hcross | hfac
  · left
    have hid : (2*d^2-4*c*d+5*c^2)*D^2 -
        (2*D^2-4*C*D+5*C^2)*d^2 =
        (c*D-C*d)*(-4*d*D+5*c*D+5*C*d) := by ring
    rw [hcross] at hid
    have hsame : (2*D^2-4*C*D+5*C^2)*d^2 =
        (2*D^2-4*C*D+5*C^2)*D^2 := by nlinarith [hid]
    have hBp : 0 < 2*D^2-4*C*D+5*C^2 := by
      nlinarith [sq_pos_of_pos hD, sq_nonneg (D-2*C), sq_nonneg C]
    have hde : d = D := by nlinarith [hsame]
    have hce : c = C := by
      rw [hde] at hcross
      nlinarith
    exact ⟨hce,hde⟩
  · right
    have hcubic : D*(25*D^2-16*c^2-24*c*d-9*d^2) = 0 := by
      linear_combination (10*C-31/2*D)*hA + (6*C-25/2*D)*hB - 4*d*hfac
    have hsquare : (5*D)^2 = (4*c+3*d)^2 := by
      have hn : D ≠ 0 := ne_of_gt hD
      apply (mul_left_cancel₀ hn)
      nlinarith [hcubic]
    have hDe : 5*D = 4*c+3*d := by
      have hp : 0 < 4*c+3*d := by positivity
      nlinarith
    have hCe : 5*C = -3*c+4*d := by
      have hprod : D*(5*C+3*c-4*d) = 0 := by
        calc
          D*(5*C+3*c-4*d) = C*(5*D)+D*(3*c-4*d) := by ring
          _ = C*(4*c+3*d)+D*(3*c-4*d) := by rw [hDe]
          _ = 0 := by nlinarith [hfac]
      have := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hD)
      linarith
    exact ⟨hCe,hDe⟩

private theorem cd_classify (u v : List ℕ+) (hw : lowerWidth u = lowerWidth v) :
    lowerCD u = lowerCD v ∨
      (5*((lowerCD v).1:ℝ) = -3*((lowerCD u).1:ℝ)+4*(lowerCD u).2 ∧
       5*((lowerCD v).2:ℝ) = 4*((lowerCD u).1:ℝ)+3*(lowerCD u).2) := by
  have hh := M7TieWidth14.coefficients_of_width u v hw
  have hA : 4*((lowerCD u).1:ℝ)*(lowerCD u).2-3*((lowerCD u).1:ℝ)^2 =
      4*((lowerCD v).1:ℝ)*(lowerCD v).2-3*((lowerCD v).1:ℝ)^2 := by
    have h := hh.1
    dsimp [M7TieWidth14.coeffA] at h
    exact_mod_cast h
  have hB : 2*((lowerCD u).2:ℝ)^2-4*((lowerCD u).1:ℝ)*(lowerCD u).2+5*((lowerCD u).1:ℝ)^2 =
      2*((lowerCD v).2:ℝ)^2-4*((lowerCD v).1:ℝ)*(lowerCD v).2+5*((lowerCD v).1:ℝ)^2 := by
    have h := hh.2
    dsimp [M7TieWidth14.coeffB] at h
    exact_mod_cast h
  rcases algebra_classify (q_pos u) (q_pos v) (by positivity) (by positivity) hA hB with h | h
  · left
    apply Prod.ext
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  · exact Or.inr h

end M7LowTies15

namespace M7LowTies15

private theorem cd_fst_le_snd (w : List ℕ+) : (lowerCD w).1 ≤ (lowerCD w).2 := by
  have hr := (lowerEarlyTerminal_ratio_range w).2
  rw [lowerRatio, div_le_one (q_pos w)] at hr
  exact_mod_cast hr

private theorem width_seven_fifths (u v : List ℕ+)
    (hden : 5*((((lowerCD v).1:ℝ)*lowerAlpha+(lowerCD v).2)*
        (((lowerCD v).1:ℝ)*lowerBeta+(lowerCD v).2)) ≤
      7*((((lowerCD u).1:ℝ)*lowerAlpha+(lowerCD u).2)*
        (((lowerCD u).1:ℝ)*lowerBeta+(lowerCD u).2))) :
    lowerWidth u ≤ (7/5:ℝ)*lowerWidth v := by
  rw [width_formula,width_formula]
  have hn := sub_pos.mpr tails.2.2
  have hu : 0 < ((((lowerCD u).1:ℝ)*lowerAlpha+(lowerCD u).2)*
      (((lowerCD u).1:ℝ)*lowerBeta+(lowerCD u).2)) := by
    have ha := tails.1.1
    have hb := tails.2.1.1
    have hq := q_pos u
    positivity
  have hv : 0 < ((((lowerCD v).1:ℝ)*lowerAlpha+(lowerCD v).2)*
      (((lowerCD v).1:ℝ)*lowerBeta+(lowerCD v).2)) := by
    have ha := tails.1.1
    have hb := tails.2.1.1
    have hq := q_pos v
    positivity
  rw [show (7/5:ℝ) * ((lowerBeta-lowerAlpha) /
      ((((lowerCD v).1:ℝ)*lowerAlpha+(lowerCD v).2)*
       (((lowerCD v).1:ℝ)*lowerBeta+(lowerCD v).2))) =
      ((7/5:ℝ)*(lowerBeta-lowerAlpha)) /
      ((((lowerCD v).1:ℝ)*lowerAlpha+(lowerCD v).2)*
       (((lowerCD v).1:ℝ)*lowerBeta+(lowerCD v).2)) by ring]
  rw [div_le_div_iff₀ hu hv]
  nlinarith [mul_pos hn hv]

private theorem reflection_bounds_low {c d C D : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d) (hdc : d ≤ 2*c)
    (hC : 5*C = -3*c+4*d) (hD : 5*D = 4*c+3*d) :
    let E := prefixEval [3] lowerTau
    let F := prefixEval [2,1,3] lowerTau
    let a := lowerAlpha
    let b := lowerBeta
    let ce := d
    let de := c+3*d
    let Ce := D
    let De := C+3*D
    (d+E*c)*(d+F*c) ≤ (D+E*C)*(D+F*C) ∧
      5*((De+a*Ce)*(De+b*Ce)) ≤ 7*((de+a*ce)*(de+b*ce)) ∧
      5*((de+a*ce)*(de+b*ce)) ≤ 7*((De+a*Ce)*(De+b*Ce)) := by
  dsimp only
  have hC' : C = (-3*c+4*d)/5 := by linarith
  have hD' : D = (4*c+3*d)/5 := by linarith
  have hs3 := radical3.1
  have hs30 := radical3.2.1
  have hs21 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 21)
  have hs210 := Real.sqrt_nonneg (21:ℝ)
  have hs21lo : 4 < Real.sqrt (21:ℝ) := by nlinarith
  have hs21hi : Real.sqrt (21:ℝ) < 5 := by nlinarith
  have hprod : 0 ≤ (c+2*d)*(2*c-d) :=
    mul_nonneg (by linarith) (by linarith)
  rw [endpoint_tails.1, endpoint_tails.2.1, hC', hD']
  dsimp [lowerAlpha, lowerBeta]
  constructor
  · have hid :
      (((4*c+3*d)/5+(2-Real.sqrt 3)*((-3*c+4*d)/5))*
       ((4*c+3*d)/5+(15-Real.sqrt 3)/37*((-3*c+4*d)/5))) -
      ((d+(2-Real.sqrt 3)*c)*(d+(15-Real.sqrt 3)/37*c)) =
      (2*(182*Real.sqrt 3-251)/925)*(c+2*d)*(2*c-d) := by
      field_simp
      nlinarith [hs3]
    have hk : 0 ≤ 2*(182*Real.sqrt 3-251)/925 := by nlinarith
    nlinarith [mul_nonneg hk hprod]
  constructor
  · have hq1 : 0 ≤ c*d-c^2 := by
      nlinarith [mul_nonneg hc (sub_nonneg.mpr hcd)]
    have hq2 : 0 ≤ d^2-c*d := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ d) (sub_nonneg.mpr hcd)]
    have h1 : 0 ≤ (93*Real.sqrt 21+237)*(d^2-c*d) := by positivity
    have h2 : 0 ≤ (41*Real.sqrt 21+249)*(c*d-c^2) := by positivity
    have h3 : 0 ≤ (207-7*Real.sqrt 21)*c^2 :=
      mul_nonneg (by nlinarith) (sq_nonneg c)
    field_simp
    nlinarith
  · have hd0 : 0 ≤ d := by linarith
    have hgap : 0 ≤ (2*c-d)*d := mul_nonneg (by linarith) hd0
    have hk : 0 ≤ 111*Real.sqrt 21-321 := by nlinarith
    have h1 : 0 ≤ (111*Real.sqrt 21-321)*((2*c-d)*d) :=
      mul_nonneg hk hgap
    have h2 : 0 ≤ (382*Real.sqrt 21+1998)*(c*d) := by positivity
    have h3 : 0 ≤ (336*Real.sqrt 21+654)*c^2 := by positivity
    field_simp
    nlinarith

private theorem low_metric_data (u v : List ℕ+) (hu1 : lowerEnds u [1])
    (hw : lowerWidth u = lowerWidth v) :
    let E := prefixEval [3] lowerTau
    let F := prefixEval [2,1,3] lowerTau
    lowerWidth (u++[3]) ≤ (7/5:ℝ)*lowerWidth (v++[3]) ∧
    lowerWidth (v++[3]) ≤ (7/5:ℝ)*lowerWidth (u++[3]) ∧
    (((lowerCD u).2:ℝ)+E*(lowerCD u).1)*(((lowerCD u).2:ℝ)+F*(lowerCD u).1) ≤
      (((lowerCD v).2:ℝ)+E*(lowerCD v).1)*(((lowerCD v).2:ℝ)+F*(lowerCD v).1) := by
  dsimp only
  have huc : (0:ℝ) ≤ (lowerCD u).1 := by positivity
  have hucd : ((lowerCD u).1:ℝ) ≤ (lowerCD u).2 := by
    exact_mod_cast cd_fst_le_snd u
  obtain ⟨P,rfl⟩ := hu1
  have hudc : ((lowerCD (P++[1])).2:ℝ) ≤ 2*(lowerCD (P++[1])).1 := by
    rw [cd_append_one]
    push_cast
    have hp : (lowerCD P).1 ≤ (lowerCD P).2 := cd_fst_le_snd P
    have hpR : ((lowerCD P).1:ℝ) ≤ (lowerCD P).2 := by exact_mod_cast hp
    nlinarith
  rcases cd_classify (P++[1]) v hw with heq | href
  · have hae : lowerCD ((P++[1])++[3]) = lowerCD (v++[3]) := by
      rw [cd_append_low,cd_append_low,heq]
    refine ⟨?_, ?_, ?_⟩
    · have hwe := width_eq_of_cd _ _ hae
      nlinarith [width_pos (v++[3])]
    · have hwe := width_eq_of_cd _ _ hae
      nlinarith [width_pos ((P++[1])++[3])]
    · rw [heq]
  · have hb := reflection_bounds_low huc hucd hudc href.1 href.2
    refine ⟨?_, ?_, hb.1⟩
    · apply width_seven_fifths
      simpa only [cd_append_low, Prod.fst, Prod.snd, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using hb.2.1
    · apply width_seven_fifths
      simpa only [cd_append_low, Prod.fst, Prod.snd, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using hb.2.2

private theorem cd_append_three_one (w : List ℕ+) :
    lowerCD (w ++ [3,1]) =
      ((lowerCD w).1 + 3*(lowerCD w).2,
       (lowerCD w).1 + 4*(lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]
  ring

private theorem low_not_short (u v : List ℕ+)
    (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hu1 : lowerEnds u [1]) (hv2 : lowerEnds v [2])
    (hw : lowerWidth u = lowerWidth v) : ¬ lowerEnds u [3,1] := by
  rcases cd_classify u v hw with heq | href
  · have huv := CDUnique15.injective u v hu hv heq
    subst v
    have h1 := hu1.getLast (by simp)
    have h2 := hv2.getLast (by simp)
    have hx : (1 : ℕ+) = 2 := h1.trans h2.symm
    norm_num at hx
  · intro hu31
    obtain ⟨P,rfl⟩ := hu31
    obtain ⟨Q,rfl⟩ := hv2
    have hdu : 3*((lowerCD (P++[3,1])).2:ℝ) ≤
        4*(lowerCD (P++[3,1])).1 := by
      rw [cd_append_three_one]
      push_cast
      have hz : (0:ℝ) ≤ (lowerCD P).1 := by positivity
      nlinarith
    have hDv : ((lowerCD (Q++[2])).2:ℝ) ≤
        3*(lowerCD (Q++[2])).1 := by
      rw [cd_append_two]
      push_cast
      have hq := cd_fst_le_snd Q
      have hq' : ((lowerCD Q).1:ℝ) ≤ (lowerCD Q).2 := by exact_mod_cast hq
      nlinarith
    have hcpos : (0:ℝ) < (lowerCD (P++[3,1])).1 := by
      exact_mod_cast CDUnique15.fst_pos (P++[3,1]) (by simp)
    nlinarith [href.1, href.2]

private theorem low_words_lower (P Q : List ℕ+)
    (hp : (P++[1]).length % 2 = 0) (hq : (Q++[2]).length % 2 = 0)
    (hshort : ¬ lowerEnds (P++[1]) [3,1])
    (hw : lowerWidth (P++[1]) = lowerWidth (Q++[2])) :
    lowerEndpointWords (P++[1],Q++[2]) false =
      (P++[1]++[3], Q++[2]++[2,1,3]) ∧
    lowerEndpointWords (Q++[2],P++[1]) false =
      (Q++[2]++[3], P++[1]++[2,1,3]) := by
  have hm := low_metric_data (P++[1]) (Q++[2]) ⟨P,rfl⟩ hw
  dsimp only at hm
  have hp' : (P.length+1)%2 = 0 := by simpa using hp
  have hq' : (Q.length+1)%2 = 0 := by simpa using hq
  have hshort' : ¬ [3] <+: P.reverse := by
    simpa [lowerEnds, ← List.reverse_prefix] using hshort
  have hm1 : lowerWidth (P++[1,3]) ≤ (7/5:ℝ)*lowerWidth (Q++[2,3]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hm.1
  have hm2 : lowerWidth (Q++[2,3]) ≤ (7/5:ℝ)*lowerWidth (P++[1,3]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hm.2.1
  constructor
  · unfold lowerEndpointWords
    have hpar : (P++[1]).length % 2 = (Q++[2]).length % 2 := hp.trans hq.symm
    rw [if_pos hpar]
    unfold lowerEqualWords
    rw [show lowerNormalize (P++[1],Q++[2]) = (P++[1],Q++[2]) by
      simp [lowerNormalize, hw.ge]]
    simp [lowerNaturalShort, lowerEndpointSuffix, lowerEnds, ← List.reverse_prefix,
      hp', hq', hshort', hw.ge, hm1, List.append_assoc]
  · unfold lowerEndpointWords
    have hpar : (Q++[2]).length % 2 = (P++[1]).length % 2 := hq.trans hp.symm
    rw [if_pos hpar]
    unfold lowerEqualWords
    rw [show lowerNormalize (Q++[2],P++[1]) = (Q++[2],P++[1]) by
      simp [lowerNormalize, hw.le]]
    simp [lowerNaturalShort, lowerEndpointSuffix, lowerEnds, ← List.reverse_prefix,
      hp', hq', hshort', hw.le, hm2, List.append_assoc]

private theorem low_words_upper (P Q : List ℕ+)
    (hp : (P++[1]).length % 2 = 1) (hq : (Q++[2]).length % 2 = 1)
    (hshort : ¬ lowerEnds (P++[1]) [3,1])
    (hw : lowerWidth (P++[1]) = lowerWidth (Q++[2])) :
    lowerEndpointWords (P++[1],Q++[2]) true =
      (P++[1]++[3], Q++[2]++[2,1,3]) ∧
    lowerEndpointWords (Q++[2],P++[1]) true =
      (Q++[2]++[3], P++[1]++[2,1,3]) := by
  have hm := low_metric_data (P++[1]) (Q++[2]) ⟨P,rfl⟩ hw
  dsimp only at hm
  have hp' : (P.length+1)%2 = 1 := by simpa using hp
  have hq' : (Q.length+1)%2 = 1 := by simpa using hq
  have hshort' : ¬ [3] <+: P.reverse := by
    simpa [lowerEnds, ← List.reverse_prefix] using hshort
  have hm1 : lowerWidth (P++[1,3]) ≤ (7/5:ℝ)*lowerWidth (Q++[2,3]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hm.1
  have hm2 : lowerWidth (Q++[2,3]) ≤ (7/5:ℝ)*lowerWidth (P++[1,3]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hm.2.1
  constructor
  · unfold lowerEndpointWords
    have hpar : (P++[1]).length % 2 = (Q++[2]).length % 2 := hp.trans hq.symm
    rw [if_pos hpar]
    unfold lowerEqualWords
    rw [show lowerNormalize (P++[1],Q++[2]) = (P++[1],Q++[2]) by
      simp [lowerNormalize, hw.ge]]
    simp [lowerNaturalShort, lowerEndpointSuffix, lowerEnds, ← List.reverse_prefix,
      hp', hq', hshort', hw.ge, hm1, List.append_assoc]
  · unfold lowerEndpointWords
    have hpar : (Q++[2]).length % 2 = (P++[1]).length % 2 := hq.trans hp.symm
    rw [if_pos hpar]
    unfold lowerEqualWords
    rw [show lowerNormalize (Q++[2],P++[1]) = (Q++[2],P++[1]) by
      simp [lowerNormalize, hw.le]]
    simp [lowerNaturalShort, lowerEndpointSuffix, lowerEnds, ← List.reverse_prefix,
      hp', hq', hshort', hw.le, hm2, List.append_assoc]

private theorem low_delta_abs (u v : List ℕ+) (hu1 : lowerEnds u [1])
    (hw : lowerWidth u = lowerWidth v) :
    let E := prefixEval [3] lowerTau
    let F := prefixEval [2,1,3] lowerTau
    |prefixEval v E - prefixEval v F| ≤
      |prefixEval u E - prefixEval u F| := by
  dsimp only
  have hm := (low_metric_data u v hu1 hw).2.2
  rw [pe_delta_abs, pe_delta_abs]
  apply div_le_div_of_nonneg_left (sub_nonneg.mpr endpoint_tails.2.2.1.le)
  · exact mul_pos (endpoint_den_pos _ _ endpoint_tails.2.2.2.1.1)
      (endpoint_den_pos _ _ endpoint_tails.2.2.2.2.1)
  · exact hm

private theorem delta_nonpos_of_even (w : List ℕ+) (hp : w.length % 2 = 0) :
    prefixEval w (prefixEval [3] lowerTau) -
      prefixEval w (prefixEval [2,1,3] lowerTau) ≤ 0 := by
  rw [pe_signed_difference w _ _ endpoint_tails.2.2.2.1.1
    endpoint_tails.2.2.2.2.1, neg_one_pow_eq_pow_mod_two, hp]
  norm_num only [pow_zero, mul_one]
  have hd := mul_pos (endpoint_den_pos w _ endpoint_tails.2.2.2.1.1)
    (endpoint_den_pos w _ endpoint_tails.2.2.2.2.1)
  exact (div_neg_of_neg_of_pos (sub_neg.mpr endpoint_tails.2.2.1) hd).le

private theorem delta_nonneg_of_odd (w : List ℕ+) (hp : w.length % 2 = 1) :
    0 ≤ prefixEval w (prefixEval [3] lowerTau) -
      prefixEval w (prefixEval [2,1,3] lowerTau) := by
  rw [pe_signed_difference w _ _ endpoint_tails.2.2.2.1.1
    endpoint_tails.2.2.2.2.1, neg_one_pow_eq_pow_mod_two, hp]
  norm_num only [pow_one]
  have hn := sub_neg.mpr endpoint_tails.2.2.1
  have hd := mul_pos (endpoint_den_pos w _ endpoint_tails.2.2.2.1.1)
    (endpoint_den_pos w _ endpoint_tails.2.2.2.2.1)
  exact (div_nonneg (by linarith) hd.le)

private theorem lowTieLaw : Mixed15.LowTieLaw := by
  intro u v hu hv hnu hnv hu1 hv2 hpar hw
  have hshort := low_not_short u v hu hv hu1 hv2 hw
  have habs := low_delta_abs u v hu1 hw
  obtain ⟨P,rfl⟩ := hu1
  obtain ⟨Q,rfl⟩ := hv2
  dsimp only at habs
  rcases Nat.mod_two_eq_zero_or_one (P++[1]).length with hue | huo
  · have hve : (Q++[2]).length % 2 = 0 := hpar.symm ▸ hue
    rw [if_pos hue]
    have hwords := low_words_lower P Q hue hve hshort hw
    have hdu := delta_nonpos_of_even (P++[1]) hue
    have hdv := delta_nonpos_of_even (Q++[2]) hve
    rw [abs_of_nonpos hdv, abs_of_nonpos hdu] at habs
    unfold lowerEndpoint
    rw [hwords.1,hwords.2]
    simp only [Prod.fst,Prod.snd]
    rw [pe_append (P++[1]) [3] lowerTau,
      pe_append (Q++[2]) [2,1,3] lowerTau,
      pe_append (Q++[2]) [3] lowerTau,
      pe_append (P++[1]) [2,1,3] lowerTau]
    linarith
  · have hvo : (Q++[2]).length % 2 = 1 := hpar.symm ▸ huo
    simp only [if_neg (by omega : (P++[1]).length % 2 ≠ 0)]
    have hwords := low_words_upper P Q huo hvo hshort hw
    have hdu := delta_nonneg_of_odd (P++[1]) huo
    have hdv := delta_nonneg_of_odd (Q++[2]) hvo
    rw [abs_of_nonneg hdv, abs_of_nonneg hdu] at habs
    unfold lowerEndpoint
    rw [hwords.1,hwords.2]
    simp only [Prod.fst,Prod.snd]
    rw [pe_append (P++[1]) [3] lowerTau,
      pe_append (Q++[2]) [2,1,3] lowerTau,
      pe_append (Q++[2]) [3] lowerTau,
      pe_append (P++[1]) [2,1,3] lowerTau]
    linarith

end M7LowTies15


open Freiman
namespace Cross16TwoOne
set_option maxHeartbeats 0

private theorem containment_of_ne (u v : List ℕ+)
    (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ []) (hp : u.length%2 ≠ v.length%2)
    (hwu : lowerWidth (u++[2]) < lowerWidth v)
    (hne : lowerWidth (u++[2]) ≠ lowerWidth (v++[1])) :
    lowerEndpoint (v++[1],u++[2]) false ≤ lowerEndpoint (u++[2],v++[1]) false ∧
    lowerEndpoint (u++[2],v++[1]) true ≤ lowerEndpoint (v++[1],u++[2]) true := by
  have hxn := Cross16.two_one_virtual_nontie u v hu hv hnu hnv hwu
  by_cases hyn : lowerWidth ((v++[1])++[1]) = lowerWidth (u++[2])
  · have hwide : lowerWidth (u++[2]) ≤ lowerWidth (v++[1]) := by
      rw [← hyn]
      exact (Cross16Bounds.append_one_lt (v++[1])).le
    have hnot : ¬ lowerWidth (v++[1]) ≤ lowerWidth (u++[2]) := by
      rw [← hyn]
      exact not_le_of_gt (Cross16Bounds.append_one_lt (v++[1]))
    have hgu := CDUnique15.goodHead_append u [2] hu hnu
    have hgv := CDUnique15.goodHead_append v [1] hv hnv
    have hgvv := CDUnique15.goodHead_append (v++[1]) [1] hgv (by simp)
    have hpar : ((v++[1])++[1]).length%2 = (u++[2]).length%2 := by
      simp only [List.length_append,List.length_singleton]; omega
    have hh := M7LowTies15.lowTieLaw ((v++[1])++[1]) (u++[2]) hgvv hgu
      (by simp) (by simp) ⟨v++[1],rfl⟩ ⟨u,rfl⟩ hpar hyn
    rcases Nat.mod_two_eq_zero_or_one v.length with hv0 | hv1
    · have hu1 : u.length%2=1 := by omega
      have hxp : (u++[2]).length%2=0 := by simp [hu1,Nat.add_mod]
      have hyp : (v++[1]).length%2=1 := by simp [hv0,Nat.add_mod]
      have hyyp : ((v++[1])++[1]).length%2=0 := by simp [hv0,Nat.add_mod]
      simp only [hyyp,if_true] at hh
      have he1 : lowerEndpoint (v++[1],u++[2]) false =
          lowerEndpoint ((v++[1])++[1],u++[2]) false := by
        simp [lowerEndpoint,lowerEndpointWords,hxp,hyp,hyyp,hwide,hnot,List.length_append,Nat.add_mod,hv0,hu1]
      have he2 : lowerEndpoint (u++[2],v++[1]) false =
          lowerEndpoint (u++[2],(v++[1])++[1]) false := by
        simp [lowerEndpoint,lowerEndpointWords,hxp,hyp,hyyp,hwide,hnot,List.length_append,Nat.add_mod,hv0,hu1]
      constructor
      · simpa only [he1,he2] using hh
      · apply le_of_eq
        unfold lowerEndpoint lowerEndpointWords
        simp only [Prod.fst,Prod.snd,hxp,hyp,hwide,hnot]
        norm_num [Nat.add_mod,hv0]
        unfold lowerNaturalWords
        ring
    · have hu0 : u.length%2=0 := by omega
      have hxp : (u++[2]).length%2=1 := by simp [hu0,Nat.add_mod]
      have hyp : (v++[1]).length%2=0 := by simp [hv1,Nat.add_mod]
      have hyyp : ((v++[1])++[1]).length%2=1 := by simp [hv1,Nat.add_mod]
      simp only [hyyp,show ¬(1:ℕ)=0 by omega,if_false] at hh
      have he1 : lowerEndpoint (v++[1],u++[2]) true =
          lowerEndpoint ((v++[1])++[1],u++[2]) true := by
        simp [lowerEndpoint,lowerEndpointWords,hxp,hyp,hyyp,hwide,hnot,List.length_append,Nat.add_mod,hv1,hu0]
      have he2 : lowerEndpoint (u++[2],v++[1]) true =
          lowerEndpoint (u++[2],(v++[1])++[1]) true := by
        simp [lowerEndpoint,lowerEndpointWords,hxp,hyp,hyyp,hwide,hnot,List.length_append,Nat.add_mod,hv1,hu0]
      constructor
      · apply le_of_eq
        unfold lowerEndpoint lowerEndpointWords
        simp only [Prod.fst,Prod.snd,hxp,hyp,hwide,hnot]
        norm_num [Nat.add_mod,hv1]
        unfold lowerNaturalWords
        ring
      · simpa only [he1,he2] using hh
  · have hno : LowerEarlyTerminalNoTies (u++[2],v++[1]) :=
      ⟨hne,fun _ => ⟨hxn,Ne.symm hyn⟩⟩
    exact ⟨(lowerEarlyTerminal_endpoint_swap_nontie _ hno false).symm.le,
      (lowerEarlyTerminal_endpoint_swap_nontie _ hno true).le⟩
end Cross16TwoOne


open Freiman
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace Tie2Relax16

private theorem normalized_width_le (p : LowerPair) :
    lowerWidth (lowerNormalize p).2 ≤ lowerWidth (lowerNormalize p).1 := by
  unfold lowerNormalize
  split_ifs with h
  · exact h
  · exact (lt_of_not_ge h).le

private theorem ratio_append_two_ge_quarter (w : List ℕ+) :
    (1/4:ℝ) ≤ lowerRatio (w++[2]) := by
  have hr := lowerEarlyTerminal_ratio_range w
  rw [lowerEarlyTerminal_ratio_append]
  norm_num [prefixEval]
  rw [inv_eq_one_div]
  rw [le_div_iff₀ (by linarith [hr.1])]
  linarith [hr.2]

private theorem normal_true_strict (hw : LowerHistoryWidthLaw)
    (base words : LowerPair)
    (hlt : lowerWidth (base.1++words.1) < lowerWidth (base.2++words.2)) :
    lowerHistoryAtBase base [⟨true,true,lowerHistoryWH words⟩] := by
  have hn : ¬ lowerHistoryAtBase base [⟨false,false,lowerHistoryWH words⟩] := by
    rw [← (hw base words).1]
    exact not_le_of_gt hlt
  simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton,
    forall_eq, certBoundHolds, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte] at hn ⊢
  exact lt_of_not_ge hn

end Tie2Relax16

open Freiman
namespace Tie2Relax16

private theorem data (t : ℝ) (p : LowerPair) (hs : lowerState t p)
    (hd : lowerEarlyDomain p) :
    let Z := lowerNormalize p
    CDUnique15.GoodHead Z.1 ∧ CDUnique15.GoodHead Z.2 ∧
    Z.1 ≠ [] ∧ Z.2 ≠ [] ∧ Z.1.length%2 = Z.2.length%2 := by
  let Z := lowerNormalize p
  have hheads0 := CDUnique15.admissible_goodHead p hs.1
  have hheads : CDUnique15.GoodHead Z.1 ∧ CDUnique15.GoodHead Z.2 := by
    dsimp [Z]
    unfold lowerNormalize
    split <;> simp_all
  have hbox := hs.2.2.2
  have hne0 : p.1 ≠ [] ∧ p.2 ≠ [] := by
    constructor
    · intro hp
      have hh := hbox.1
      rw [hp] at hh
      norm_num [lowerRatio,lowerCD] at hh
    · intro hp
      have hh := hbox.2.2.1
      rw [hp] at hh
      norm_num [lowerRatio,lowerCD] at hh
  have hne : Z.1 ≠ [] ∧ Z.2 ≠ [] := by
    dsimp [Z]
    unfold lowerNormalize
    split <;> simp_all
  have hp : p.1.length%2 = p.2.length%2 := not_ne_iff.mp hd.1
  have hpar : Z.1.length%2 = Z.2.length%2 := by
    dsimp [Z]
    unfold lowerNormalize
    split
    · exact hp
    · exact hp.symm
  exact ⟨hheads.1,hheads.2,hne.1,hne.2,hpar⟩

end Tie2Relax16

open Freiman
attribute [local instance] Classical.propDecidable
namespace Tie2Relax16

private theorem fork_shape (p : LowerPair) (d : ℕ+) :
    lowerEarlyTerminalForkPair p (([2,2],[3,2]) : LowerLabel) true d =
      ((lowerNormalize p).1++[2,2],(lowerNormalize p).2++[3,2,d]) := by
  simp [lowerEarlyTerminalForkPair,lowerEarlyTerminalForkWords,
    section14LabelWords,lowerHistoryAppend,lowerHistorySet,lowerHistoryPick,
    List.append_assoc]

private theorem child_shape (p : LowerPair) (d : ℕ+)
    (hlt : lowerWidth ((lowerNormalize p).1++[2,2]) <
      lowerWidth ((lowerNormalize p).2++[3,2])) :
    lowerChild (lowerChild p (([2,2],[3,2]) : LowerLabel)) ([d],[]) =
      ((lowerNormalize p).2++[3,2,d],(lowerNormalize p).1++[2,2]) := by
  have hmid : lowerChild p (([2,2],[3,2]) : LowerLabel) =
      ((lowerNormalize p).1++[2,2],(lowerNormalize p).2++[3,2]) := by
    simp [lowerChild]
  have hnormmid : lowerNormalize
      ((lowerNormalize p).1++[2,2],(lowerNormalize p).2++[3,2]) =
      ((lowerNormalize p).2++[3,2],(lowerNormalize p).1++[2,2]) := by
    change (if lowerWidth ((lowerNormalize p).2++[3,2]) ≤
        lowerWidth ((lowerNormalize p).1++[2,2]) then
        ((lowerNormalize p).1++[2,2],(lowerNormalize p).2++[3,2]) else
        ((lowerNormalize p).2++[3,2],(lowerNormalize p).1++[2,2])) = _
    rw [if_neg (not_le_of_gt hlt)]
  rw [hmid]
  simp [lowerChild,hnormmid,List.append_assoc]

end Tie2Relax16

open Freiman
attribute [local instance] Classical.propDecidable
namespace Tie2Relax16

private theorem tie_shapes (p : LowerPair)
    (htie : lowerWidth (lowerEarlyTerminalForkPair p (([2,2],[3,2]) : LowerLabel) true 1).1 =
      lowerWidth ((lowerEarlyTerminalForkPair p (([2,2],[3,2]) : LowerLabel) true 1).2++[1])) :
    lowerWidth ((lowerNormalize p).1++[2,2]) =
        lowerWidth ((lowerNormalize p).2++[3,2,1,1]) ∧
      lowerWidth ((lowerNormalize p).1++[2,2]) <
        lowerWidth ((lowerNormalize p).2++[3,2]) := by
  have htie' : lowerWidth ((lowerNormalize p).1++[2,2]) =
      lowerWidth ((lowerNormalize p).2++[3,2,1,1]) := by
    simpa [lowerEarlyTerminalForkPair, lowerHistoryAppend, lowerEarlyTerminalForkWords,
      section14LabelWords, lowerHistorySet, lowerHistoryPick,
      List.append_assoc] using htie
  refine ⟨htie',?_⟩
  calc
    lowerWidth ((lowerNormalize p).1++[2,2]) =
        lowerWidth ((((lowerNormalize p).2++[3,2])++[1])++[1]) := by
      simpa [List.append_assoc] using htie'
    _ < lowerWidth (((lowerNormalize p).2++[3,2])++[1]) := Cross16Bounds.append_one_lt _
    _ < lowerWidth ((lowerNormalize p).2++[3,2]) := Cross16Bounds.append_one_lt _

end Tie2Relax16

open Freiman
namespace Tie2Relax16

private theorem norm_at (hw : LowerHistoryWidthLaw) (p : LowerPair)
    (hlt : lowerWidth ((lowerNormalize p).1++[2,2]) <
      lowerWidth ((lowerNormalize p).2++[3,2])) :
    lowerEarlyTerminalAt p
      [⟨true,true,lowerHistoryWH (([2,2],[3,2]) : LowerPair)⟩] := by
  have ha := normal_true_strict hw (lowerNormalize p)
    (([2,2],[3,2]) : LowerPair) (by simpa using hlt)
  simpa [lowerEarlyTerminalAt,section14Holds,lowerEarlyTerminalR,lowerEarlyTerminalS,
    lowerEarlyTerminalQ,lowerHistoryAtBase,lowerHistoryConditions] using ha

end Tie2Relax16

open Freiman
namespace Tie2Relax16

private theorem d1_cover (a b : List ℕ+)
    (ha : CDUnique15.GoodHead a) (hb : CDUnique15.GoodHead b)
    (hna : a ≠ []) (hnb : b ≠ []) (hpar : a.length%2=b.length%2)
    (htie : lowerWidth (a++[2,2]) = lowerWidth (b++[3,2,1,1]))
    (hlt : lowerWidth (a++[2,2]) < lowerWidth (b++[3,2])) :
    lowerCover (a++[2,2],b++[3,2,1]) ⊆
      lowerCover (b++[3,2,1],a++[2,2]) := by
  let u := a++[2]
  let v := b++[3,2]
  have hu := CDUnique15.goodHead_append a [2] ha hna
  have hv := CDUnique15.goodHead_append b [3,2] hb hnb
  have hp : u.length%2 ≠ v.length%2 := by
    dsimp [u,v]
    simp only [List.length_append]; norm_num; omega
  have hwide : lowerWidth (u++[2]) < lowerWidth v := by
    simpa [u,v,List.append_assoc] using hlt
  have hneuv : lowerWidth (u++[2]) ≠ lowerWidth (v++[1]) := by
    intro heq
    have hdrop : lowerWidth ((v++[1])++[1]) < lowerWidth (v++[1]) :=
      Cross16Bounds.append_one_lt _
    have ht : lowerWidth (u++[2]) = lowerWidth ((v++[1])++[1]) := by
      simpa [u,v,List.append_assoc] using htie
    linarith
  have hcontain := Cross16TwoOne.containment_of_ne u v hu hv
    (by simp [u]) (by simp [v]) hp hwide hneuv
  have hcontain' :
      lowerEndpoint (b++[3,2,1],a++[2,2]) false ≤
          lowerEndpoint (a++[2,2],b++[3,2,1]) false ∧
      lowerEndpoint (a++[2,2],b++[3,2,1]) true ≤
          lowerEndpoint (b++[3,2,1],a++[2,2]) true := by
    simpa [u,v,List.append_assoc] using hcontain
  intro x hx
  simp only [lowerCover,Set.mem_Icc] at hx ⊢
  exact And.intro (hcontain'.1.trans hx.1) (hx.2.trans hcontain'.2)

end Tie2Relax16


open Freiman
namespace Tie2Cross17
set_option maxHeartbeats 10000
set_option profiler true
set_option profiler.threshold 50

private theorem ratio_two_ge_quarter (w : List ℕ+) :
    (1/4:ℝ) ≤ lowerRatio (w++[2]) := by
  have hr := lowerEarlyTerminal_ratio_range w
  rw [lowerEarlyTerminal_ratio_append]
  norm_num [prefixEval]
  rw [inv_eq_one_div]
  rw [le_div_iff₀ (by linarith only [hr.1])]
  linarith only [hr.2]

private theorem d2_cover (a b : List ℕ+)
    (ha : CDUnique15.GoodHead a) (hb : CDUnique15.GoodHead b)
    (hna : a ≠ []) (hnb : b ≠ [])
    (hpar : a.length%2=b.length%2) :
    lowerCover (a++[2,2],b++[3,2,2]) ⊆
      lowerCover (b++[3,2,2],a++[2,2]) := by
  let u := a++[2]
  let v := b++[3,2]
  have hu := CDUnique15.goodHead_append a [2] ha hna
  have hv := CDUnique15.goodHead_append b [3,2] hb hnb
  have hnu : u ≠ [] := by simp only [u, List.append_eq_nil_iff]; simp
  have hnv : v ≠ [] := by simp only [v, List.append_eq_nil_iff]; simp
  have hp : u.length%2 ≠ v.length%2 := by
    simp only [u,v,List.length_append,List.length_cons,List.length_nil] at ⊢
    omega
  have hru : (1/4:ℝ) ≤ lowerRatio u := ratio_two_ge_quarter a
  have hvEq : (b++[3])++[2] = v := List.append_assoc b [3] [2]
  have hrv : (1/4:ℝ) ≤ lowerRatio v := by
    rw [← hvEq]
    exact ratio_two_ge_quarter (b++[3])
  have hno : LowerEarlyTerminalNoTies (u++[2],v++[2]) := by
    refine ⟨CDUnique15.width_ne_append_two u v hu hv hnu hnv hp, fun _ => ⟨?_,?_⟩⟩
    · exact Cross16.two_virtual_nontie_of_ratio u v hru hv
    · exact Ne.symm (Cross16.two_virtual_nontie_of_ratio v u hrv hu)
  have heq (upper : Bool) := lowerEarlyTerminal_endpoint_swap_nontie
    (u++[2],v++[2]) hno upper
  have h0 : lowerEndpoint (a++[2,2],b++[3,2,2]) false =
      lowerEndpoint (b++[3,2,2],a++[2,2]) false := by
    simpa only [u,v,List.append_assoc,List.cons_append,List.nil_append] using heq false
  have h1 : lowerEndpoint (a++[2,2],b++[3,2,2]) true =
      lowerEndpoint (b++[3,2,2],a++[2,2]) true := by
    simpa only [u,v,List.append_assoc,List.cons_append,List.nil_append] using heq true
  intro x hx
  simp only [lowerCover,Set.mem_Icc] at hx ⊢
  exact ⟨h0.symm.le.trans hx.1,hx.2.trans h1.le⟩
end Tie2Cross17


open Freiman
attribute [local instance] Classical.propDecidable

theorem solution (t : ℝ) (p : LowerPair)
    (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (l : LowerLabel) (hn : lowerEarlyTerminalNative p l)
    (he : lowerEarlyTerminalTie2 p l) (hw : LowerHistoryWidthLaw) :
    ∃ norm : CertBound, (true,norm) ∈ section14NormalCases (section14LabelWords l) ∧
      lowerEarlyTerminalAt p [norm] ∧
      ∀ d ∈ ([1,2] : List ℕ+),
        lowerCover (lowerEarlyTerminalForkPair p l true d) ⊆
          lowerCover (lowerChild (lowerChild p l) ([d],[])) := by
  rcases he with ⟨rfl, hend, htie⟩
  let a := (lowerNormalize p).1
  let b := (lowerNormalize p).2
  have hdata := Tie2Relax16.data t p hs hd
  have ha : CDUnique15.GoodHead a := hdata.1
  have hb : CDUnique15.GoodHead b := hdata.2.1
  have hna : a ≠ [] := hdata.2.2.1
  have hnb : b ≠ [] := hdata.2.2.2.1
  have hpar : a.length%2=b.length%2 := hdata.2.2.2.2
  have hshapes := Tie2Relax16.tie_shapes p htie
  have htie' : lowerWidth (a++[2,2]) = lowerWidth (b++[3,2,1,1]) := hshapes.1
  have hlt : lowerWidth (a++[2,2]) < lowerWidth (b++[3,2]) := hshapes.2
  let norm : CertBound := ⟨true,true,lowerHistoryWH (([2,2],[3,2]) : LowerPair)⟩
  refine ⟨norm, ?_, ?_, ?_⟩
  · simp [norm,section14NormalCases,section14LabelWords]
  · exact Tie2Relax16.norm_at hw p hshapes.2
  · intro d hdigit
    simp at hdigit
    rw [Tie2Relax16.fork_shape p d, Tie2Relax16.child_shape p d hshapes.2]
    change lowerCover (a++[2,2],b++[3,2,d]) ⊆
      lowerCover (b++[3,2,d],a++[2,2])
    rcases hdigit with rfl | rfl
    · exact Tie2Relax16.d1_cover a b ha hb hna hnb hpar htie' hlt
    · exact Tie2Cross17.d2_cover a b ha hb hna hnb hpar



#print axioms solution
