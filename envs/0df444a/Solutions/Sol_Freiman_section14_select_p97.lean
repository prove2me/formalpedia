-- Prove2me | solution 1 for Freiman.section14_select_p97
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T15:13:00.078073+00:00
-- url     : https://prove2.me/submissions/d9739808-2eae-44ac-bd7a-8a1f0476f1ee

import Definitions.Def_Freiman_section14Geometry
import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_prefixEval_difference
import Theorems.Thm_Freiman_prefixEval_mobius
import Theorems.Thm_Freiman_continuant_determinant
import Theorems.Thm_Freiman_continuant_denominator_pos
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_range
import Mathlib.Tactic
import Definitions.Def_Freiman_lowerCover
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_append
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_swap_nontie
import Theorems.Thm_Freiman_lower_forced_reflections
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Theorems.Thm_Freiman_trunk_endpoint_strict_order
import Mathlib.Tactic.FinCases

-- Source: agents.tiealgebra14.Injective

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

-- Source: agents.tiewidth14.Width

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

-- Source: agents.cdunique15.Unique

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

-- Source: agents.cdunique15.Width

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

-- Source: agents.mixed15.Alignment

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

-- Source: agents.lowties15.LowTie

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


-- Source: agents.p97_16.Virtual
open Freiman
set_option maxHeartbeats 0

private theorem virtual_left (a b : List ℕ+) (upper : Bool)
    (hp : a.length % 2 ≠ b.length % 2)
    (hw : lowerWidth b ≤ lowerWidth a)
    (heq : (a++[1]).length % 2 = b.length % 2)
    (hu : upper = decide (a.length % 2 = 0)) :
    lowerEndpoint (a,b) upper = lowerEndpoint (a++[1],b) upper := by
  unfold lowerEndpoint
  have heq' : (a.length+1) % 2 = b.length % 2 := by simpa using heq
  simp only [lowerEndpointWords,if_neg hp,hw,hu,if_pos,List.length_append,List.length_singleton]
  rw [if_pos heq']

private theorem virtual_right (a b : List ℕ+) (upper : Bool)
    (hp : a.length % 2 ≠ b.length % 2)
    (hw : lowerWidth b < lowerWidth a)
    (heq : b.length % 2 = (a++[1]).length % 2)
    (hu : upper = decide (a.length % 2 = 0)) :
    lowerEndpoint (b,a) upper = lowerEndpoint (b,a++[1]) upper := by
  unfold lowerEndpoint
  have hp' : b.length % 2 ≠ a.length % 2 := Ne.symm hp
  have hn : ¬ lowerWidth a ≤ lowerWidth b := not_le_of_gt hw
  have heq' : b.length % 2 = (a.length+1) % 2 := by simpa using heq
  simp only [lowerEndpointWords,if_neg hp',hn,if_false,hu,if_pos,
    List.length_append,List.length_singleton]
  rw [if_pos heq']

private theorem parent_tie_endpoint_end2 (a b : List ℕ+)
    (ha : CDUnique15.GoodHead a) (hb : CDUnique15.GoodHead b)
    (hna : a ≠ []) (hnb : b ≠ [])
    (hp : a.length % 2 ≠ b.length % 2)
    (hvu : lowerWidth b < lowerWidth a)
    (htie : lowerWidth (a++[1]) = lowerWidth b)
    (hend : lowerEnds b [2]) :
    (if a.length % 2 = 0 then
      lowerEndpoint (b,a) true ≤ lowerEndpoint (a,b) true
    else lowerEndpoint (a,b) false ≤ lowerEndpoint (b,a) false) := by
  have heq : (a++[1]).length % 2 = b.length % 2 := by
    rcases Nat.mod_two_eq_zero_or_one a.length with h0 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one b.length with k0 | k1 <;>
      simp only [List.length_append,List.length_singleton] <;> omega
  have hga := CDUnique15.goodHead_append a [1] ha hna
  have hlow := M7LowTies15.lowTieLaw (a++[1]) b hga hb (by simp) hnb
    ⟨a,rfl⟩ hend heq htie
  by_cases he : a.length % 2 = 0
  · rw [if_pos he]
    have hu : (a++[1]).length % 2 ≠ 0 := by
      simp only [List.length_append,List.length_singleton]
      omega
    simp only [if_neg hu] at hlow
    rw [virtual_right a b true hp hvu heq.symm (by simp [he]),
      virtual_left a b true hp hvu.le heq (by simp [he])]
    exact hlow
  · rw [if_neg he]
    have hu : (a++[1]).length % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one a.length with h0 | h1
      · exact (he h0).elim
      · simp only [List.length_append,List.length_singleton]; omega
    simp only [if_pos hu] at hlow
    rw [virtual_left a b false hp hvu.le heq (by simp [he]),
      virtual_right a b false hp hvu heq.symm (by simp [he])]
    exact hlow

private theorem ratio_lt_one (w : List ℕ+) (hg : CDUnique15.GoodHead w)
    (hn : w ≠ []) : lowerRatio w < 1 := by
  rw [lowerRatio, div_lt_one]
  · exact_mod_cast CDUnique15.cd_strict w hg
  · exact_mod_cast CDUnique15.snd_pos w

private theorem ratio_append_one_gt_half (w : List ℕ+)
    (hg : CDUnique15.GoodHead w) (hn : w ≠ []) :
    (1/2:ℝ) < lowerRatio (w++[1]) := by
  rw [lowerEarlyTerminal_ratio_append]
  simp only [List.reverse_cons,List.reverse_nil,List.nil_append,prefixEval]
  have hone : (((1 : ℕ+) : ℕ) : ℝ) = 1 := by norm_num
  rw [hone]
  change (1/2:ℝ) < 1 / (1 + lowerRatio w)
  have hp := CDUnique15.ratio_pos w hn
  have hl := ratio_lt_one w hg hn
  rw [lt_div_iff₀ (by linarith)]
  linarith

private theorem parent_tie_end1_eq (a b : List ℕ+)
    (ha : CDUnique15.GoodHead a) (hb : CDUnique15.GoodHead b)
    (hna : a ≠ []) (htie : lowerWidth (a++[1]) = lowerWidth b)
    (hend : lowerEnds b [1]) : b = a++[1] := by
  rcases hend with ⟨pre,rfl⟩
  have hnp : pre ≠ [] := by
    intro he
    subst pre
    norm_num [CDUnique15.GoodHead] at hb
  have hgp := CDUnique15.goodHead_prefix pre [1] hb
  have hga := CDUnique15.goodHead_append a [1] ha hna
  have hcd := M7TieWidth14.cd_eq_of_width_same_side (a++[1]) (pre++[1]) htie
    (Or.inl ⟨ratio_append_one_gt_half a ha hna,
      ratio_append_one_gt_half pre hgp hnp⟩)
  exact (CDUnique15.injective (a++[1]) (pre++[1]) hga hb hcd).symm


-- Source: agents.p97_16.End3

open Freiman
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace P97End3

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
    let E := prefixEval [1,3] lowerTau
    let F := prefixEval [1,2,1,3] lowerTau
    E = (3 + Real.sqrt 3) / 6 ∧ F = (52 + Real.sqrt 3) / 73 ∧
      F < E ∧ E ∈ Set.Icc (0 : ℝ) 1 ∧ F ∈ Set.Icc (0 : ℝ) 1 := by
  have hs := radical3.1
  have hp := radical3.2.1
  have hh := radical3.2.2
  have h3 : (1:ℝ) / (3 + (Real.sqrt 3 - 1)) = 2 - Real.sqrt 3 := by
    field_simp [show (3:ℝ) + (Real.sqrt 3 - 1) ≠ 0 by nlinarith]
    nlinarith
  have hE : prefixEval [1,3] lowerTau = (3 + Real.sqrt 3) / 6 := by
    dsimp [lowerTau, prefixEval]
    norm_num only [PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat]
    rw [h3]
    field_simp [show (1:ℝ) + (2 - Real.sqrt 3) ≠ 0 by nlinarith]
    nlinarith
  have h2 : (1:ℝ) / (2 + (3 + Real.sqrt 3) / 6) =
      (15 - Real.sqrt 3) / 37 := by
    field_simp [show (2:ℝ) + (3 + Real.sqrt 3) / 6 ≠ 0 by nlinarith]
    nlinarith
  have hF : prefixEval [1,2,1,3] lowerTau = (52 + Real.sqrt 3) / 73 := by
    dsimp [lowerTau, prefixEval]
    norm_num only [PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat]
    rw [h3]
    have he : (1:ℝ) / (1 + (2 - Real.sqrt 3)) = (3 + Real.sqrt 3) / 6 := by
      field_simp [show (1:ℝ) + (2 - Real.sqrt 3) ≠ 0 by nlinarith]
      nlinarith
    rw [he, h2]
    rw [div_eq_iff (show (1:ℝ) + (15 - Real.sqrt 3) / 37 ≠ 0 by nlinarith)]
    field_simp
    nlinarith
  rw [hE, hF]
  refine ⟨rfl, rfl, by nlinarith, ⟨by positivity, by nlinarith⟩,
    ⟨by positivity, by nlinarith⟩⟩

private theorem cd_append_one (w : List ℕ+) :
    lowerCD (w ++ [1]) = ((lowerCD w).2, (lowerCD w).1 + (lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]

private theorem cd_append_two (w : List ℕ+) :
    lowerCD (w ++ [2]) = ((lowerCD w).2, (lowerCD w).1 + 2*(lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]

private theorem cd_append_e (w : List ℕ+) :
    lowerCD (w ++ [1,3]) = ((lowerCD w).1 + (lowerCD w).2,
      3*(lowerCD w).1 + 4*(lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]
  ring

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
    let E := prefixEval [1,3] lowerTau
    let F := prefixEval [1,2,1,3] lowerTau
    |prefixEval w E - prefixEval w F| =
      (E-F) / ((((lowerCD w).2:ℝ)+E*(lowerCD w).1) *
        (((lowerCD w).2:ℝ)+F*(lowerCD w).1)) := by
  dsimp only
  rw [prefixEval_difference w _ _ endpoint_tails.2.2.2.1 endpoint_tails.2.2.2.2]
  rw [abs_of_pos (sub_pos.mpr endpoint_tails.2.2.1), cd_eq]

end P97End3

namespace P97End3

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

end P97End3

namespace P97End3

private theorem tie_not_ends_three (a b : List ℕ+)
    (ha : lowerEnds a [3,1])
    (hb : lowerEnds b [3])
    (htie : lowerWidth (a++[1]) = lowerWidth b) : False := by
  rcases ha with ⟨P,rfl⟩
  rcases hb with ⟨Q,rfl⟩
  have hP := q_pos P
  have hQ := q_pos Q
  have hu : lowerCD (P++[3,1]++[1]) =
      ((lowerCD P).1 + 4*(lowerCD P).2,
       2*(lowerCD P).1 + 7*(lowerCD P).2) := by
    rw [show P++[3,1]++[1] = ((P++[3])++[1])++[1] by simp]
    rw [CDUnique15.cd_snoc,CDUnique15.cd_snoc,CDUnique15.cd_snoc]
    norm_num
    omega
  have hv : lowerCD (Q++[3]) =
      ((lowerCD Q).2,(lowerCD Q).1+3*(lowerCD Q).2) := by
    rw [CDUnique15.cd_snoc]
    norm_num
  rcases cd_classify (P++[3,1]++[1]) (Q++[3]) htie with heq | href
  · rw [hu,hv] at heq
    simp only [Prod.mk.injEq] at heq
    have hqn : 0 < (lowerCD Q).2 := by exact_mod_cast hQ
    omega
  · rw [hu,hv] at href
    simp only [Prod.fst,Prod.snd] at href
    push_cast at href
    have hpR : (0:ℝ) < (lowerCD P).2 := hP
    have hqR : (0:ℝ) ≤ (lowerCD Q).1 := by positivity
    have hqD : (0:ℝ) < (lowerCD Q).2 := hQ
    nlinarith

end P97End3


-- Source: agents.p97_16.Parent
open Freiman
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0

private def smallEnd (w : List ℕ+) : Prop :=
  lowerEnds w [1] ∨ lowerEnds w [2] ∨ lowerEnds w [3]

private lemma smallEnd_of_last (w : List ℕ+) (hn : w ≠ [])
    (hl : ((w.getLast hn : ℕ)) ≤ 3) : smallEnd w := by
  have hp : 0 < (w.getLast hn : ℕ) := PNat.pos _
  have hd : (w.getLast hn : ℕ) = 1 ∨ (w.getLast hn : ℕ) = 2 ∨
      (w.getLast hn : ℕ) = 3 := by omega
  have hs := List.dropLast_append_getLast hn
  rcases hd with h | h | h
  · have he : w.getLast hn = 1 := by exact_mod_cast h
    left
    exact ⟨w.dropLast, by simpa [he] using hs⟩
  · have he : w.getLast hn = 2 := by exact_mod_cast h
    right; left
    exact ⟨w.dropLast, by simpa [he] using hs⟩
  · have he : w.getLast hn = 3 := by exact_mod_cast h
    right; right
    exact ⟨w.dropLast, by simpa [he] using hs⟩

private lemma append_smallEnd (w u : List ℕ+) (hw : smallEnd w)
    (hu : ∀ d ∈ u, (d : ℕ) ≤ 3) : smallEnd (w ++ u) := by
  induction u generalizing w with
  | nil => simpa using hw
  | cons a u ih =>
      rw [show w ++ a :: u = (w ++ [a]) ++ u by simp]
      apply ih (w := w ++ [a])
      · have ha := hu a (by simp)
        have hp : 0 < (a : ℕ) := PNat.pos a
        have : (a : ℕ) = 1 ∨ (a : ℕ) = 2 ∨ (a : ℕ) = 3 := by omega
        rcases this with h | h | h
        · have ha1 : a = 1 := by exact_mod_cast h
          left; exact ⟨w, by simp [ha1]⟩
        · have ha2 : a = 2 := by exact_mod_cast h
          right; left; exact ⟨w, by simp [ha2]⟩
        · have ha3 : a = 3 := by exact_mod_cast h
          right; right; exact ⟨w, by simp [ha3]⟩
      · intro d hd
        exact hu d (by simp [hd])

private lemma admissible_smallEnds (p : LowerPair) (ha : lowerAdmissible p) :
    smallEnd p.1 ∧ smallEnd p.2 := by
  rcases ha.1 with ⟨c,hc,u,v,rfl,hu,hv⟩
  have hbase : smallEnd c.1 ∧ smallEnd c.2 := by
    simp only [lowerCores,lowerBaseCores,List.mem_append,List.mem_cons,List.mem_map,
      List.not_mem_nil,or_false] at hc
    rcases hc with hc | ⟨d,hd,rfl⟩
    · rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> constructor <;> apply smallEnd_of_last <;> simp
    · rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> constructor <;> apply smallEnd_of_last <;> simp
  exact ⟨append_smallEnd _ _ hbase.1 hu,append_smallEnd _ _ hbase.2 hv⟩

private theorem endpoint_swap_append_one (w : List ℕ+)
    (hlt : lowerWidth (w++[1]) < lowerWidth w) (upper : Bool) :
    lowerEndpoint (w++[1],w) upper = lowerEndpoint (w,w++[1]) upper := by
  unfold lowerEndpoint lowerEndpointWords
  have hp : (w++[1]).length%2 ≠ w.length%2 := by simp; omega
  rw [if_neg hp,if_neg hp.symm]
  have hn := not_le_of_gt hlt
  simp only [hlt.le,hn,if_true,if_false]
  by_cases hu : upper = decide (w.length%2=0)
  · simp only [if_pos hu]
  · simp only [if_neg hu,lowerNaturalWords]; ring

private theorem parent_tie_word (t : ℝ) (w : List ℕ+)
    (hlt : lowerWidth (w++[1]) < lowerWidth w)
    (hs : lowerState t (w++[1],w)) :
    lowerLocalCoordinate (w++[1],w) t ≤ section14LocalEndpoint (w++[1],w) ([],[]) true := by
  rcases hs with ⟨_,_,hc,_⟩
  have hn : lowerNormalize ((w++[1],w):LowerPair)=(w,w++[1]) := by simp [lowerNormalize,not_le_of_gt hlt]
  by_cases he : w.length%2=0
  · simp only [lowerLocalCoordinate,section14LocalEndpoint,hn,he,if_pos,List.append_nil]
    rw [← endpoint_swap_append_one w hlt true]; exact hc.2
  · simp only [lowerLocalCoordinate,section14LocalEndpoint,hn,he,List.append_nil,Bool.not_true]
    rw [← endpoint_swap_append_one w hlt false]; exact neg_le_neg hc.1

private theorem p97_parent_upper (t : ℝ) (p : LowerPair) (hs : lowerState t p)
    (hm : lowerMixed p) (hL : lowerL p) :
    lowerLocalCoordinate p t ≤ section14LocalEndpoint p ([],[]) true := by
  rcases hs with ⟨had,hgood,hcover,hbox⟩
  have hforced := lower_forced_reflections p hgood hbox
  by_cases hw : lowerWidth p.2 ≤ lowerWidth p.1
  · have hn : lowerNormalize p=p := by simp [lowerNormalize,hw]
    by_cases he : p.1.length%2=0
    · simpa [lowerLocalCoordinate,section14LocalEndpoint,hn,he] using hcover.2
    · simpa [lowerLocalCoordinate,section14LocalEndpoint,hn,he] using neg_le_neg hcover.1
  · have hlt : lowerWidth p.1 < lowerWidth p.2 := lt_of_not_ge hw
    have hn : lowerNormalize p=(p.2,p.1) := by simp [lowerNormalize,hw]
    by_cases htie : lowerWidth (p.2++[1]) = lowerWidth p.1
    · have heads := CDUnique15.admissible_goodHead p had
      have hne1 : p.1 ≠ [] := by
        intro he
        have hx := hbox.1
        rw [he] at hx
        norm_num [lowerRatio, lowerCD] at hx
      have hne2 : p.2 ≠ [] := by
        intro he
        have hx := hbox.2.2.1
        rw [he] at hx
        norm_num [lowerRatio, lowerCD] at hx
      have hends := admissible_smallEnds p had
      have ha31 : lowerEnds p.2 [3,1] := by simpa [lowerL,hn] using hL
      rcases hends.1 with he1 | he2 | he3
      · have heq := parent_tie_end1_eq p.2 p.1 heads.2 heads.1 hne2 htie he1
        have hp_eq : p = (p.2++[1],p.2) := by
          apply Prod.ext
          · exact heq
          · rfl
        have hsword : lowerState t (p.2++[1],p.2) := by
          rw [← hp_eq]
          exact ⟨had,hgood,hcover,hbox⟩
        rw [hp_eq]
        exact parent_tie_word t p.2 (by simpa [heq] using hlt) hsword
      · have hal := parent_tie_endpoint_end2 p.2 p.1 heads.2 heads.1 hne2 hne1
          (by exact Ne.symm hm) hlt htie he2
        by_cases he : p.2.length%2=0
        · simp only [if_pos he] at hal
          simpa [lowerLocalCoordinate,section14LocalEndpoint,hn,he] using hcover.2.trans hal
        · simp only [if_neg he] at hal
          have hx := hal.trans hcover.1
          simpa [lowerLocalCoordinate,section14LocalEndpoint,hn,he] using neg_le_neg hx
      · exact (P97End3.tie_not_ends_three p.2 p.1 ha31 he3 htie).elim
    · have hno : LowerEarlyTerminalNoTies p := by
        rw [LowerEarlyTerminalNoTies]
        refine ⟨hlt.ne,fun _ => ⟨?_,?_⟩⟩
        · simpa [hn] using hforced.2.2.2.ne
        · simpa [hn] using (Ne.symm htie)
      have hswap (upper : Bool) :
          lowerEndpoint p upper = lowerEndpoint (p.2,p.1) upper :=
        lowerEarlyTerminal_endpoint_swap_nontie p hno upper
      by_cases he : p.2.length%2=0
      · simp only [lowerLocalCoordinate,hn,Prod.fst,if_pos he]
        unfold section14LocalEndpoint
        simp only [hn,Prod.fst,Prod.snd,List.nil_append,List.append_nil,if_pos he]
        simpa only [hswap true] using hcover.2
      · have hx := neg_le_neg hcover.1
        simp only [lowerLocalCoordinate,hn,Prod.fst,if_neg he]
        unfold section14LocalEndpoint
        simp only [hn,Prod.fst,Prod.snd,List.nil_append,List.append_nil,if_neg he,Bool.not_true]
        simpa only [hswap false] using hx


-- Source: agents.p97_16.Assembly

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Freiman

private theorem two_Icc_cover (a b c d x : ℝ) (hcx : c ≤ x) (hxb : x ≤ b)
    (hac : a ≤ d) : x ∈ Set.Icc a b ∨ x ∈ Set.Icc c d := by
  by_cases hxd : x ≤ d
  · exact Or.inr ⟨hcx, hxd⟩
  · exact Or.inl ⟨le_trans hac (le_of_lt (lt_of_not_ge hxd)), hxb⟩

private theorem strictGood_good (p : LowerPair) (h : lowerStrictGood p) : lowerGood p := by
  rw [lowerStrictGood] at h
  rcases lt_min_iff.mp h with ⟨h1, h2⟩
  rw [lowerGood, lowerCover]
  refine ⟨max (lowerEndpoint (lowerChild p ([1], [])) false)
    (lowerEndpoint (lowerChild p ([2], [])) false), ?_⟩
  constructor
  · exact ⟨le_max_left _ _, h1.le⟩
  · exact ⟨le_max_right _ _, h2.le⟩

private theorem p97_selection_core (t : ℝ) (p : LowerPair)
    (hm : lowerMixed p) (hn2 : ¬ lowerH p 2) (h5 : lowerH p 5) (hL : lowerL p)
    (hp97 : lowerP97Anchor p t) (hg : section14RawGeometry p)
    (hgood1 : lowerGood (lowerChild p ([1], [])))
    (hgood2 : lowerGood (lowerChild p ([2], [])))
    (hparentUpper : lowerLocalCoordinate p t ≤ section14LocalEndpoint p ([], []) true) :
    lowerNumericSuccessor t p := by
  classical
  have hraw : section14RawList p = [([1], []), ([2], [])] := by
    simp [section14RawList, hn2, h5, hL]
  have htarget : section14TargetLower p = true := by
    simp [section14TargetLower, hn2, h5, hL]
  have hspec (s : Section14Spec)
      (hspec : s ∈ section14ExpectedSpecs [([1], []), ([2], [])] true) :
      section14SpecHolds p s := by
    apply hg s
    simpa [hraw, htarget] using hspec
  have hcontact :
      section14LocalEndpoint p ([1], []) false ≤
        section14LocalEndpoint p ([2], []) true := by
    simpa [section14SpecHolds, section14Holds] using
      hspec ⟨([2], []), true, ([1], []), false, false, []⟩ (by
        simp [section14ExpectedSpecs, section14NormalCases, section14LabelWords])
  have hupper :
      section14LocalEndpoint p ([], []) true ≤
        section14LocalEndpoint p ([1], []) true := by
    simpa [section14SpecHolds, section14Holds] using
      hspec ⟨([1], []), true, ([], []), true, false, []⟩ (by
        simp [section14ExpectedSpecs, section14NormalCases, section14LabelWords])
  have hanchor := hp97 hm hn2 h5 hL
  have hu := two_Icc_cover
    (section14LocalEndpoint p ([1], []) false)
    (section14LocalEndpoint p ([1], []) true)
    (section14LocalEndpoint p ([2], []) false)
    (section14LocalEndpoint p ([2], []) true)
    (lowerLocalCoordinate p t) hanchor (hparentUpper.trans hupper) hcontact
  have hoff1 : lowerOffered p ([1], []) := by
    simp [lowerOffered, hm, lowerMixedList, hn2, h5, hL]
  have hoff2 : lowerOffered p ([2], []) := by
    simp [lowerOffered, hm, lowerMixedList, hn2, h5, hL]
  right
  rcases hu with hu | hu
  · refine ⟨([1], []), hoff1, hgood1, ?_⟩
    by_cases he : (lowerNormalize p).1.length % 2 = 0
    · simpa [lowerCover, lowerChild, lowerLocalCoordinate,
        section14LocalEndpoint, he] using hu
    · simp [lowerCover, lowerChild, lowerLocalCoordinate,
        section14LocalEndpoint, he] at hu ⊢
      exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
  · refine ⟨([2], []), hoff2, hgood2, ?_⟩
    by_cases he : (lowerNormalize p).1.length % 2 = 0
    · simpa [lowerCover, lowerChild, lowerLocalCoordinate,
        section14LocalEndpoint, he] using hu
    · simp [lowerCover, lowerChild, lowerLocalCoordinate,
        section14LocalEndpoint, he] at hu ⊢
      exact ⟨by linarith [hu.2], by linarith [hu.1]⟩

private theorem p97_parent_upper_of_not_tie (t : ℝ) (p : LowerPair)
    (hs : lowerState t p) (hm : lowerMixed p)
    (hne : lowerWidth ((lowerNormalize p).1 ++ [1]) ≠ lowerWidth (lowerNormalize p).2) :
    lowerLocalCoordinate p t ≤ section14LocalEndpoint p ([], []) true := by
  classical
  rcases hs with ⟨_, hg, hcover, hbox⟩
  have hforced := lower_forced_reflections p hg hbox
  by_cases hp : lowerWidth p.2 ≤ lowerWidth p.1
  · have hnorm : lowerNormalize p = p := by simp [lowerNormalize, hp]
    by_cases he : p.1.length % 2 = 0
    · simpa [lowerLocalCoordinate, section14LocalEndpoint, hnorm, he] using hcover.2
    · have hx : -t ≤ -lowerEndpoint p false := neg_le_neg hcover.1
      simpa [lowerLocalCoordinate, section14LocalEndpoint, hnorm, he] using hx
  · have hlt : lowerWidth p.1 < lowerWidth p.2 := lt_of_not_ge hp
    have hnorm : lowerNormalize p = (p.2, p.1) := by simp [lowerNormalize, hp]
    have hmix : p.1.length % 2 ≠ p.2.length % 2 := hm
    have hno : LowerEarlyTerminalNoTies p := by
      rw [LowerEarlyTerminalNoTies]
      refine ⟨hlt.ne, fun _ => ⟨?_, ?_⟩⟩
      · simpa [hnorm] using hforced.2.2.2.ne
      · simpa [hnorm] using hne.symm
    have hswap (upper : Bool) : lowerEndpoint p upper = lowerEndpoint (p.2,p.1) upper :=
      lowerEarlyTerminal_endpoint_swap_nontie p hno upper
    by_cases he : p.2.length % 2 = 0
    · simp only [lowerLocalCoordinate, hnorm, Prod.fst, if_pos he]
      unfold section14LocalEndpoint
      simp only [hnorm, Prod.fst, Prod.snd, List.nil_append, List.append_nil, if_pos he]
      simpa only [hswap true] using hcover.2
    · have hx : -t ≤ -lowerEndpoint p false := neg_le_neg hcover.1
      simp only [lowerLocalCoordinate, hnorm, Prod.fst, if_neg he]
      unfold section14LocalEndpoint
      simp only [hnorm, Prod.fst, Prod.snd, List.nil_append, List.append_nil, if_neg he, Bool.not_true]
      simpa only [hswap false] using hx

private theorem Freiman.section14_select_p97_of_cross
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : lowerMixed p ∧ ¬ lowerH p 2 ∧ lowerH p 5 ∧ lowerL p) (hg : section14RawGeometry p)
    (hcross : ∀ d : ℕ+, d = 1 ∨ d = 2 →
      lowerWidth ((lowerNormalize p).1++[d]) < lowerWidth (lowerNormalize p).2 →
      lowerEndpoint ((lowerNormalize p).1++[d],(lowerNormalize p).2++[2]) false <
        lowerEndpoint ((lowerNormalize p).1++[d],(lowerNormalize p).2++[1]) true →
      lowerEndpoint ((lowerNormalize p).1++[d],(lowerNormalize p).2++[1]) false <
        lowerEndpoint ((lowerNormalize p).1++[d],(lowerNormalize p).2++[2]) true →
      lowerEndpoint ((lowerNormalize p).2++[2],(lowerNormalize p).1++[d]) false <
        lowerEndpoint ((lowerNormalize p).2++[1],(lowerNormalize p).1++[d]) true ∧
      lowerEndpoint ((lowerNormalize p).2++[1],(lowerNormalize p).1++[d]) false <
        lowerEndpoint ((lowerNormalize p).2++[2],(lowerNormalize p).1++[d]) true) :
    lowerNumericSuccessor t p := by
  classical
  rcases hc with ⟨hm, hn2, h5, hL⟩
  have hraw : section14RawList p = [([1], []), ([2], [])] := by
    simp [section14RawList, hn2, h5, hL]
  have htarget : section14TargetLower p = true := by
    simp [section14TargetLower, hn2, h5, hL]
  have hspec (s : Section14Spec)
      (hspec : s ∈ section14ExpectedSpecs [([1], []), ([2], [])] true) :
      section14SpecHolds p s := by
    apply hg s
    simpa [hraw, htarget] using hspec
  have hone :
      section14LocalEndpoint p ([1], []) false ≤
        section14LocalEndpoint p ([1], []) true := by
    simpa [section14SpecHolds, section14Holds] using
      hspec ⟨([1], []), true, ([1], []), false, false, []⟩ (by
        simp [section14ExpectedSpecs, section14NormalCases, section14LabelWords])
  have htwo :
      section14LocalEndpoint p ([2], []) false ≤
        section14LocalEndpoint p ([2], []) true := by
    simpa [section14SpecHolds, section14Holds] using
      hspec ⟨([2], []), true, ([2], []), false, false, []⟩ (by
        simp [section14ExpectedSpecs, section14NormalCases, section14LabelWords])
  have hcontact12 :
      section14LocalEndpoint p ([2], []) false ≤
        section14LocalEndpoint p ([1], []) true := by
    simpa [section14SpecHolds, section14Holds] using
      hspec ⟨([1], []), true, ([2], []), false, false, []⟩ (by
        simp [section14ExpectedSpecs, section14NormalCases, section14LabelWords])
  have hcontact21 :
      section14LocalEndpoint p ([1], []) false ≤
        section14LocalEndpoint p ([2], []) true := by
    simpa [section14SpecHolds, section14Holds] using
      hspec ⟨([2], []), true, ([1], []), false, false, []⟩ (by
        simp [section14ExpectedSpecs, section14NormalCases, section14LabelWords])
  have hupper :
      section14LocalEndpoint p ([], []) true ≤
        section14LocalEndpoint p ([1], []) true := by
    simpa [section14SpecHolds, section14Holds] using
      hspec ⟨([1], []), true, ([], []), true, false, []⟩ (by
        simp [section14ExpectedSpecs, section14NormalCases, section14LabelWords])
  have h1f12 :
      section14Holds [⟨false, false, lowerHistoryWH ([1], [])⟩]
          (section14R p) (section14S p) (section14Q p) →
        section14LocalEndpoint p ([1,2], []) false <
          section14LocalEndpoint p ([1,1], []) true := by
    simpa [section14SpecHolds] using
      hspec ⟨([1,1], []), true, ([1,2], []), false, true,
        [⟨false, false, lowerHistoryWH ([1], [])⟩]⟩ (by
          simp [section14ExpectedSpecs, section14NormalCases, section14LabelWords,
            lowerHistorySet, lowerHistoryPick])
  have h1f21 :
      section14Holds [⟨false, false, lowerHistoryWH ([1], [])⟩]
          (section14R p) (section14S p) (section14Q p) →
        section14LocalEndpoint p ([1,1], []) false <
          section14LocalEndpoint p ([1,2], []) true := by
    simpa [section14SpecHolds] using
      hspec ⟨([1,2], []), true, ([1,1], []), false, true,
        [⟨false, false, lowerHistoryWH ([1], [])⟩]⟩ (by
          simp [section14ExpectedSpecs, section14NormalCases, section14LabelWords,
            lowerHistorySet, lowerHistoryPick])
  have h1t12 :
      section14Holds [⟨true, true, lowerHistoryWH ([1], [])⟩]
          (section14R p) (section14S p) (section14Q p) →
        section14LocalEndpoint p ([1], [2]) false <
          section14LocalEndpoint p ([1], [1]) true := by
    simpa [section14SpecHolds] using
      hspec ⟨([1], [1]), true, ([1], [2]), false, true,
        [⟨true, true, lowerHistoryWH ([1], [])⟩]⟩ (by
          simp [section14ExpectedSpecs, section14NormalCases, section14LabelWords,
            lowerHistorySet, lowerHistoryPick])
  have h1t21 :
      section14Holds [⟨true, true, lowerHistoryWH ([1], [])⟩]
          (section14R p) (section14S p) (section14Q p) →
        section14LocalEndpoint p ([1], [1]) false <
          section14LocalEndpoint p ([1], [2]) true := by
    simpa [section14SpecHolds] using
      hspec ⟨([1], [2]), true, ([1], [1]), false, true,
        [⟨true, true, lowerHistoryWH ([1], [])⟩]⟩ (by
          simp [section14ExpectedSpecs, section14NormalCases, section14LabelWords,
            lowerHistorySet, lowerHistoryPick])
  have hgood1 : lowerStrictGood (lowerChild p ([1], [])) := by
    let Z := lowerNormalize p
    by_cases hw : lowerWidth Z.2 ≤ lowerWidth (Z.1 ++ [1])
    · have hn : section14Holds [⟨false, false, lowerHistoryWH ([1], [])⟩]
          (section14R p) (section14S p) (section14Q p) := by
        have hw0 : lowerWidth (Z.2 ++ []) ≤ lowerWidth (Z.1 ++ [1]) := by simpa using hw
        have ht := (lowerHistory_width_threshold Z ([1], [])).1.mp hw0
        simpa [lowerHistoryAtBase, lowerHistoryConditions, section14Holds,
          section14R, section14S, section14Q, Z] using ht
      have ha := h1f12 hn
      have hb := h1f21 hn
      have hc : lowerChild p ([1], []) = (Z.1 ++ [1], Z.2) := by
        simp [lowerChild, Z]
      have hca : lowerChild (lowerChild p ([1], [])) ([1], []) =
          (Z.1 ++ [1,1], Z.2) := by
        rw [hc]
        simp [lowerChild, lowerNormalize, hw]
      have hcb : lowerChild (lowerChild p ([1], [])) ([2], []) =
          (Z.1 ++ [1,2], Z.2) := by
        rw [hc]
        simp [lowerChild, lowerNormalize, hw]
      have hoa := trunk_endpoint_strict_order (Z.1 ++ [1,1], Z.2)
      have hob := trunk_endpoint_strict_order (Z.1 ++ [1,2], Z.2)
      rw [lowerStrictGood, hca, hcb]
      simp only [max_lt_iff, lt_min_iff]
      by_cases he : Z.1.length % 2 = 0
      · simp [section14LocalEndpoint, Z, he] at ha hb
        exact ⟨⟨hoa, ha⟩, ⟨hb, hob⟩⟩
      ·
        simp [section14LocalEndpoint, Z, he] at ha hb
        exact ⟨⟨hoa, hb⟩, ⟨ha, hob⟩⟩
    · have hw' : lowerWidth (Z.1 ++ [1]) < lowerWidth Z.2 := lt_of_not_ge hw
      have hn : section14Holds [⟨true, true, lowerHistoryWH ([1], [])⟩]
          (section14R p) (section14S p) (section14Q p) := by
        have hn0 : ¬ section14Holds [⟨false, false, lowerHistoryWH ([1], [])⟩]
            (section14R p) (section14S p) (section14Q p) := by
          intro ht
          apply hw
          have hw0 := (lowerHistory_width_threshold Z ([1], [])).1.mpr (by
            simpa [lowerHistoryAtBase, lowerHistoryConditions, section14Holds,
              section14R, section14S, section14Q, Z] using ht)
          simpa using hw0
        simpa [section14Holds, certBoundHolds] using hn0
      have ha := h1t12 hn
      have hb := h1t21 hn
      have hc : lowerChild p ([1], []) = (Z.1 ++ [1], Z.2) := by
        simp [lowerChild, Z]
      have hca : lowerChild (lowerChild p ([1], [])) ([1], []) =
          (Z.2 ++ [1], Z.1 ++ [1]) := by
        rw [hc]
        simp [lowerChild, lowerNormalize, hw, hw']
      have hcb : lowerChild (lowerChild p ([1], [])) ([2], []) =
          (Z.2 ++ [2], Z.1 ++ [1]) := by
        rw [hc]
        simp [lowerChild, lowerNormalize, hw, hw']
      have hoa := trunk_endpoint_strict_order (Z.2 ++ [1], Z.1 ++ [1])
      have hob := trunk_endpoint_strict_order (Z.2 ++ [2], Z.1 ++ [1])
      rw [lowerStrictGood, hca, hcb]
      simp only [max_lt_iff, lt_min_iff]
      by_cases he : Z.1.length % 2 = 0
      · simp [section14LocalEndpoint, Z, he] at ha hb
        have hx := hcross 1 (Or.inl rfl) (by simpa [Z] using hw')
          (by simpa [Z] using ha) (by simpa [Z] using hb)
        exact ⟨⟨hoa, hx.1⟩, ⟨hx.2, hob⟩⟩
      ·
        simp [section14LocalEndpoint, Z, he] at ha hb
        have hx := hcross 1 (Or.inl rfl) (by simpa [Z] using hw')
          (by simpa [Z] using hb) (by simpa [Z] using ha)
        exact ⟨⟨hoa, hx.1⟩, ⟨hx.2, hob⟩⟩
  have h2f12 :
      section14Holds [⟨false, false, lowerHistoryWH ([2], [])⟩]
          (section14R p) (section14S p) (section14Q p) →
        section14LocalEndpoint p ([2,1], []) false <
          section14LocalEndpoint p ([2,2], []) true := by
    simpa [section14SpecHolds] using
      hspec ⟨([2,2], []), true, ([2,1], []), false, true,
        [⟨false, false, lowerHistoryWH ([2], [])⟩]⟩ (by
          simp [section14ExpectedSpecs, section14NormalCases, section14LabelWords,
            lowerHistorySet, lowerHistoryPick])
  have h2f21 :
      section14Holds [⟨false, false, lowerHistoryWH ([2], [])⟩]
          (section14R p) (section14S p) (section14Q p) →
        section14LocalEndpoint p ([2,2], []) false <
          section14LocalEndpoint p ([2,1], []) true := by
    simpa [section14SpecHolds] using
      hspec ⟨([2,1], []), true, ([2,2], []), false, true,
        [⟨false, false, lowerHistoryWH ([2], [])⟩]⟩ (by
          simp [section14ExpectedSpecs, section14NormalCases, section14LabelWords,
            lowerHistorySet, lowerHistoryPick])
  have h2t12 :
      section14Holds [⟨true, true, lowerHistoryWH ([2], [])⟩]
          (section14R p) (section14S p) (section14Q p) →
        section14LocalEndpoint p ([2], [2]) false <
          section14LocalEndpoint p ([2], [1]) true := by
    simpa [section14SpecHolds] using
      hspec ⟨([2], [1]), true, ([2], [2]), false, true,
        [⟨true, true, lowerHistoryWH ([2], [])⟩]⟩ (by
          simp [section14ExpectedSpecs, section14NormalCases, section14LabelWords,
            lowerHistorySet, lowerHistoryPick])
  have h2t21 :
      section14Holds [⟨true, true, lowerHistoryWH ([2], [])⟩]
          (section14R p) (section14S p) (section14Q p) →
        section14LocalEndpoint p ([2], [1]) false <
          section14LocalEndpoint p ([2], [2]) true := by
    simpa [section14SpecHolds] using
      hspec ⟨([2], [2]), true, ([2], [1]), false, true,
        [⟨true, true, lowerHistoryWH ([2], [])⟩]⟩ (by
          simp [section14ExpectedSpecs, section14NormalCases, section14LabelWords,
            lowerHistorySet, lowerHistoryPick])
  have hgood2 : lowerStrictGood (lowerChild p ([2], [])) := by
    let Z := lowerNormalize p
    by_cases hw : lowerWidth Z.2 ≤ lowerWidth (Z.1 ++ [2])
    · have hn : section14Holds [⟨false, false, lowerHistoryWH ([2], [])⟩]
          (section14R p) (section14S p) (section14Q p) := by
        have hw0 : lowerWidth (Z.2 ++ []) ≤ lowerWidth (Z.1 ++ [2]) := by simpa using hw
        have ht := (lowerHistory_width_threshold Z ([2], [])).1.mp hw0
        simpa [lowerHistoryAtBase, lowerHistoryConditions, section14Holds,
          section14R, section14S, section14Q, Z] using ht
      have ha := h2f12 hn
      have hb := h2f21 hn
      have hc : lowerChild p ([2], []) = (Z.1 ++ [2], Z.2) := by
        simp [lowerChild, Z]
      have hca : lowerChild (lowerChild p ([2], [])) ([1], []) =
          (Z.1 ++ [2,1], Z.2) := by
        rw [hc]
        simp [lowerChild, lowerNormalize, hw]
      have hcb : lowerChild (lowerChild p ([2], [])) ([2], []) =
          (Z.1 ++ [2,2], Z.2) := by
        rw [hc]
        simp [lowerChild, lowerNormalize, hw]
      have hoa := trunk_endpoint_strict_order (Z.1 ++ [2,1], Z.2)
      have hob := trunk_endpoint_strict_order (Z.1 ++ [2,2], Z.2)
      rw [lowerStrictGood, hca, hcb]
      simp only [max_lt_iff, lt_min_iff]
      by_cases he : Z.1.length % 2 = 0
      · simp [section14LocalEndpoint, Z, he] at ha hb
        exact ⟨⟨hoa, hb⟩, ⟨ha, hob⟩⟩
      ·
        simp [section14LocalEndpoint, Z, he] at ha hb
        exact ⟨⟨hoa, ha⟩, ⟨hb, hob⟩⟩
    · have hw' : lowerWidth (Z.1 ++ [2]) < lowerWidth Z.2 := lt_of_not_ge hw
      have hn : section14Holds [⟨true, true, lowerHistoryWH ([2], [])⟩]
          (section14R p) (section14S p) (section14Q p) := by
        have hn0 : ¬ section14Holds [⟨false, false, lowerHistoryWH ([2], [])⟩]
            (section14R p) (section14S p) (section14Q p) := by
          intro ht
          apply hw
          have hw0 := (lowerHistory_width_threshold Z ([2], [])).1.mpr (by
            simpa [lowerHistoryAtBase, lowerHistoryConditions, section14Holds,
              section14R, section14S, section14Q, Z] using ht)
          simpa using hw0
        simpa [section14Holds, certBoundHolds] using hn0
      have ha := h2t12 hn
      have hb := h2t21 hn
      have hc : lowerChild p ([2], []) = (Z.1 ++ [2], Z.2) := by
        simp [lowerChild, Z]
      have hca : lowerChild (lowerChild p ([2], [])) ([1], []) =
          (Z.2 ++ [1], Z.1 ++ [2]) := by
        rw [hc]
        simp [lowerChild, lowerNormalize, hw, hw']
      have hcb : lowerChild (lowerChild p ([2], [])) ([2], []) =
          (Z.2 ++ [2], Z.1 ++ [2]) := by
        rw [hc]
        simp [lowerChild, lowerNormalize, hw, hw']
      have hoa := trunk_endpoint_strict_order (Z.2 ++ [1], Z.1 ++ [2])
      have hob := trunk_endpoint_strict_order (Z.2 ++ [2], Z.1 ++ [2])
      rw [lowerStrictGood, hca, hcb]
      simp only [max_lt_iff, lt_min_iff]
      by_cases he : Z.1.length % 2 = 0
      · simp [section14LocalEndpoint, Z, he] at ha hb
        have hx := hcross 2 (Or.inr rfl) (by simpa [Z] using hw')
          (by simpa [Z] using ha) (by simpa [Z] using hb)
        exact ⟨⟨hoa, hx.1⟩, ⟨hx.2, hob⟩⟩
      ·
        simp [section14LocalEndpoint, Z, he] at ha hb
        have hx := hcross 2 (Or.inr rfl) (by simpa [Z] using hw')
          (by simpa [Z] using hb) (by simpa [Z] using ha)
        exact ⟨⟨hoa, hx.1⟩, ⟨hx.2, hob⟩⟩
  have hparent : lowerLocalCoordinate p t ≤ section14LocalEndpoint p ([], []) true :=
    p97_parent_upper t p hs hm hL
  exact p97_selection_core t p hm hn2 h5 hL hp97 hg
    (strictGood_good _ hgood1) (strictGood_good _ hgood2) hparent


-- Source: agents.p97_16.Data
open Freiman
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0

namespace P97Data

private theorem normalized_data (t : ℝ) (p : LowerPair) (hs : lowerState t p)
    (hm : lowerMixed p) (hL : lowerL p) :
    let Z := lowerNormalize p
    CDUnique15.GoodHead Z.1 ∧ CDUnique15.GoodHead Z.2 ∧
    Z.1 ≠ [] ∧ Z.2 ≠ [] ∧ Z.1.length % 2 ≠ Z.2.length % 2 ∧
    lowerEnds Z.1 [3,1] ∧
    lowerWidth (Z.1++[2]) < lowerWidth Z.2 ∧
    lowerWidth (Z.2++[1]) < lowerWidth Z.1 := by
  rcases hs with ⟨had,hgood,_,hbox⟩
  have hh := CDUnique15.admissible_goodHead p had
  have hn1 : p.1 ≠ [] := by
    intro he
    have hx := hbox.1
    rw [he] at hx
    norm_num [lowerRatio,lowerCD] at hx
  have hn2 : p.2 ≠ [] := by
    intro he
    have hx := hbox.2.2.1
    rw [he] at hx
    norm_num [lowerRatio,lowerCD] at hx
  have hf := lower_forced_reflections p hgood hbox
  unfold lowerNormalize
  split_ifs with hw
  · simp [lowerL,lowerNormalize,hw] at hL hf
    exact ⟨hh.1,hh.2,hn1,hn2,hm,hL,hf.1,hf.2.2.2⟩
  · simp [lowerL,lowerNormalize,hw] at hL hf
    exact ⟨hh.2,hh.1,hn2,hn1,Ne.symm hm,hL,hf.1,hf.2.2.2⟩

end P97Data

-- Source: agents.cross16.Critical

open Freiman
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Cross16Critical

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

end Cross16Critical

namespace Cross16Critical

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

end Cross16Critical

namespace Cross16Critical

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

end Cross16Critical

namespace Cross16Critical
private theorem critical_metric {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hdc : d ≤ 2*c) :
    let z := Real.sqrt 3
    let E := 2-z
    let A := (52+z)/73
    let B := (4+z)/13
    let G := (9-z)/13
    let C := (-3*c+4*d)/5
    0 < (A-E)/((c+A*(d-c))*(c+E*(d-c))) +
      (B-G)/((C+B*(2*c-d))*(C+G*(2*c-d))) := by
  dsimp only
  have hz := radical3.1
  have hz0 := radical3.2.1
  have hzlo : (17/10:ℝ) < Real.sqrt 3 := by nlinarith
  have hzhi : Real.sqrt 3 < (18/10:ℝ) := by nlinarith
  have he : 0 ≤ 2-Real.sqrt 3 := by linarith
  have ha : 0 ≤ (52+Real.sqrt 3)/73 := by positivity
  have hb : 0 ≤ (4+Real.sqrt 3)/13 := by positivity
  have hg : 0 ≤ (9-Real.sqrt 3)/13 := by linarith
  have hdc0 : 0 ≤ d-c := by linarith
  have hcd0 : 0 ≤ 2*c-d := by linarith
  have hC : 0 < (-3*c+4*d)/5 := by linarith
  have hden1 : 0 < (c+(52+Real.sqrt 3)/73*(d-c))*(c+(2-Real.sqrt 3)*(d-c)) := by positivity
  have hden2 : 0 < ((-3*c+4*d)/5+(4+Real.sqrt 3)/13*(2*c-d))*
      ((-3*c+4*d)/5+(9-Real.sqrt 3)/13*(2*c-d)) := by positivity
  rw [div_add_div _ _ (ne_of_gt hden1) (ne_of_gt hden2), div_pos_iff]
  left
  constructor
  · have hid :
      ((52+Real.sqrt 3)/73-(2-Real.sqrt 3))*
        (((-3*c+4*d)/5+(4+Real.sqrt 3)/13*(2*c-d))*
         ((-3*c+4*d)/5+(9-Real.sqrt 3)/13*(2*c-d))) +
      ((4+Real.sqrt 3)/13-(9-Real.sqrt 3)/13)*
        ((c+(52+Real.sqrt 3)/73*(d-c))*(c+(2-Real.sqrt 3)*(d-c))) =
      ((216306-116776*Real.sqrt 3)*c^2 +
       (142386*Real.sqrt 3-232166)*c*d +
       (146176*Real.sqrt 3-247881)*d^2)/308425 := by
      linear_combination -(322*c^2*Real.sqrt 3-2493*c^2-348*c*d*Real.sqrt 3+
        1258*c*d+100*d^2*Real.sqrt 3+771*d^2)/12337 * hz
    suffices 0 < ((216306-116776*Real.sqrt 3)*c^2 +
       (142386*Real.sqrt 3-232166)*c*d +
       (146176*Real.sqrt 3-247881)*d^2)/308425 by nlinarith [hid]
    apply div_pos _ (by norm_num)
    have h1 : 0 < (216306-116776*Real.sqrt 3)*c^2 :=
      mul_pos (by linarith) (sq_pos_of_pos hc)
    have h2 : 0 ≤ (142386*Real.sqrt 3-232166)*c*d := by
      apply mul_nonneg (mul_nonneg (by linarith) hc.le) (by linarith)
    have h3 : 0 ≤ (146176*Real.sqrt 3-247881)*d^2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  · exact mul_pos hden1 hden2
end Cross16Critical
namespace Cross16Critical

private theorem critical_tie_delta (U v : List ℕ+)
    (hU : CDUnique15.GoodHead U) (hv : CDUnique15.GoodHead v)
    (hnU : U ≠ []) (hnv : v ≠ [])
    (hp : U.length%2=v.length%2)
    (ht : lowerWidth (U++[1])=lowerWidth (v++[2])) :
    let z := Real.sqrt 3
    let delta := prefixEval U ((52+z)/73) - prefixEval U (2-z) +
      (prefixEval v ((4+z)/13)-prefixEval v ((9-z)/13))
    if U.length%2=0 then 0 < delta else delta < 0 := by
  dsimp only
  have hgu := CDUnique15.goodHead_append U [1] hU hnU
  have hgv := CDUnique15.goodHead_append v [2] hv hnv
  have hh :
      5*((lowerCD (v++[2])).1:ℝ) = -3*((lowerCD (U++[1])).1:ℝ)+4*(lowerCD (U++[1])).2 ∧
      5*((lowerCD (v++[2])).2:ℝ) = 4*((lowerCD (U++[1])).1:ℝ)+3*(lowerCD (U++[1])).2 := by
    rcases cd_classify (U++[1]) (v++[2]) ht with he | he
    · have heq := CDUnique15.injective _ _ hgu hgv he
      have heLast := congrArg List.getLast? heq
      simp at heLast
    · exact he
  rw [cd_append_one,cd_append_two] at hh
  simp only [Prod.fst,Prod.snd] at hh
  push_cast at hh
  let c : ℝ := (lowerCD U).2
  let d : ℝ := (lowerCD U).1+(lowerCD U).2
  have hc : 0 < c := q_pos U
  have hcd : c ≤ d := by
    have hh : (0:ℝ) ≤ (lowerCD U).1 := by positivity
    dsimp [c,d]; linarith
  have hdc : d ≤ 2*c := by
    have hr := cd_fst_le_snd U
    have hr' : ((lowerCD U).1:ℝ) ≤ (lowerCD U).2 := by exact_mod_cast hr
    dsimp [c,d]; linarith
  have heU : ((lowerCD U).1:ℝ)=d-c := by dsimp [c,d]; ring
  have heV1 : ((lowerCD v).1:ℝ)=2*c-d := by dsimp [c,d]; linarith [hh.1,hh.2]
  have heV2 : ((lowerCD v).2:ℝ)=(-3*c+4*d)/5 := by dsimp [c,d]; linarith [hh.1]
  have hz0 := radical3.2.1
  have hzhi := radical3.2.2
  have hA : 0 ≤ (52+Real.sqrt 3)/73 := by positivity
  have hE : 0 ≤ 2-Real.sqrt 3 := by linarith
  have hB : 0 ≤ (4+Real.sqrt 3)/13 := by positivity
  have hG : 0 ≤ (9-Real.sqrt 3)/13 := by linarith
  have hu := pe_signed_difference U ((52+Real.sqrt 3)/73) (2-Real.sqrt 3) hA hE
  have hvd := pe_signed_difference v ((4+Real.sqrt 3)/13) ((9-Real.sqrt 3)/13) hB hG
  rw [heU] at hu
  change prefixEval U ((52+Real.sqrt 3)/73)-prefixEval U (2-Real.sqrt 3) =
    _ / ((c+((52+Real.sqrt 3)/73)*(d-c))*(c+(2-Real.sqrt 3)*(d-c))) at hu
  rw [heV1,heV2] at hvd
  have hm := critical_metric hc hcd hdc
  dsimp only at hm
  rw [neg_one_pow_eq_pow_mod_two] at hu hvd
  rw [← hp] at hvd
  rw [hu,hvd]
  split_ifs with hp0
  · simpa only [hp0,pow_zero,mul_one] using hm
  · have hp1 : U.length%2=1 := by omega
    simp only [hp1,pow_one,mul_neg_one]
    have hh := neg_lt_zero.mpr hm
    convert hh using 1 <;> ring
end Cross16Critical

namespace Cross16Critical

private theorem critical_width_order (U v : List ℕ+)
    (hU : CDUnique15.GoodHead U) (hv : CDUnique15.GoodHead v)
    (hnU : U ≠ []) (hnv : v ≠ [])
    (ht : lowerWidth (U++[1])=lowerWidth (v++[2])) :
    lowerWidth (v++[1]) < lowerWidth U ∧ lowerWidth (v++[2]) < lowerWidth U := by
  have hgu := CDUnique15.goodHead_append U [1] hU hnU
  have hgv := CDUnique15.goodHead_append v [2] hv hnv
  have hh :
      5*((lowerCD (v++[2])).1:ℝ) = -3*((lowerCD (U++[1])).1:ℝ)+4*(lowerCD (U++[1])).2 ∧
      5*((lowerCD (v++[2])).2:ℝ) = 4*((lowerCD (U++[1])).1:ℝ)+3*(lowerCD (U++[1])).2 := by
    rcases cd_classify (U++[1]) (v++[2]) ht with he | he
    · have heq := CDUnique15.injective _ _ hgu hgv he
      have heLast := congrArg List.getLast? heq
      simp at heLast
    · exact he
  rw [cd_append_one,cd_append_two] at hh
  simp only [Prod.fst,Prod.snd] at hh
  push_cast at hh
  let c : ℝ := (lowerCD U).2
  let d : ℝ := (lowerCD U).1+(lowerCD U).2
  have hc : 0 < c := q_pos U
  have hcd : c ≤ d := by
    have hh : (0:ℝ) ≤ (lowerCD U).1 := by positivity
    dsimp [c,d]; linarith
  have hdc : d ≤ 2*c := by
    have hr := cd_fst_le_snd U
    have hr' : ((lowerCD U).1:ℝ) ≤ (lowerCD U).2 := by exact_mod_cast hr
    dsimp [c,d]; linarith
  have heU : ((lowerCD U).1:ℝ)=d-c := by dsimp [c,d]; ring
  have heV1 : ((lowerCD v).1:ℝ)=2*c-d := by dsimp [c,d]; linarith [hh.1,hh.2]
  have heV2 : ((lowerCD v).2:ℝ)=(-3*c+4*d)/5 := by dsimp [c,d]; linarith [hh.1]
  have hDC : 0 < 2*c-d := by
    have hh := CDUnique15.cd_strict U hU
    have hh' : ((lowerCD U).1:ℝ) < (lowerCD U).2 := by exact_mod_cast hh
    dsimp [c,d]; linarith
  have hd : 0 < d := lt_of_lt_of_le hc hcd
  have hz := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 21)
  have hz0 := Real.sqrt_nonneg (21:ℝ)
  have hzlo : 4 < Real.sqrt (21:ℝ) := by nlinarith
  have hzhi : Real.sqrt (21:ℝ) < 5 := by nlinarith
  have hapos := tails.1.1
  have hbpos := tails.2.1.1
  have hnum := sub_pos.mpr tails.2.2
  have hdenU : 0 < (((lowerCD U).1:ℝ)*lowerAlpha+(lowerCD U).2)*
      (((lowerCD U).1:ℝ)*lowerBeta+(lowerCD U).2) := by
    have hq := q_pos U
    positivity
  constructor
  · rw [width_formula,width_formula]
    apply div_lt_div_of_pos_left hnum hdenU
    rw [cd_append_one]
    simp only [Prod.fst,Prod.snd,Nat.cast_add]
    rw [heV1,heV2,heU]
    change ((d-c)*lowerAlpha+c)*((d-c)*lowerBeta+c) < _
    have hid :
        (((-3*c+4*d)/5*lowerAlpha+(2*c-d)+(-3*c+4*d)/5)*
         ((-3*c+4*d)/5*lowerBeta+(2*c-d)+(-3*c+4*d)/5)) -
        (((d-c)*lowerAlpha+c)*((d-c)*lowerBeta+c)) =
        (2*c-d)*(32*c*Real.sqrt 21-72*c-11*d*Real.sqrt 21+81*d)/150 := by
      dsimp [lowerAlpha,lowerBeta]
      linear_combination (-((2*c-d)*(8*c-9*d))/300)*hz
    have hfac : 0 < 32*c*Real.sqrt 21-72*c-11*d*Real.sqrt 21+81*d := by
      have h1 : 0 < (32*Real.sqrt 21-72)*c := mul_pos (by linarith) hc
      have h2 : 0 < (81-11*Real.sqrt 21)*d := mul_pos (by linarith) hd
      nlinarith
    have hpos := div_pos (mul_pos hDC hfac) (by norm_num : (0:ℝ)<150)
    nlinarith [hid]
  · rw [← ht,width_formula,width_formula]
    apply div_lt_div_of_pos_left hnum hdenU
    rw [cd_append_one]
    simp only [Prod.fst,Prod.snd,Nat.cast_add]
    have hq := q_pos U
    have hc0 : (0:ℝ) ≤ (lowerCD U).1 := by positivity
    have ha0 := tails.1.1
    have hb0 := tails.2.1.1
    have ha1 := tails.1.2
    have hb1 := tails.2.1.2
    have hg : ((lowerCD U).1:ℝ) < (lowerCD U).2 := by
      exact_mod_cast CDUnique15.cd_strict U hU
    have hcp : (0:ℝ) < (lowerCD U).1 := by exact_mod_cast CDUnique15.fst_pos U hnU
    have hA : ((lowerCD U).1:ℝ)*lowerAlpha+(lowerCD U).2 <
        ((lowerCD U).2:ℝ)*lowerAlpha+((lowerCD U).1+(lowerCD U).2) := by nlinarith
    have hB : ((lowerCD U).1:ℝ)*lowerBeta+(lowerCD U).2 <
        ((lowerCD U).2:ℝ)*lowerBeta+((lowerCD U).1+(lowerCD U).2) := by nlinarith
    apply mul_lt_mul hA hB.le
    · positivity
    · positivity
end Cross16Critical
namespace Cross16Critical
private theorem critical_tails :
    prefixEval [1,2,1,3] lowerTau = (52+Real.sqrt 3)/73 ∧
    prefixEval [2,3] lowerTau = (4+Real.sqrt 3)/13 ∧
    prefixEval [1,1,3] lowerTau = (9-Real.sqrt 3)/13 := by
  have hz := radical3.1
  have hp := radical3.2.1
  have hh := radical3.2.2
  have hF : prefixEval [1,2,1,3] lowerTau = 1/(1+prefixEval [2,1,3] lowerTau) := by norm_num [prefixEval]
  have hG : prefixEval [1,1,3] lowerTau = 1/(1+1/(1+prefixEval [3] lowerTau)) := by norm_num [prefixEval]
  constructor
  · rw [hF,endpoint_tails.2.1]
    rw [div_eq_iff (show 1+(15-Real.sqrt 3)/37 ≠ 0 by linarith)]
    field_simp
    nlinarith [hz]
  constructor
  · change 1 / (2 + prefixEval [3] lowerTau) = _
    rw [endpoint_tails.1]
    rw [div_eq_iff (show 2+(2-Real.sqrt 3) ≠ 0 by linarith)]
    field_simp
    nlinarith [hz]
  · rw [hG,endpoint_tails.1]
    have hi : (1:ℝ)/(1+(2-Real.sqrt 3))=(3+Real.sqrt 3)/6 := by
      field_simp [show 1+(2-Real.sqrt 3) ≠ 0 by linarith]
      nlinarith [hz]
    rw [hi]
    rw [div_eq_iff (show 1+(3+Real.sqrt 3)/6 ≠ 0 by linarith)]
    field_simp
    nlinarith [hz]

private theorem critical_tie_cross (U v : List ℕ+)
    (hU : CDUnique15.GoodHead U) (hv : CDUnique15.GoodHead v)
    (hnU : U ≠ []) (hnv : v ≠ [])
    (hp : U.length%2=v.length%2)
    (hshort : ¬ lowerEnds U [3,1])
    (ht : lowerWidth (U++[1])=lowerWidth (v++[2])) :
    if U.length%2=0 then
      lowerEndpoint (v++[1],U) false < lowerEndpoint (v++[2],U) true
    else lowerEndpoint (v++[2],U) false < lowerEndpoint (v++[1],U) true := by
  have hw := critical_width_order U v hU hv hnU hnv ht
  have hd := critical_tie_delta U v hU hv hnU hnv hp ht
  dsimp only at hd
  have hns := low_not_short (U++[1]) (v++[2])
    (CDUnique15.goodHead_append _ _ hU hnU) (CDUnique15.goodHead_append _ _ hv hnv)
    ⟨U,rfl⟩ ⟨v,rfl⟩ ht
  have hmix1 : (v++[1]).length%2 ≠ U.length%2 := by simp; omega
  have hmix2 : (v++[2]).length%2 ≠ U.length%2 := by simp; omega
  have hv1 : ¬ lowerWidth U ≤ lowerWidth (v++[1]) := not_le_of_gt hw.1
  have hv2 : ¬ lowerWidth U ≤ lowerWidth (v++[2]) := not_le_of_gt hw.2
  have hshortv : ¬ lowerEnds (v++[1]) [3] := by
    simp [lowerEnds, ← List.reverse_prefix]
  rcases Nat.mod_two_eq_zero_or_one U.length with hU0 | hU1
  · have hv0 : v.length%2=0 := hp ▸ hU0
    have hxp : (U++[1]).length%2=1 := by simp [hU0,Nat.add_mod]
    have hyp : (v++[2]).length%2=1 := by simp [hv0,Nat.add_mod]
    have hh := low_words_upper U v hxp hyp hns ht
    simp only [hU0,if_true] at hd ⊢
    have hA : lowerEndpoint (v++[1],U) false =
        4+prefixEval (v++[1,1,3]) lowerTau+prefixEval (U++[3]) lowerTau := by
      unfold lowerEndpoint lowerEndpointWords
      simp only [Prod.fst,Prod.snd,if_neg hmix1,hv1,if_false,hU0,decide_true,
        Bool.false_eq_true,if_false]
      simp [lowerNaturalWords,lowerNaturalShort,lowerEndpointSuffix,hU0,hv0,
        Nat.add_mod,hshort,hshortv,List.append_assoc]
    have hB : lowerEndpoint (v++[2],U) true =
        4+prefixEval (v++[2,3]) lowerTau+prefixEval (U++[1,2,1,3]) lowerTau := by
      unfold lowerEndpoint lowerEndpointWords
      simp only [Prod.fst,Prod.snd,if_neg hmix2,hv2,if_false,hU0,decide_true,if_true]
      rw [← show lowerEndpointWords (v++[2],U++[1]) true = lowerEqualWords (v++[2],U++[1]) true by
        unfold lowerEndpointWords
        rw [if_pos (hyp.trans hxp.symm)]]
      rw [hh.2]
      simp [List.append_assoc, Nat.add_mod, hU0, hv0]
    rw [hA,hB]
    rw [pe_append v [1,1,3],pe_append U [3],pe_append v [2,3],pe_append U [1,2,1,3]]
    rw [endpoint_tails.1,critical_tails.1,critical_tails.2.1,critical_tails.2.2]
    linarith
  · have hv1p : v.length%2=1 := hp ▸ hU1
    have hxp : (U++[1]).length%2=0 := by simp [hU1,Nat.add_mod]
    have hyp : (v++[2]).length%2=0 := by simp [hv1p,Nat.add_mod]
    have hh := low_words_lower U v hxp hyp hns ht
    have hU0 : ¬ U.length%2=0 := by omega
    simp only [hU0,if_false] at hd ⊢
    have hA : lowerEndpoint (v++[1],U) true =
        4+prefixEval (v++[1,1,3]) lowerTau+prefixEval (U++[3]) lowerTau := by
      unfold lowerEndpoint lowerEndpointWords
      simp only [Prod.fst,Prod.snd,if_neg hmix1,hv1,if_false,hU0,decide_false,
        Bool.true_eq_false,if_false]
      simp [lowerNaturalWords,lowerNaturalShort,lowerEndpointSuffix,hU1,hv1p,
        Nat.add_mod,hshort,hshortv,List.append_assoc]
    have hB : lowerEndpoint (v++[2],U) false =
        4+prefixEval (v++[2,3]) lowerTau+prefixEval (U++[1,2,1,3]) lowerTau := by
      unfold lowerEndpoint lowerEndpointWords
      simp only [Prod.fst,Prod.snd,if_neg hmix2,hv2,if_false,hU0,decide_false,if_true]
      rw [← show lowerEndpointWords (v++[2],U++[1]) false = lowerEqualWords (v++[2],U++[1]) false by
        unfold lowerEndpointWords
        rw [if_pos (hyp.trans hxp.symm)]]
      rw [hh.2]
      simp [List.append_assoc, Nat.add_mod, hU1, hv1p]
    rw [hA,hB]
    rw [pe_append v [1,1,3],pe_append U [3],pe_append v [2,3],pe_append U [1,2,1,3]]
    rw [endpoint_tails.1,critical_tails.1,critical_tails.2.1,critical_tails.2.2]
    linarith
end Cross16Critical
namespace Cross16Critical

private theorem low_tie_not_short (u v : List ℕ+)
    (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hu1 : lowerEnds u [1]) (hv2 : lowerEnds v [2])
    (hw : lowerWidth u = lowerWidth v) : ¬ lowerEnds u [3,1] :=
  low_not_short u v hu hv hu1 hv2 hw
end Cross16Critical

-- Source: agents.p97_16.ChildNontie
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

-- Source: agents.cross16.One
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

-- Source: agents.long16.Complement

open Freiman
set_option maxHeartbeats 0

namespace Long16Complement

private theorem mixed_other_swap (a b : List ℕ+) (upper : Bool)
    (hp : a.length % 2 ≠ b.length % 2)
    (hwide : lowerWidth b < lowerWidth a)
    (hu : upper ≠ decide (a.length % 2 = 0)) :
    lowerEndpoint (b,a) upper = lowerEndpoint (a,b) upper := by
  unfold lowerEndpoint lowerEndpointWords
  have hp' : b.length % 2 ≠ a.length % 2 := Ne.symm hp
  have hn : ¬ lowerWidth a ≤ lowerWidth b := not_le_of_gt hwide
  simp only [if_neg hp,if_neg hp',hwide.le,hn,if_true,if_false,hu,lowerNaturalWords]
  ring

private theorem critical_tie_complement (u v : List ℕ+)
    (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ []) (hp : u.length%2 ≠ v.length%2)
    (hwu : lowerWidth (u++[1]) < lowerWidth v)
    (hwv : lowerWidth (v++[1]) < lowerWidth u)
    (ht : lowerWidth ((u++[1])++[1]) = lowerWidth (v++[2]))
    (hraw : if (u++[1]).length%2=0 then
      lowerEndpoint (u++[1],v++[2]) false < lowerEndpoint (u++[1],v++[1]) true
    else lowerEndpoint (u++[1],v++[1]) false < lowerEndpoint (u++[1],v++[2]) true) :
    if (u++[1]).length%2=0 then
      lowerEndpoint (v++[2],u++[1]) false < lowerEndpoint (v++[1],u++[1]) true
    else lowerEndpoint (v++[1],u++[1]) false < lowerEndpoint (v++[2],u++[1]) true := by
  have hn := Cross16.one_nonties u v hu hv hnu hnv hp hwu hwv
  have hs (upper : Bool) := lowerEarlyTerminal_endpoint_swap_nontie
    (u++[1],v++[1]) hn upper
  have hwidth := Cross16Critical.critical_width_order (u++[1]) v
    (CDUnique15.goodHead_append _ _ hu hnu) hv (by simp) hnv ht
  have hpar : (u++[1]).length%2 ≠ (v++[2]).length%2 := by simp; omega
  rcases Nat.mod_two_eq_zero_or_one (u++[1]).length with h0 | h1
  · simp only [if_pos h0] at hraw ⊢
    have h0' : (u.length+1)%2=0 := by simpa using h0
    have ha := mixed_other_swap (u++[1]) (v++[2]) false hpar hwidth.2 (by simp [h0'])
    exact ha.trans_lt (hraw.trans_eq (hs true))
  · have h0 : ¬(u++[1]).length%2=0 := by omega
    simp only [if_neg h0] at hraw ⊢
    have h1' : (u.length+1)%2=1 := by simpa using h1
    have ha := mixed_other_swap (u++[1]) (v++[2]) true hpar hwidth.2 (by simp [h1'])
    exact (hs false).symm ▸ (hraw.trans_eq ha.symm)

end Long16Complement


-- Source: agents.p97_16.DirectWords
open Freiman
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace P97Direct

private theorem direct_words_even_true (u v : List ℕ+)
    (hu : u.length%2=1) (hv : v.length%2=0)
    (ht : lowerWidth (u++[2])=lowerWidth (v++[1]))
    (hU1 : lowerWidth ((u++[2])++[1]) < lowerWidth (v++[1]))
    (hshortV : ¬ lowerEnds (v++[1]) [3,1])
    (hthr : (7/5:ℝ)*lowerWidth ((u++[2])++[1,3]) < lowerWidth ((v++[1])++[3])) :
    lowerEndpointWords (u++[2],v++[1]) true =
      ((lowerEndpointWords (v++[1],u++[2]) true).2,
       (lowerEndpointWords (v++[1],u++[2]) true).1) := by
  have hp : (u++[2]).length%2 ≠ (v++[1]).length%2 := by simp; omega
  unfold lowerEndpointWords
  rw [if_neg hp,if_neg hp.symm]
  have hw : lowerWidth (v++[1]) ≤ lowerWidth (u++[2]) := ht.ge
  have hw' : lowerWidth (u++[2]) ≤ lowerWidth (v++[1]) := ht.le
  simp only [hw,hw',if_true]
  have hpu : (u++[2]).length%2=0 := by simp; omega
  have hpv : (v++[1]).length%2=1 := by simp; omega
  simp only [hpu,hpv,decide_true,decide_false,if_true,if_false]
  norm_num
  unfold lowerEqualWords
  have hU1' : lowerWidth (u++[2,1]) < lowerWidth (v++[1]) := by
    simpa using hU1
  have hn : lowerNormalize (u++[2,1],v++[1])=(v++[1],u++[2,1]) := by
    simp [lowerNormalize,not_le_of_gt hU1']
  rw [hn]
  simp only [Prod.fst,Prod.snd]
  have hnV3 : ¬ lowerEnds (v++[1]) [3] := by
    simp [lowerEnds, ← List.reverse_prefix]
  have hnU31 : ¬ lowerEnds (u++[2,1]) [3,1] := by
    simp [lowerEnds, ← List.reverse_prefix]
  have hnU3 : ¬ lowerEnds (u++[2,1]) [3] := by
    simp [lowerEnds, ← List.reverse_prefix]
  have hnU2_3 : ¬ lowerEnds (u++[2]) [3] := by
    simp [lowerEnds, ← List.reverse_prefix]
  have hsV : lowerNaturalShort (v++[1]) true = false := by
    simp [lowerNaturalShort,hpv,hshortV,hnV3]
  have hsU : lowerNaturalShort (u++[2,1]) true = false := by
    simp [lowerNaturalShort,hu,hnU31,hnU3]
  rw [hsV,hsU]
  simp only [Bool.not_false,Bool.true_and,decide_eq_false_iff_not]
  have hnot : ¬ lowerWidth (v++[1,3]) ≤
      (7/5:ℝ)*lowerWidth (u++[2,1,3]) := by
    simpa using not_le_of_gt hthr
  simp only [hpv,show ¬ (1:ℕ)=0 by omega,decide_false,if_false,List.append_assoc]
  norm_num
  simp only [hnot,decide_false]
  simp only [not_le_of_gt hU1',if_false]
  unfold lowerNaturalWords
  simp only [Prod.fst,Prod.snd]
  apply Prod.ext
  · have hulen : (u.length+1)%2=0 := by omega
    simp [lowerNaturalShort,lowerEndpointSuffix,hu,hulen,hnU31,hnU3,hnU2_3,List.append_assoc]
  · have hvlen : (v.length+1)%2=1 := by omega
    have hvnot : ¬ [3] <+: v.reverse := by
      simpa [lowerEnds,← List.reverse_prefix] using hshortV
    simp [lowerNaturalShort,lowerEndpointSuffix,hvlen,hvnot,List.append_assoc]
    exact hshortV


private theorem direct_words_odd_false (u v : List ℕ+)
    (hu : u.length%2=0) (hv : v.length%2=1)
    (ht : lowerWidth (u++[2])=lowerWidth (v++[1]))
    (hU1 : lowerWidth ((u++[2])++[1]) < lowerWidth (v++[1]))
    (hshortV : ¬ lowerEnds (v++[1]) [3,1])
    (hthr : (7/5:ℝ)*lowerWidth ((u++[2])++[1,3]) < lowerWidth ((v++[1])++[3])) :
    lowerEndpointWords (u++[2],v++[1]) false =
      ((lowerEndpointWords (v++[1],u++[2]) false).2,
       (lowerEndpointWords (v++[1],u++[2]) false).1) := by
  have hp : (u++[2]).length%2 ≠ (v++[1]).length%2 := by simp; omega
  unfold lowerEndpointWords
  rw [if_neg hp,if_neg hp.symm]
  have hw : lowerWidth (v++[1]) ≤ lowerWidth (u++[2]) := ht.ge
  have hw' : lowerWidth (u++[2]) ≤ lowerWidth (v++[1]) := ht.le
  simp only [hw,hw',if_true]
  have hpu : (u++[2]).length%2=1 := by simp; omega
  have hpv : (v++[1]).length%2=0 := by simp; omega
  simp only [hpu,hpv,decide_true,decide_false,if_true,if_false]
  norm_num
  unfold lowerEqualWords
  have hU1' : lowerWidth (u++[2,1]) < lowerWidth (v++[1]) := by
    simpa using hU1
  have hn : lowerNormalize (u++[2,1],v++[1])=(v++[1],u++[2,1]) := by
    simp [lowerNormalize,not_le_of_gt hU1']
  rw [hn]
  simp only [Prod.fst,Prod.snd]
  have hnV3 : ¬ lowerEnds (v++[1]) [3] := by
    simp [lowerEnds, ← List.reverse_prefix]
  have hnU31 : ¬ lowerEnds (u++[2,1]) [3,1] := by
    simp [lowerEnds, ← List.reverse_prefix]
  have hnU3 : ¬ lowerEnds (u++[2,1]) [3] := by
    simp [lowerEnds, ← List.reverse_prefix]
  have hnU2_3 : ¬ lowerEnds (u++[2]) [3] := by
    simp [lowerEnds, ← List.reverse_prefix]
  have hsV : lowerNaturalShort (v++[1]) false = false := by
    simp [lowerNaturalShort,hpv,hshortV,hnV3]
  have hsU : lowerNaturalShort (u++[2,1]) false = false := by
    simp [lowerNaturalShort,hu,hnU31,hnU3]
  rw [hsV,hsU]
  simp only [Bool.not_false,Bool.true_and,decide_eq_false_iff_not]
  have hnot : ¬ lowerWidth (v++[1,3]) ≤
      (7/5:ℝ)*lowerWidth (u++[2,1,3]) := by
    simpa using not_le_of_gt hthr
  simp only [hpv,show ¬ (1:ℕ)=0 by omega,decide_false,if_false,List.append_assoc]
  norm_num
  simp only [hnot,decide_false]
  simp only [not_le_of_gt hU1',if_false]
  unfold lowerNaturalWords
  simp only [Prod.fst,Prod.snd]
  apply Prod.ext
  · have hulen : (u.length+1)%2=1 := by omega
    simp [lowerNaturalShort,lowerEndpointSuffix,hu,hulen,hnU31,hnU3,hnU2_3,List.append_assoc]
  · have hvlen : (v.length+1)%2=0 := by omega
    have hvnot : ¬ [3] <+: v.reverse := by
      simpa [lowerEnds,← List.reverse_prefix] using hshortV
    simp [lowerNaturalShort,lowerEndpointSuffix,hvlen,hvnot,List.append_assoc]
    exact hshortV

end P97Direct

-- Source: agents.cross16.DirectOther
open Freiman
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Cross16DirectOther

private theorem one_two_even_true (u v : List ℕ+)
    (hu : u.length%2=1) (hv : v.length%2=0)
    (ht : lowerWidth (u++[1])=lowerWidth (v++[2]))
    (hU1 : lowerWidth ((u++[1])++[1]) < lowerWidth (v++[2]))
    (hthr : (7/5:ℝ)*lowerWidth ((u++[1])++[1,3]) < lowerWidth ((v++[2])++[3])) :
    lowerEndpointWords (u++[1],v++[2]) true =
      ((lowerEndpointWords (v++[2],u++[1]) true).2,
       (lowerEndpointWords (v++[2],u++[1]) true).1) := by
  have hshortV : ¬ lowerEnds (v++[2]) [3,1] := by simp [lowerEnds, ← List.reverse_prefix]
  have hp : (u++[1]).length%2 ≠ (v++[2]).length%2 := by simp; omega
  unfold lowerEndpointWords
  rw [if_neg hp,if_neg hp.symm]
  have hw : lowerWidth (v++[2]) ≤ lowerWidth (u++[1]) := ht.ge
  have hw' : lowerWidth (u++[1]) ≤ lowerWidth (v++[2]) := ht.le
  simp only [hw,hw',if_true]
  have hpu : (u++[1]).length%2=0 := by simp; omega
  have hpv : (v++[2]).length%2=1 := by simp; omega
  simp only [hpu,hpv,decide_true,decide_false,if_true,if_false]
  norm_num
  unfold lowerEqualWords
  have hU1' : lowerWidth (u++[1,1]) < lowerWidth (v++[2]) := by
    simpa using hU1
  have hn : lowerNormalize (u++[1,1],v++[2])=(v++[2],u++[1,1]) := by
    simp [lowerNormalize,not_le_of_gt hU1']
  rw [hn]
  simp only [Prod.fst,Prod.snd]
  have hnV3 : ¬ lowerEnds (v++[2]) [3] := by
    simp [lowerEnds, ← List.reverse_prefix]
  have hnU31 : ¬ lowerEnds (u++[1,1]) [3,1] := by
    simp [lowerEnds, ← List.reverse_prefix]
  have hnU3 : ¬ lowerEnds (u++[1,1]) [3] := by
    simp [lowerEnds, ← List.reverse_prefix]
  have hnU2_3 : ¬ lowerEnds (u++[1]) [3] := by
    simp [lowerEnds, ← List.reverse_prefix]
  have hsV : lowerNaturalShort (v++[2]) true = false := by
    simp [lowerNaturalShort,hpv,hshortV,hnV3]
  have hsU : lowerNaturalShort (u++[1,1]) true = false := by
    simp [lowerNaturalShort,hu,hnU31,hnU3]
  rw [hsV,hsU]
  simp only [Bool.not_false,Bool.true_and,decide_eq_false_iff_not]
  have hnot : ¬ lowerWidth (v++[2,3]) ≤
      (7/5:ℝ)*lowerWidth (u++[1,1,3]) := by
    simpa using not_le_of_gt hthr
  simp only [hpv,show ¬ (1:ℕ)=0 by omega,decide_false,if_false,List.append_assoc]
  norm_num
  simp only [hnot,decide_false]
  simp only [not_le_of_gt hU1',if_false]
  unfold lowerNaturalWords
  simp only [Prod.fst,Prod.snd]
  apply Prod.ext
  · have hulen : (u.length+1)%2=0 := by omega
    simp [lowerNaturalShort,lowerEndpointSuffix,hu,hulen,hnU31,hnU3,hnU2_3,List.append_assoc]
  · have hvlen : (v.length+1)%2=1 := by omega
    simp [lowerNaturalShort,lowerEndpointSuffix,hvlen,lowerEnds,← List.reverse_prefix,List.append_assoc]


private theorem one_two_odd_false (u v : List ℕ+)
    (hu : u.length%2=0) (hv : v.length%2=1)
    (ht : lowerWidth (u++[1])=lowerWidth (v++[2]))
    (hU1 : lowerWidth ((u++[1])++[1]) < lowerWidth (v++[2]))
    (hthr : (7/5:ℝ)*lowerWidth ((u++[1])++[1,3]) < lowerWidth ((v++[2])++[3])) :
    lowerEndpointWords (u++[1],v++[2]) false =
      ((lowerEndpointWords (v++[2],u++[1]) false).2,
       (lowerEndpointWords (v++[2],u++[1]) false).1) := by
  have hshortV : ¬ lowerEnds (v++[2]) [3,1] := by simp [lowerEnds, ← List.reverse_prefix]
  have hp : (u++[1]).length%2 ≠ (v++[2]).length%2 := by simp; omega
  unfold lowerEndpointWords
  rw [if_neg hp,if_neg hp.symm]
  have hw : lowerWidth (v++[2]) ≤ lowerWidth (u++[1]) := ht.ge
  have hw' : lowerWidth (u++[1]) ≤ lowerWidth (v++[2]) := ht.le
  simp only [hw,hw',if_true]
  have hpu : (u++[1]).length%2=1 := by simp; omega
  have hpv : (v++[2]).length%2=0 := by simp; omega
  simp only [hpu,hpv,decide_true,decide_false,if_true,if_false]
  norm_num
  unfold lowerEqualWords
  have hU1' : lowerWidth (u++[1,1]) < lowerWidth (v++[2]) := by
    simpa using hU1
  have hn : lowerNormalize (u++[1,1],v++[2])=(v++[2],u++[1,1]) := by
    simp [lowerNormalize,not_le_of_gt hU1']
  rw [hn]
  simp only [Prod.fst,Prod.snd]
  have hnV3 : ¬ lowerEnds (v++[2]) [3] := by
    simp [lowerEnds, ← List.reverse_prefix]
  have hnU31 : ¬ lowerEnds (u++[1,1]) [3,1] := by
    simp [lowerEnds, ← List.reverse_prefix]
  have hnU3 : ¬ lowerEnds (u++[1,1]) [3] := by
    simp [lowerEnds, ← List.reverse_prefix]
  have hnU2_3 : ¬ lowerEnds (u++[1]) [3] := by
    simp [lowerEnds, ← List.reverse_prefix]
  have hsV : lowerNaturalShort (v++[2]) false = false := by
    simp [lowerNaturalShort,hpv,hshortV,hnV3]
  have hsU : lowerNaturalShort (u++[1,1]) false = false := by
    simp [lowerNaturalShort,hu,hnU31,hnU3]
  rw [hsV,hsU]
  simp only [Bool.not_false,Bool.true_and,decide_eq_false_iff_not]
  have hnot : ¬ lowerWidth (v++[2,3]) ≤
      (7/5:ℝ)*lowerWidth (u++[1,1,3]) := by
    simpa using not_le_of_gt hthr
  simp only [hpv,show ¬ (1:ℕ)=0 by omega,decide_false,if_false,List.append_assoc]
  norm_num
  simp only [hnot,decide_false]
  simp only [not_le_of_gt hU1',if_false]
  unfold lowerNaturalWords
  simp only [Prod.fst,Prod.snd]
  apply Prod.ext
  · have hulen : (u.length+1)%2=1 := by omega
    simp [lowerNaturalShort,lowerEndpointSuffix,hu,hulen,hnU31,hnU3,hnU2_3,List.append_assoc]
  · have hvlen : (v.length+1)%2=0 := by omega
    simp [lowerNaturalShort,lowerEndpointSuffix,hvlen,lowerEnds,← List.reverse_prefix,List.append_assoc]

end Cross16DirectOther

-- Source: agents.cross16.Bounds

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


-- Source: agents.p97_16.DirectComplete
open Freiman
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0
namespace P97Direct

private theorem direct_tie_two_one (u v : List ℕ+)
    (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ [])
    (hp : u.length%2 ≠ v.length%2)
    (ht : lowerWidth (u++[2]) = lowerWidth (v++[1])) (upper : Bool) :
    lowerEndpoint (u++[2],v++[1]) upper =
      lowerEndpoint (v++[1],u++[2]) upper := by
  have hshort := Cross16Critical.low_tie_not_short (v++[1]) (u++[2])
    (CDUnique15.goodHead_append _ _ hv hnv) (CDUnique15.goodHead_append _ _ hu hnu)
    ⟨v,rfl⟩ ⟨u,rfl⟩ ht.symm
  have hU1 : lowerWidth ((u++[2])++[1]) < lowerWidth (v++[1]) :=
    (Cross16Bounds.append_one_lt (u++[2])).trans_eq ht
  have hV1 : lowerWidth ((v++[1])++[1]) < lowerWidth (u++[2]) :=
    (Cross16Bounds.append_one_lt (v++[1])).trans_eq ht.symm
  have hthrU := Cross16Bounds.tied_three_threshold (u++[2]) (v++[1]) ht
  have hthrV := Cross16Bounds.tied_three_threshold (v++[1]) (u++[2]) ht.symm
  rcases Nat.mod_two_eq_zero_or_one u.length with hu0 | hu1
  · have hv1 : v.length%2=1 := by omega
    rcases upper with _|_
    · have hw := direct_words_odd_false u v hu0 hv1 ht hU1 hshort hthrU
      unfold lowerEndpoint
      rw [hw]
      ring
    · have hw := Cross16DirectOther.one_two_even_true v u hv1 hu0 ht.symm hV1 hthrV
      unfold lowerEndpoint
      rw [hw]
      ring
  · have hv0 : v.length%2=0 := by omega
    rcases upper with _|_
    · have hw := Cross16DirectOther.one_two_odd_false v u hv0 hu1 ht.symm hV1 hthrV
      unfold lowerEndpoint
      rw [hw]
      ring
    · have hw := direct_words_even_true u v hu1 hv0 ht hU1 hshort hthrU
      unfold lowerEndpoint
      rw [hw]
      ring

end P97Direct

-- Source: agents.long16.D1

open Freiman
set_option maxHeartbeats 0

namespace Long16D1

private theorem one_two_other_virtual_eq (u v : List ℕ+)
    (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ [])
    (ht : lowerWidth (u++[1]) = lowerWidth ((v++[2])++[1])) : u=v++[2] := by
  have hgu := CDUnique15.goodHead_append u [1] hu hnu
  have hgv := CDUnique15.goodHead_append v [2] hv hnv
  have hgvv := CDUnique15.goodHead_append (v++[2]) [1] hgv (by simp)
  have hc := M7TieWidth14.cd_eq_of_width_same_side _ _ ht
    (Or.inl ⟨Cross16.ratio_one_gt_half u hu,Cross16.ratio_one_gt_half (v++[2]) hgv⟩)
  have hsame := CDUnique15.injective _ _ hgu hgvv hc
  exact List.append_cancel_right hsame

private theorem append_one_swap (w : List ℕ+) (upper : Bool) :
    lowerEndpoint (w++[1],w) upper = lowerEndpoint (w,w++[1]) upper := by
  have hlt := Cross16Bounds.append_one_lt w
  unfold lowerEndpoint lowerEndpointWords
  have hp : (w++[1]).length%2 ≠ w.length%2 := by simp; omega
  rw [if_neg hp,if_neg hp.symm]
  have hn := not_le_of_gt hlt
  simp only [hlt.le,hn,if_true,if_false]
  by_cases hu : upper = decide (w.length%2=0)
  · simp only [if_pos hu]
  · simp only [if_neg hu,lowerNaturalWords]; ring

private theorem transfer_one (u v : List ℕ+)
    (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ []) (hp : u.length%2 ≠ v.length%2)
    (heu : lowerEnds u [1])
    (hwu : lowerWidth (u++[1]) < lowerWidth v)
    (hwv : lowerWidth (v++[1]) < lowerWidth u)
    (h12 : lowerEndpoint (u++[1],v++[2]) false <
      lowerEndpoint (u++[1],v++[1]) true)
    (h21 : lowerEndpoint (u++[1],v++[1]) false <
      lowerEndpoint (u++[1],v++[2]) true) :
    lowerEndpoint (v++[2],u++[1]) false <
      lowerEndpoint (v++[1],u++[1]) true ∧
    lowerEndpoint (v++[1],u++[1]) false <
      lowerEndpoint (v++[2],u++[1]) true := by
  have hn1 := Cross16.one_nonties u v hu hv hnu hnv hp hwu hwv
  have hs1 (upper : Bool) := lowerEarlyTerminal_endpoint_swap_nontie
    (u++[1],v++[1]) hn1 upper
  by_cases hd : lowerWidth (u++[1]) = lowerWidth (v++[2])
  · have hs2 (upper : Bool) := P97Direct.direct_tie_two_one v u hv hu hnv hnu hp.symm hd.symm upper
    constructor
    · exact (hs2 false).symm ▸ (h12.trans_eq (hs1 true))
    · exact (hs1 false).symm ▸ (h21.trans_eq (hs2 true).symm)
  · by_cases ht : lowerWidth ((u++[1])++[1]) = lowerWidth (v++[2])
    · have hshort : ¬ lowerEnds (u++[1]) [3,1] := by
        rcases heu with ⟨z,rfl⟩
        simp [lowerEnds,← List.reverse_prefix]
      have hc := Cross16Critical.critical_tie_cross (u++[1]) v
        (CDUnique15.goodHead_append _ _ hu hnu) hv (by simp) hnv
        (by simp; omega) hshort ht
      by_cases he : (u++[1]).length%2=0
      · have he' : (u.length+1)%2=0 := by simpa using he
        have hr : if (u++[1]).length%2=0 then
            lowerEndpoint (u++[1],v++[2]) false < lowerEndpoint (u++[1],v++[1]) true
          else lowerEndpoint (u++[1],v++[1]) false < lowerEndpoint (u++[1],v++[2]) true := by
          simp [he',h12]
        have ho := Long16Complement.critical_tie_complement u v hu hv hnu hnv hp
          hwu hwv ht hr
        simp only [if_pos he] at hc ho
        exact ⟨ho,hc⟩
      · have he' : ¬(u.length+1)%2=0 := by simpa using he
        have hr : if (u++[1]).length%2=0 then
            lowerEndpoint (u++[1],v++[2]) false < lowerEndpoint (u++[1],v++[1]) true
          else lowerEndpoint (u++[1],v++[1]) false < lowerEndpoint (u++[1],v++[2]) true := by
          simp [he',h21]
        have ho := Long16Complement.critical_tie_complement u v hu hv hnu hnv hp
          hwu hwv ht hr
        simp only [if_neg he] at hc ho
        exact ⟨hc,ho⟩
    · have hn2 : LowerEarlyTerminalNoTies (u++[1],v++[2]) := by
        refine ⟨hd,fun _ => ⟨ht,?_⟩⟩
        exact Cross16.one_two_other_virtual_nontie u v hu hv hnu hnv heu
      have hs2 (upper : Bool) := lowerEarlyTerminal_endpoint_swap_nontie
        (u++[1],v++[2]) hn2 upper
      constructor
      · exact (hs2 false).symm ▸ (h12.trans_eq (hs1 true))
      · exact (hs1 false).symm ▸ (h21.trans_eq (hs2 true))

end Long16D1


-- Source: agents.cross16.TwoOne
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

-- Source: agents.cross16.Two

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

-- Source: agents.cross16.TransferTwo
open Freiman
namespace Cross16
set_option maxHeartbeats 0

private theorem transfer_two_core (u v : List ℕ+)
    (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ []) (hp : u.length%2 ≠ v.length%2)
    (heu : lowerEnds u [3,1])
    (hc1 : lowerEndpoint (v++[1],u++[2]) false ≤ lowerEndpoint (u++[2],v++[1]) false ∧
      lowerEndpoint (u++[2],v++[1]) true ≤ lowerEndpoint (v++[1],u++[2]) true)
    (h12 : lowerEndpoint (u++[2],v++[2]) false < lowerEndpoint (u++[2],v++[1]) true)
    (h21 : lowerEndpoint (u++[2],v++[1]) false < lowerEndpoint (u++[2],v++[2]) true) :
    lowerEndpoint (v++[2],u++[2]) false < lowerEndpoint (v++[1],u++[2]) true ∧
    lowerEndpoint (v++[1],u++[2]) false < lowerEndpoint (v++[2],u++[2]) true := by
  have hc := two_complementary_swap u v hu hv hnu hnv hp heu
  have ha := Mixed15.alignment M7LowTies15.lowTieLaw u v hu hv hnu hnv hp
  rcases Nat.mod_two_eq_zero_or_one v.length with hv0 | hv1
  · simp only [if_pos hv0] at ha hc
    exact ⟨ha.trans_lt (h12.trans_le hc1.2), hc1.1.trans_lt (h21.trans_eq hc)⟩
  · simp only [if_neg (by omega : ¬ v.length%2=0)] at ha hc
    exact ⟨hc.symm.le.trans_lt (h12.trans_le hc1.2), hc1.1.trans_lt (h21.trans_le ha)⟩


private theorem transfer_two (u v : List ℕ+)
    (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ []) (hp : u.length%2 ≠ v.length%2)
    (heu : lowerEnds u [3,1])
    (hwu : lowerWidth (u++[2]) < lowerWidth v)
    (h12 : lowerEndpoint (u++[2],v++[2]) false < lowerEndpoint (u++[2],v++[1]) true)
    (h21 : lowerEndpoint (u++[2],v++[1]) false < lowerEndpoint (u++[2],v++[2]) true) :
    lowerEndpoint (v++[2],u++[2]) false < lowerEndpoint (v++[1],u++[2]) true ∧
    lowerEndpoint (v++[1],u++[2]) false < lowerEndpoint (v++[2],u++[2]) true := by
  apply transfer_two_core u v hu hv hnu hnv hp heu _ h12 h21
  by_cases ht : lowerWidth (u++[2])=lowerWidth (v++[1])
  · have hh := P97Direct.direct_tie_two_one u v hu hv hnu hnv hp ht
    exact ⟨(hh false).symm.le,(hh true).le⟩
  · exact Cross16TwoOne.containment_of_ne u v hu hv hnu hnv hp hwu ht
private theorem transfer_two_ratio_core (u v : List ℕ+)
    (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ []) (hp : u.length%2 ≠ v.length%2)
    (heu : (1/4:ℝ) ≤ lowerRatio u)
    (hc1 : lowerEndpoint (v++[1],u++[2]) false ≤ lowerEndpoint (u++[2],v++[1]) false ∧
      lowerEndpoint (u++[2],v++[1]) true ≤ lowerEndpoint (v++[1],u++[2]) true)
    (h12 : lowerEndpoint (u++[2],v++[2]) false < lowerEndpoint (u++[2],v++[1]) true)
    (h21 : lowerEndpoint (u++[2],v++[1]) false < lowerEndpoint (u++[2],v++[2]) true) :
    lowerEndpoint (v++[2],u++[2]) false < lowerEndpoint (v++[1],u++[2]) true ∧
    lowerEndpoint (v++[1],u++[2]) false < lowerEndpoint (v++[2],u++[2]) true := by
  have hc := two_complementary_swap_of_ratio u v hu hv hnu hnv hp heu
  have ha := Mixed15.alignment M7LowTies15.lowTieLaw u v hu hv hnu hnv hp
  rcases Nat.mod_two_eq_zero_or_one v.length with hv0 | hv1
  · simp only [if_pos hv0] at ha hc
    exact ⟨ha.trans_lt (h12.trans_le hc1.2), hc1.1.trans_lt (h21.trans_eq hc)⟩
  · simp only [if_neg (by omega : ¬ v.length%2=0)] at ha hc
    exact ⟨hc.symm.le.trans_lt (h12.trans_le hc1.2), hc1.1.trans_lt (h21.trans_le ha)⟩


private theorem transfer_two_of_ratio (u v : List ℕ+)
    (hu : CDUnique15.GoodHead u) (hv : CDUnique15.GoodHead v)
    (hnu : u ≠ []) (hnv : v ≠ []) (hp : u.length%2 ≠ v.length%2)
    (heu : (1/4:ℝ) ≤ lowerRatio u)
    (hwu : lowerWidth (u++[2]) < lowerWidth v)
    (h12 : lowerEndpoint (u++[2],v++[2]) false < lowerEndpoint (u++[2],v++[1]) true)
    (h21 : lowerEndpoint (u++[2],v++[1]) false < lowerEndpoint (u++[2],v++[2]) true) :
    lowerEndpoint (v++[2],u++[2]) false < lowerEndpoint (v++[1],u++[2]) true ∧
    lowerEndpoint (v++[1],u++[2]) false < lowerEndpoint (v++[2],u++[2]) true := by
  apply transfer_two_ratio_core u v hu hv hnu hnv hp heu _ h12 h21
  by_cases ht : lowerWidth (u++[2])=lowerWidth (v++[1])
  · have hh := P97Direct.direct_tie_two_one u v hu hv hnu hnv hp ht
    exact ⟨(hh false).symm.le,(hh true).le⟩
  · exact Cross16TwoOne.containment_of_ne u v hu hv hnu hnv hp hwu ht
end Cross16


-- Source: agents.p97_16.Final

open Freiman
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem p97_cross (t : ℝ) (p : LowerPair) (hs : lowerState t p)
    (hm : lowerMixed p) (hL : lowerL p) :
    ∀ d : ℕ+, d = 1 ∨ d = 2 →
      lowerWidth ((lowerNormalize p).1++[d]) < lowerWidth (lowerNormalize p).2 →
      lowerEndpoint ((lowerNormalize p).1++[d],(lowerNormalize p).2++[2]) false <
        lowerEndpoint ((lowerNormalize p).1++[d],(lowerNormalize p).2++[1]) true →
      lowerEndpoint ((lowerNormalize p).1++[d],(lowerNormalize p).2++[1]) false <
        lowerEndpoint ((lowerNormalize p).1++[d],(lowerNormalize p).2++[2]) true →
      lowerEndpoint ((lowerNormalize p).2++[2],(lowerNormalize p).1++[d]) false <
        lowerEndpoint ((lowerNormalize p).2++[1],(lowerNormalize p).1++[d]) true ∧
      lowerEndpoint ((lowerNormalize p).2++[1],(lowerNormalize p).1++[d]) false <
        lowerEndpoint ((lowerNormalize p).2++[2],(lowerNormalize p).1++[d]) true := by
  let Z := lowerNormalize p
  have hdta := P97Data.normalized_data t p hs hm hL
  dsimp only at hdta
  rcases hdta with ⟨hgu,hgv,hnu,hnv,hp,he31,hw2,hw1⟩
  intro d hd hwd h12 h21
  rcases hd with rfl | rfl
  · have he1 : lowerEnds Z.1 [1] := by
      rcases he31 with ⟨P,hP⟩
      exact ⟨P++[3],by simpa [List.append_assoc] using hP⟩
    exact Long16D1.transfer_one Z.1 Z.2 hgu hgv hnu hnv hp he1 hwd hw1 h12 h21
  · exact Cross16.transfer_two Z.1 Z.2 hgu hgv hnu hnv hp he31 hwd h12 h21

 private theorem p97_complete (t : ℝ) (p : LowerPair)
    (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : lowerMixed p ∧ ¬ lowerH p 2 ∧ lowerH p 5 ∧ lowerL p)
    (hg : section14RawGeometry p) : lowerNumericSuccessor t p := by
  exact Freiman.section14_select_p97_of_cross t p hs hb hp97 hlate hc hg
    (p97_cross t p hs hc.1 hc.2.2.2)


theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : lowerMixed p ∧ ¬ lowerH p 2 ∧ lowerH p 5 ∧ lowerL p) (hg : section14RawGeometry p) : lowerNumericSuccessor t p := by
  exact p97_complete t p hs hb hp97 hlate hc hg

#print axioms solution
