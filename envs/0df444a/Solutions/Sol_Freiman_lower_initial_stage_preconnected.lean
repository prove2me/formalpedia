-- Prove2me | solution 1 for Freiman.lower_initial_stage_preconnected
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T06:24:28.196154+00:00
-- url     : https://prove2.me/submissions/44409455-2948-4a19-bd5b-0a07866115d6

import Definitions.Def_Freiman_lowerInitial
import Definitions.Def_Freiman_lowerInitialStage
import Mathlib.Tactic
import Theorems.Thm_Freiman_lower_entry_context_auxB
import Theorems.Thm_Freiman_lower_entry_family_domain
import Theorems.Thm_Freiman_lower_initial_family_normalization
import Theorems.Thm_Freiman_lower_initial_matrix_bottom
import Theorems.Thm_Freiman_lower_initial_word_fraction
import Theorems.Thm_Freiman_prefixEval_mobius

namespace M7Stage13AC

open Freiman

set_option maxHeartbeats 2000000

private noncomputable def acX (q : LowerPair) : ℝ :=
  4 + prefixEval (q.1 ++ [3,1,2,1,3]) lowerTau +
      prefixEval (q.2 ++ [2,1,3]) lowerTau

private noncomputable def acY (q : LowerPair) : ℝ :=
  4 + prefixEval (q.1 ++ [1,2,1,3]) lowerTau +
      prefixEval (q.2 ++ [1,2,1,3]) lowerTau

private noncomputable def acH (q : LowerPair) : Set ℝ :=
  Set.Icc (min (acX q) (acY q)) (max (acX q) (acY q))

private def acNext (q : LowerPair) : LowerPair :=
  (q.1 ++ [3,3], q.2 ++ [3,3])

private theorem pe_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [prefixEval, ih]

private theorem pe_nonneg (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ prefixEval w x := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
      simp only [prefixEval]
      have ha : (0 : ℝ) < ((a : ℕ) : ℝ) := by exact_mod_cast a.pos
      exact div_nonneg zero_le_one (by linarith)

private theorem pe_mono (w : List ℕ+) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x < y) :
    (w.length % 2 = 0 → prefixEval w x < prefixEval w y) ∧
    (w.length % 2 = 1 → prefixEval w y < prefixEval w x) := by
  induction w with
  | nil => exact ⟨fun _ => hxy, fun h => by simp at h⟩
  | cons a w ih =>
      have ha : (0 : ℝ) < ((a : ℕ) : ℝ) := by exact_mod_cast a.pos
      have px := pe_nonneg w x hx
      have py := pe_nonneg w y hy
      constructor
      · intro he
        have ho : w.length % 2 = 1 := by simp at he; omega
        have h := ih.2 ho
        simp only [prefixEval]
        apply one_div_lt_one_div_of_lt <;> linarith
      · intro ho
        have he : w.length % 2 = 0 := by simp at ho; omega
        have h := ih.1 he
        simp only [prefixEval]
        apply one_div_lt_one_div_of_lt <;> linarith

private theorem tau_nonneg : 0 ≤ lowerTau := by
  unfold lowerTau
  have hs := Real.sqrt_nonneg 3
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  nlinarith

private theorem tail_three_lt_common (r : List ℕ+) :
    prefixEval ((3 : ℕ+) :: r) lowerTau < prefixEval [1,2,1,3] lowerTau := by
  have hr := pe_nonneg r lowerTau tau_nonneg
  have hb := pe_nonneg ([1,3] : List ℕ+) lowerTau tau_nonneg
  have hc := pe_nonneg ([2,1,3] : List ℕ+) lowerTau tau_nonneg
  have hb_lt : prefixEval ([2,1,3] : List ℕ+) lowerTau < 1 := by
    change 1 / (2 + prefixEval ([1,3] : List ℕ+) lowerTau) < 1
    rw [div_lt_iff₀ (by linarith)]
    linarith
  rw [prefixEval, prefixEval]
  norm_num
  apply (inv_lt_inv₀ (by linarith) (by linarith)).2
  linarith

private theorem ac_overlap
    (q : LowerPair)
    (hpar : q.1.length % 2 = q.2.length % 2)
    (hcontact : lowerContact q
      [3,3,1,2,1,3] [3,1,2,1,3]
      [3,3,1,2,1,3] [2,1,3]) :
    (acH q ∩ acH (acNext q)).Nonempty := by
  have hcross : 0 < (-1 : ℝ) ^ q.1.length * (acY (acNext q) - acX q) := by
    unfold lowerContact at hcontact
    dsimp [acX, acY, acNext]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    nlinarith [hcontact]
  have ht1 : prefixEval ([3,3,3,1,2,1,3] : List ℕ+) lowerTau <
      prefixEval [1,2,1,3] lowerTau := tail_three_lt_common _
  have ht2 : prefixEval ([3,3,2,1,3] : List ℕ+) lowerTau <
      prefixEval [1,2,1,3] lowerTau := tail_three_lt_common _
  have h1 := pe_mono q.1
    (prefixEval ([3,3,3,1,2,1,3] : List ℕ+) lowerTau)
    (prefixEval ([1,2,1,3] : List ℕ+) lowerTau)
    (pe_nonneg _ _ tau_nonneg) (pe_nonneg _ _ tau_nonneg) ht1
  have h2 := pe_mono q.2
    (prefixEval ([3,3,2,1,3] : List ℕ+) lowerTau)
    (prefixEval ([1,2,1,3] : List ℕ+) lowerTau)
    (pe_nonneg _ _ tau_nonneg) (pe_nonneg _ _ tau_nonneg) ht2
  have hop : if q.1.length % 2 = 0 then acX (acNext q) < acY q
      else acY q < acX (acNext q) := by
    by_cases he : q.1.length % 2 = 0
    · simp only [he, if_true]
      have he2 : q.2.length % 2 = 0 := by omega
      have hu := h1.1 he
      have hv := h2.1 he2
      dsimp [acX, acY, acNext]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [pe_append, pe_append, pe_append, pe_append]
      linarith
    · simp only [he, if_false]
      have ho : q.1.length % 2 = 1 := by omega
      have ho2 : q.2.length % 2 = 1 := by omega
      have hu := h1.2 ho
      have hv := h2.2 ho2
      dsimp [acX, acY, acNext]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [pe_append, pe_append, pe_append, pe_append]
      linarith
  have hpairs :
      min (acX q) (acY q) ≤ max (acX (acNext q)) (acY (acNext q)) ∧
      min (acX (acNext q)) (acY (acNext q)) ≤ max (acX q) (acY q) := by
    by_cases he : q.1.length % 2 = 0
    · have hc : acX q < acY (acNext q) := by
        rw [neg_one_pow_eq_pow_mod_two, he, pow_zero, one_mul] at hcross
        linarith
      simp only [he, if_true] at hop
      constructor
      · calc
          min (acX q) (acY q) ≤ acX q := min_le_left _ _
          _ ≤ acY (acNext q) := le_of_lt hc
          _ ≤ max (acX (acNext q)) (acY (acNext q)) := le_max_right _ _
      · calc
          min (acX (acNext q)) (acY (acNext q)) ≤ acX (acNext q) := min_le_left _ _
          _ ≤ acY q := le_of_lt hop
          _ ≤ max (acX q) (acY q) := le_max_right _ _
    · have ho : q.1.length % 2 = 1 := by omega
      have hc : acY (acNext q) < acX q := by
        rw [neg_one_pow_eq_pow_mod_two, ho, pow_one] at hcross
        linarith
      simp only [he, if_false] at hop
      constructor
      · calc
          min (acX q) (acY q) ≤ acY q := min_le_right _ _
          _ ≤ acX (acNext q) := le_of_lt hop
          _ ≤ max (acX (acNext q)) (acY (acNext q)) := le_max_left _ _
      · calc
          min (acX (acNext q)) (acY (acNext q)) ≤ acY (acNext q) := min_le_right _ _
          _ ≤ acX q := le_of_lt hc
          _ ≤ max (acX q) (acY q) := le_max_left _ _
  refine ⟨max (min (acX q) (acY q))
      (min (acX (acNext q)) (acY (acNext q))), ?_⟩
  simp only [acH, Set.mem_inter_iff, Set.mem_Icc]
  constructor
  · exact ⟨le_max_left _ _, max_le min_le_max hpairs.2⟩
  · exact ⟨le_max_right _ _, max_le hpairs.1 min_le_max⟩

private theorem lower_A_step_two (hseams : lowerInitialSeams) :
    ∀ n k, (lowerFamilyH .A n k 0 ∩ lowerFamilyH .A n (k+2) 0).Nonempty := by
  intro n k
  let q := lowerNormalize (lowerFamilyPair .A n k 0)
  have hnext : lowerNormalize (lowerFamilyPair .A n (k+2) 0) = acNext q := by
    have hr : List.replicate ((k+2)+1) (3 : ℕ+) =
        List.replicate (k+1) 3 ++ [3,3] := by
      rw [show (k+2)+1 = (k+1)+2 by omega, List.replicate_add]
      rfl
    rw [lower_initial_family_normalization .A n (k+2) 0 (by decide)]
    dsimp [q]
    rw [lower_initial_family_normalization .A n k 0 (by decide)]
    simp [lowerFamilyPair, acNext, hr, List.append_assoc]
  have hpar : q.1.length % 2 = q.2.length % 2 := by
    rw [show q = (lowerFamilyPair .A n k 0).swap by
      dsimp [q]; simpa using lower_initial_family_normalization .A n k 0 (by decide)]
    simp [lowerFamilyPair]
    omega
  have hh := ac_overlap q hpar (hseams.1 n k)
  have hH : lowerFamilyH .A n k 0 = acH q := by
    simp [lowerFamilyH, acH, acX, acY, q]
  have hHnext : lowerFamilyH .A n (k+2) 0 = acH (acNext q) := by
    simp [lowerFamilyH, acH, acX, acY, hnext]
  rwa [hH, hHnext]

private theorem lower_C_step_two (hseams : lowerInitialSeams) :
    ∀ n k p, (lowerFamilyH .C n k p ∩ lowerFamilyH .C n k (p+2)).Nonempty := by
  intro n k p
  let q := lowerNormalize (lowerFamilyPair .C n k p)
  have hnext : lowerNormalize (lowerFamilyPair .C n k (p+2)) = acNext q := by
    have hr : List.replicate ((p+2)+1) (3 : ℕ+) =
        List.replicate (p+1) 3 ++ [3,3] := by
      rw [show (p+2)+1 = (p+1)+2 by omega, List.replicate_add]
      rfl
    rw [lower_initial_family_normalization .C n k (p+2) (by decide)]
    dsimp [q]
    rw [lower_initial_family_normalization .C n k p (by decide)]
    simp [lowerFamilyPair, acNext, hr, List.append_assoc]
  have hpar : q.1.length % 2 = q.2.length % 2 := by
    rw [show q = (lowerFamilyPair .C n k p).swap by
      dsimp [q]; simpa using lower_initial_family_normalization .C n k p (by decide)]
    simp [lowerFamilyPair]
    omega
  have hh := ac_overlap q hpar (hseams.2.1 n k p)
  have hH : lowerFamilyH .C n k p = acH q := by
    simp [lowerFamilyH, acH, acX, acY, q]
  have hHnext : lowerFamilyH .C n k (p+2) = acH (acNext q) := by
    simp [lowerFamilyH, acH, acX, acY, hnext]
  rwa [hH, hHnext]


end M7Stage13AC

open Freiman
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Stage13TailBounds

private theorem tau_pos : 0 < lowerTau := by
  unfold lowerTau
  have h : (1:ℝ) < Real.sqrt 3 := by
    rw [show (1:ℝ) = Real.sqrt 1 by norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

private theorem tuple8bounds :
    let a := prefixEval [3,1,3,2,1,3] lowerTau
    let c := prefixEval [3,3,3,1,2,1,3] lowerTau
    let b := prefixEval [2,1,3,3,1,2,1,3] lowerTau
    let d := prefixEval [3,3,2,1,3] lowerTau
    (53/200 : ℝ) < a ∧ a < (133/500 : ℝ) ∧
    (151/500 : ℝ) < c ∧ c < (303/1000 : ℝ) ∧
    (723/2000 : ℝ) < b ∧ b < (181/500 : ℝ) ∧
    (303/1000 : ℝ) < d ∧ d < (3033/10000 : ℝ) := by
  dsimp only
  have ht := tau_pos.le
  have hs := Real.sqrt_nonneg 3
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  repeat' apply And.intro
  all_goals
    rw [prefixEval_mobius _ _ ht]
    norm_num [wordContinuantP, wordContinuantPrevP, wordContinuantQ,
      wordContinuantPrevQ, wordContinuantData, lowerTau]
    try rw [div_lt_div_iff₀ (by nlinarith [tau_pos]) (by nlinarith [tau_pos])]
    try rw [div_lt_iff₀ (by nlinarith [tau_pos])]
    try rw [lt_div_iff₀ (by nlinarith [tau_pos])]
    nlinarith


end Stage13TailBounds

open Freiman

namespace M7StageB

private lemma pe_append : ∀ (u v : List ℕ+) (x : ℝ),
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x)
  | [], v, x => rfl
  | a :: u, v, x => by simp only [List.cons_append, prefixEval, pe_append u v x]

private lemma pe_pos : ∀ (w : List ℕ+) (x : ℝ), 0 < x → 0 < prefixEval w x
  | [], x, hx => by simpa [prefixEval] using hx
  | a :: w, x, hx => by
      rw [prefixEval]
      have hw := pe_pos w x hx
      have ha : (0 : ℝ) < ((a : ℕ) : ℝ) := by exact_mod_cast a.pos
      positivity

private lemma signed_prefix_lt (w : List ℕ+) (x y : ℝ)
    (hx : 0 < x) (hxy : x < y) :
    0 < (-1 : ℝ) ^ w.length * (prefixEval w y - prefixEval w x) := by
  have hy : 0 < y := hx.trans hxy
  obtain ⟨fx, dx, det⟩ := lower_initial_word_fraction w x hx
  obtain ⟨fy, dy, _⟩ := lower_initial_word_fraction w y hy
  rw [fx, fy]
  unfold lowerInitialMatEval
  dsimp only [lowerInitialMatDen] at dx dy
  rw [div_sub_div _ _ (ne_of_gt dy) (ne_of_gt dx)]
  rw [show ((lowerInitialWordMatrix w).a*y+(lowerInitialWordMatrix w).b)*
        ((lowerInitialWordMatrix w).c*x+(lowerInitialWordMatrix w).d)-
        ((lowerInitialWordMatrix w).c*y+(lowerInitialWordMatrix w).d)*
        ((lowerInitialWordMatrix w).a*x+(lowerInitialWordMatrix w).b) =
      (((lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d-
        (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c)*(y-x)) by ring]
  rw [det]
  have hp : 0 < (((lowerInitialWordMatrix w).c*y+(lowerInitialWordMatrix w).d)*
      ((lowerInitialWordMatrix w).c*x+(lowerInitialWordMatrix w).d)) := by
    simpa [lowerInitialMatDen] using mul_pos dy dx
  have hs : 0 < ((-1 : ℝ)^w.length)^2 := sq_pos_of_ne_zero (pow_ne_zero _ (by norm_num))
  rw [div_eq_mul_inv]
  have hprod := mul_pos (mul_pos hs (sub_pos.mpr hxy)) (inv_pos.mpr hp)
  nlinarith

private lemma icc_inter (a b c d : ℝ) (hbd : b ≤ d) (hca : c ≤ a) :
    (Set.Icc (min a b) (max a b) ∩ Set.Icc (min c d) (max c d)).Nonempty := by
  refine ⟨max (min a b) (min c d), ?_⟩
  constructor
  · exact ⟨le_max_left _ _, max_le
      (le_trans (min_le_left _ _) (le_max_left _ _))
      ((min_le_left _ _).trans (hca.trans (le_max_left _ _)))⟩
  · exact ⟨le_max_right _ _, max_le
      ((min_le_right _ _).trans (hbd.trans (le_max_right _ _)))
      ((min_le_right _ _).trans (le_max_right _ _))⟩

private lemma iIcc_cross (a b c d s : ℝ) (hs : s = 1 ∨ s = -1)
    (had : 0 < s * (d-a)) (hbc : 0 < s * (b-c)) :
    (Set.Icc (min a b) (max a b) ∩ Set.Icc (min c d) (max c d)).Nonempty := by
  rcases hs with rfl | rfl
  · simpa [min_comm, max_comm] using icc_inter b a c d (by linarith) (by linarith)
  · simpa [min_comm, max_comm] using icc_inter a b d c (by linarith) (by linarith)

private lemma iIcc_cross' (a b c d s : ℝ) (hs : s = 1 ∨ s = -1)
    (hdb : 0 < s * (d-b)) (hac : 0 < s * (a-c)) :
    (Set.Icc (min a b) (max a b) ∩ Set.Icc (min c d) (max c d)).Nonempty := by
  rcases hs with rfl | rfl
  · exact icc_inter a b c d (by linarith) (by linarith)
  · simpa [min_comm, max_comm] using icc_inter b a d c (by linarith) (by linarith)

private lemma repeat_len (n : ℕ) : (lowerRepeat lowerPeriod n).length = 6*n := by
  simp [lowerRepeat, lowerPeriod]
  omega

private lemma neg_one_pow_cases (m : ℕ) : (-1 : ℝ)^m = 1 ∨ (-1 : ℝ)^m = -1 := by
  rw [neg_one_pow_eq_pow_mod_two]
  have hm : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one m
  rcases hm with hm | hm
  · left; simp [hm]
  · right; simp [hm]

private def bL (n k : ℕ) : List ℕ+ :=
  [3,2,1,1] ++ lowerRepeat lowerPeriod n ++ [3,1,3,1,2] ++ List.replicate k 3

private def bR (n k : ℕ) : List ℕ+ :=
  [4,3,2,2] ++ lowerRepeat lowerPeriod n ++ [3,1] ++ List.replicate (k+1) 3

private noncomputable def bX (n k : ℕ) : ℝ :=
  4 + prefixEval (bL n k ++ [3,1,2,1,3]) lowerTau +
    prefixEval (bR n k ++ [2,1,3]) lowerTau

private noncomputable def bY (n k : ℕ) : ℝ :=
  4 + prefixEval (bL n k ++ if k = 0 then [1,3] else [1,2,1,3]) lowerTau +
    prefixEval (bR n k ++ [1,2,1,3]) lowerTau

private noncomputable def cX (n k p : ℕ) : ℝ :=
  4 + prefixEval (bL n k ++ [3,1] ++ List.replicate (p+1) 3 ++ [2,1,3]) lowerTau +
    prefixEval (bR n k ++ [2,1] ++ List.replicate (p+1) 3 ++ [3,1,2,1,3]) lowerTau

private noncomputable def cY (n k p : ℕ) : ℝ :=
  4 + prefixEval (bL n k ++ [3,1] ++ List.replicate (p+1) 3 ++ [1,2,1,3]) lowerTau +
    prefixEval (bR n k ++ [2,1] ++ List.replicate (p+1) 3 ++ [1,2,1,3]) lowerTau

private lemma familyH_B (n k : ℕ) :
    lowerFamilyH .B n k 0 = Set.Icc (min (bX n k) (bY n k)) (max (bX n k) (bY n k)) := by
  rw [lowerFamilyH]
  rw [lower_initial_family_normalization .B n k 0 (by decide)]
  simp [lowerFamilyPair, bL, bR, bX, bY]

private lemma familyH_C (n k p : ℕ) :
    lowerFamilyH .C n k p = Set.Icc (min (cX n k p) (cY n k p)) (max (cX n k p) (cY n k p)) := by
  rw [lowerFamilyH]
  rw [lower_initial_family_normalization .C n k p (by decide)]
  simp [lowerFamilyPair, bL, bR, cX, cY, List.replicate_succ']
  congr 2 <;> ring

private lemma b_length (n k : ℕ) : (bL n k).length = 9 + 6*n + k := by
  simp [bL, repeat_len]
  omega

private lemma seam_B_C1 (hseams : lowerInitialSeams) (n k : ℕ) :
    0 < (-1 : ℝ)^(bL n k).length * (cY n k 1 - bX n k) := by
  have h := hseams.2.2.1 n k
  rw [lower_initial_family_normalization .B n k 0 (by decide)] at h
  simp [lowerContact, lowerFamilyPair, bL, bR, bX, cY,
    List.replicate_succ', List.replicate_add, add_assoc, add_left_comm, add_comm] at h ⊢
  linarith

private lemma seam_C0_B2 (hseams : lowerInitialSeams) (n k : ℕ) :
    0 < (-1 : ℝ)^(bL n k).length * (bY n (k+2) - cY n k 0) := by
  have h := hseams.2.2.2.1 n k
  rw [lower_initial_family_normalization .B n k 0 (by decide)] at h
  simp [lowerContact, lowerFamilyPair, bL, bR, bY, cY,
    List.replicate_succ', List.replicate_add, add_assoc, add_left_comm, add_comm] at h ⊢
  linarith

private lemma tau_pos : 0 < lowerTau := by
  unfold lowerTau
  have h : (1 : ℝ) < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

private lemma bc_tail_order :
    prefixEval [3,1,3,3,2,1,3] lowerTau < prefixEval [1,2,1,3] lowerTau ∧
    prefixEval [3,1,3,3,2,1,3] lowerTau < prefixEval [1,3] lowerTau ∧
    prefixEval [2,1,3,3,3,1,2,1,3] lowerTau < prefixEval [1,2,1,3] lowerTau := by
  have hs0 := Real.sqrt_nonneg 3
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  repeat' apply And.intro
  all_goals
    rw [prefixEval_mobius _ _ tau_pos.le, prefixEval_mobius _ _ tau_pos.le]
    norm_num [wordContinuantP, wordContinuantPrevP, wordContinuantQ,
      wordContinuantPrevQ, wordContinuantData, lowerTau]
    rw [div_lt_div_iff₀ (by nlinarith [tau_pos]) (by nlinarith [tau_pos])]
    nlinarith

private lemma companion_B_C1 (n k : ℕ) :
    0 < (-1 : ℝ)^(bL n k).length * (bY n k - cX n k 1) := by
  have ht := tau_pos
  obtain ⟨ht1, ht0, ht2⟩ := bc_tail_order
  have hR := signed_prefix_lt (bR n k)
    (prefixEval [2,1,3,3,3,1,2,1,3] lowerTau)
    (prefixEval [1,2,1,3] lowerTau) (pe_pos _ _ ht) ht2
  have hsign : (-1 : ℝ)^(bR n k).length = (-1 : ℝ)^(bL n k).length := by
    have hm : (bR n k).length % 2 = (bL n k).length % 2 := by
      simp [bL, bR, repeat_len]
      omega
    calc
      (-1 : ℝ)^(bR n k).length = (-1 : ℝ)^((bR n k).length % 2) := neg_one_pow_eq_pow_mod_two _
      _ = (-1 : ℝ)^((bL n k).length % 2) := congrArg (fun j : ℕ => (-1 : ℝ)^j) hm
      _ = (-1 : ℝ)^(bL n k).length := (neg_one_pow_eq_pow_mod_two _).symm
  rw [hsign] at hR
  by_cases hk : k = 0
  · subst k
    have hL := signed_prefix_lt (bL n 0)
      (prefixEval [3,1,3,3,2,1,3] lowerTau)
      (prefixEval [1,3] lowerTau) (pe_pos _ _ ht) ht0
    rw [show bY n 0 = 4 + prefixEval (bL n 0 ++ [1,3]) lowerTau +
      prefixEval (bR n 0 ++ [1,2,1,3]) lowerTau by simp [bY]]
    rw [show cX n 0 1 = 4 + prefixEval (bL n 0 ++ [3,1,3,3,2,1,3]) lowerTau +
      prefixEval (bR n 0 ++ [2,1,3,3,3,1,2,1,3]) lowerTau by
        simp [cX, List.replicate_succ']]
    repeat' rw [pe_append]
    nlinarith
  · have hL := signed_prefix_lt (bL n k)
      (prefixEval [3,1,3,3,2,1,3] lowerTau)
      (prefixEval [1,2,1,3] lowerTau) (pe_pos _ _ ht) ht1
    rw [show bY n k = 4 + prefixEval (bL n k ++ [1,2,1,3]) lowerTau +
      prefixEval (bR n k ++ [1,2,1,3]) lowerTau by simp [bY, hk]]
    rw [show cX n k 1 = 4 + prefixEval (bL n k ++ [3,1,3,3,2,1,3]) lowerTau +
      prefixEval (bR n k ++ [2,1,3,3,3,1,2,1,3]) lowerTau by
        simp [cX, List.replicate_succ']]
    repeat' rw [pe_append]
    nlinarith

private lemma cd_pos : ∀ w : List ℕ+, 0 < ((lowerCD w).2 : ℝ) := by
  intro w
  have hn : 0 < (lowerCD w).2 := by
    induction w using List.reverseRecOn with
    | nil => norm_num [lowerCD]
    | append_singleton w a ih =>
      have hc : lowerCD (w ++ [a]) =
          ((lowerCD w).2, (lowerCD w).1 + (a : ℕ) * (lowerCD w).2) := by
        simp [lowerCD, List.foldl_append]
      rw [hc]
      dsimp only
      positivity
  exact_mod_cast hn

private lemma margin_fraction_algebra
    (sg x y dm dn ra rb sc sd : ℝ)
    (hsg : sg^2 = 1)
    (hdm : dm ≠ 0) (hdn : dn ≠ 0)
    (hra : ra ≠ 0) (hrb : rb ≠ 0) (hsc : sc ≠ 0) (hsd : sd ≠ 0) :
    sg * (sg*x/(dm*ra*(dm*rb)) + sg*y/(dn*sc*(dn*sd))) =
      (x*sc*sd + dm^2/dn^2*y*ra*rb) / (dm^2*ra*rb*sc*sd) := by
  field_simp
  rw [hsg]
  ring

private lemma contact_of_margin (p : LowerPair) (u v w z : List ℕ+)
    (hlen : p.1.length % 2 = p.2.length % 2)
    (hd : lowerEntryDomain p)
    (hu : 0 < prefixEval u lowerTau) (hv : 0 < prefixEval v lowerTau)
    (hw : 0 < prefixEval w lowerTau) (hz : 0 < prefixEval z lowerTau)
    (hm : 0 <
      (prefixEval u lowerTau-prefixEval v lowerTau) *
        (1+lowerRatio p.2*prefixEval w lowerTau) *
        (1+lowerRatio p.2*prefixEval z lowerTau) +
      lowerScale p * (prefixEval w lowerTau-prefixEval z lowerTau) *
        (1+lowerRatio p.1*prefixEval u lowerTau) *
        (1+lowerRatio p.1*prefixEval v lowerTau)) :
    lowerContact p u v w z := by
  let A := prefixEval u lowerTau
  let B := prefixEval v lowerTau
  let C := prefixEval w lowerTau
  let D := prefixEval z lowerTau
  let M := lowerInitialWordMatrix p.1
  let N := lowerInitialWordMatrix p.2
  let r := lowerRatio p.1
  let s := lowerRatio p.2
  let q := lowerScale p
  let sg := (-1 : ℝ)^p.1.length
  have hDA : 0 < M.c*A+M.d := by
    simpa [M, A, lowerInitialMatDen] using (lower_initial_word_fraction p.1 A hu).2.1
  have hDB : 0 < M.c*B+M.d := by
    simpa [M, B, lowerInitialMatDen] using (lower_initial_word_fraction p.1 B hv).2.1
  have hDC : 0 < N.c*C+N.d := by
    simpa [N, C, lowerInitialMatDen] using (lower_initial_word_fraction p.2 C hw).2.1
  have hDD : 0 < N.c*D+N.d := by
    simpa [N, D, lowerInitialMatDen] using (lower_initial_word_fraction p.2 D hz).2.1
  have dM : 0 < M.d := by
    rw [show M.d = ((lowerCD p.1).2 : ℝ) by simpa [M] using (lower_initial_matrix_bottom p.1).2]
    exact cd_pos _
  have dN : 0 < N.d := by
    rw [show N.d = ((lowerCD p.2).2 : ℝ) by simpa [N] using (lower_initial_matrix_bottom p.2).2]
    exact cd_pos _
  have er : r = M.c/M.d := by
    dsimp [r, lowerRatio]
    rw [← (lower_initial_matrix_bottom p.1).1, ← (lower_initial_matrix_bottom p.1).2]
  have es : s = N.c/N.d := by
    dsimp [s, lowerRatio]
    rw [← (lower_initial_matrix_bottom p.2).1, ← (lower_initial_matrix_bottom p.2).2]
  have eq : q = M.d^2/N.d^2 := by
    dsimp [q, lowerScale]
    rw [← (lower_initial_matrix_bottom p.1).2, ← (lower_initial_matrix_bottom p.2).2]
  have denA : M.c*A+M.d = M.d*(1+r*A) := by rw [er]; field_simp <;> ring
  have denB : M.c*B+M.d = M.d*(1+r*B) := by rw [er]; field_simp <;> ring
  have denC : N.c*C+N.d = N.d*(1+s*C) := by rw [es]; field_simp <;> ring
  have denD : N.c*D+N.d = N.d*(1+s*D) := by rw [es]; field_simp <;> ring
  have pA : 0 < 1+r*A := by nlinarith [dM, hDA, denA]
  have pB : 0 < 1+r*B := by nlinarith [dM, hDB, denB]
  have pC : 0 < 1+s*C := by nlinarith [dN, hDC, denC]
  have pD : 0 < 1+s*D := by nlinarith [dN, hDD, denD]
  have diffM : prefixEval p.1 A-prefixEval p.1 B =
      sg*(A-B)/((M.c*A+M.d)*(M.c*B+M.d)) := by
    rw [(lower_initial_word_fraction p.1 A hu).1,
      (lower_initial_word_fraction p.1 B hv).1]
    dsimp [lowerInitialMatEval, M]
    rw [div_sub_div _ _ (ne_of_gt hDA) (ne_of_gt hDB)]
    have hdet := (lower_initial_word_fraction p.1 A hu).2.2
    dsimp [M, sg] at hdet ⊢
    rw [show (lowerInitialWordMatrix p.1).a*A+(lowerInitialWordMatrix p.1).b =
      (lowerInitialWordMatrix p.1).a*A+(lowerInitialWordMatrix p.1).b by rfl]
    rw [show ((lowerInitialWordMatrix p.1).a*A+(lowerInitialWordMatrix p.1).b)*
        ((lowerInitialWordMatrix p.1).c*B+(lowerInitialWordMatrix p.1).d)-
        ((lowerInitialWordMatrix p.1).c*A+(lowerInitialWordMatrix p.1).d)*
        ((lowerInitialWordMatrix p.1).a*B+(lowerInitialWordMatrix p.1).b) =
        (A-B)*((lowerInitialWordMatrix p.1).a*(lowerInitialWordMatrix p.1).d-
          (lowerInitialWordMatrix p.1).b*(lowerInitialWordMatrix p.1).c) by ring]
    rw [hdet]
    ring
  have diffN : prefixEval p.2 C-prefixEval p.2 D =
      sg*(C-D)/((N.c*C+N.d)*(N.c*D+N.d)) := by
    rw [(lower_initial_word_fraction p.2 C hw).1,
      (lower_initial_word_fraction p.2 D hz).1]
    dsimp [lowerInitialMatEval, N]
    rw [div_sub_div _ _ (ne_of_gt hDC) (ne_of_gt hDD)]
    have hdet := (lower_initial_word_fraction p.2 C hw).2.2
    rw [neg_one_pow_eq_pow_mod_two, ← hlen, ← neg_one_pow_eq_pow_mod_two] at hdet
    dsimp [N, sg] at hdet ⊢
    rw [show ((lowerInitialWordMatrix p.2).a*C+(lowerInitialWordMatrix p.2).b)*
        ((lowerInitialWordMatrix p.2).c*D+(lowerInitialWordMatrix p.2).d)-
        ((lowerInitialWordMatrix p.2).c*C+(lowerInitialWordMatrix p.2).d)*
        ((lowerInitialWordMatrix p.2).a*D+(lowerInitialWordMatrix p.2).b) =
        (C-D)*((lowerInitialWordMatrix p.2).a*(lowerInitialWordMatrix p.2).d-
          (lowerInitialWordMatrix p.2).b*(lowerInitialWordMatrix p.2).c) by ring]
    rw [hdet]
    ring
  have sg2 : sg^2 = 1 := by
    rcases neg_one_pow_cases p.1.length with h | h <;> simp [sg, h]
  unfold lowerContact
  repeat' rw [pe_append]
  change 0 < sg * (prefixEval p.1 A-prefixEval p.1 B +
    prefixEval p.2 C-prefixEval p.2 D)
  rw [show prefixEval p.1 A-prefixEval p.1 B + prefixEval p.2 C-prefixEval p.2 D =
    (prefixEval p.1 A-prefixEval p.1 B) + (prefixEval p.2 C-prefixEval p.2 D) by ring]
  change 0 < (A-B)*(1+s*C)*(1+s*D) + q*(C-D)*(1+r*A)*(1+r*B) at hm
  rw [eq] at hm
  rw [diffM, diffN, denA, denB, denC, denD]
  have hden : 0 < M.d^2*(1+r*A)*(1+r*B)*(1+s*C)*(1+s*D) := by positivity
  rw [margin_fraction_algebra sg (A-B) (C-D) M.d N.d
    (1+r*A) (1+r*B) (1+s*C) (1+s*D) sg2
    (ne_of_gt dM) (ne_of_gt dN) (ne_of_gt pA) (ne_of_gt pB)
    (ne_of_gt pC) (ne_of_gt pD)]
  exact div_pos hm hden

private lemma companion_C0_B2 (n k : ℕ) :
    0 < (-1 : ℝ)^(bL n k).length * (cX n k 0 - bX n (k+2)) := by
  let a := prefixEval [3,1,3,2,1,3] lowerTau
  let c := prefixEval [3,3,3,1,2,1,3] lowerTau
  let b := prefixEval [2,1,3,3,1,2,1,3] lowerTau
  let d := prefixEval [3,3,2,1,3] lowerTau
  obtain ⟨ha0, ha1, hc, hc0, hb0, hb, hd0, hd⟩ := Stage13TailBounds.tuple8bounds
  change (53/200 : ℝ) < a at ha0
  change a < (133/500 : ℝ) at ha1
  change (151/500 : ℝ) < c at hc
  change c < (303/1000 : ℝ) at hc0
  change (723/2000 : ℝ) < b at hb0
  change (303/1000 : ℝ) < d at hd0
  change b < (181/500 : ℝ) at hb
  change d < (3033/10000 : ℝ) at hd
  have ha : (13/50 : ℝ) < a := by linarith
  have hca : c-a < (19/500 : ℝ) := by linarith
  have hbd : (29/500 : ℝ) < b-d := by linarith
  have hdom := lower_entry_family_domain .B n k 0
  rw [lower_initial_family_normalization .B n k 0 (by decide)] at hdom
  simp at hdom
  have hq := hdom.1
  have hr := hdom.2.2.1
  have hslo := hdom.2.2.2.2.1
  have hs := hdom.2.2.2.2.2
  have hq' : (71/100 : ℝ) < lowerScale (lowerFamilyPair .B n k 0) := by linarith
  have hleft : (57/50 : ℝ) <
      (1+lowerRatio (bL n k)*a)*(1+lowerRatio (bL n k)*c) := by
    change (1/4 : ℝ) < lowerRatio (bL n k) at hr
    have hp1 := mul_lt_mul_of_pos_left ha (by linarith : 0 < lowerRatio (bL n k))
    have hp2 := mul_lt_mul_of_pos_left hc (by linarith : 0 < lowerRatio (bL n k))
    have f1 : (213/200 : ℝ) < 1+lowerRatio (bL n k)*a := by nlinarith
    have f2 : (43/40 : ℝ) < 1+lowerRatio (bL n k)*c := by nlinarith
    have hp := mul_pos (sub_pos.mpr f1) (sub_pos.mpr f2)
    nlinarith
  have hright :
      (1+lowerRatio (bR n k)*b)*(1+lowerRatio (bR n k)*d) < (61/50 : ℝ) := by
    change lowerRatio (bR n k) < (4/13 : ℝ) at hs
    have hbpos : 0 < b := by linarith
    have hdpos : 0 < d := pe_pos _ _ tau_pos
    have hp1 : lowerRatio (bR n k)*b < (4/13 : ℝ)*(181/500 : ℝ) :=
      mul_lt_mul hs hb.le hbpos (by norm_num)
    have hp2 : lowerRatio (bR n k)*d < (4/13 : ℝ)*(38/125 : ℝ) :=
      mul_lt_mul hs (by linarith : d ≤ (38/125 : ℝ)) hdpos (by norm_num)
    have f1 : 1+lowerRatio (bR n k)*b < (1806/1625 : ℝ) := by nlinarith [hp1]
    have f2 : 1+lowerRatio (bR n k)*d < (1777/1625 : ℝ) := by nlinarith [hp2]
    change (1/4 : ℝ) < lowerRatio (bR n k) at hslo
    have hf2pos : 0 < 1+lowerRatio (bR n k)*d := by nlinarith [hdpos]
    calc
      _ < (1806/1625 : ℝ) * (1+lowerRatio (bR n k)*d) :=
        mul_lt_mul_of_pos_right f1 hf2pos
      _ < (1806/1625 : ℝ) * (1777/1625 : ℝ) :=
        mul_lt_mul_of_pos_left f2 (by norm_num)
      _ < (61/50 : ℝ) := by norm_num
  have hmargin : 0 <
      (a-c)*(1+lowerRatio (bR n k)*b)*(1+lowerRatio (bR n k)*d) +
      lowerScale (lowerFamilyPair .B n k 0)*(b-d)*
        (1+lowerRatio (bL n k)*a)*(1+lowerRatio (bL n k)*c) := by
    have hneg : (a-c)*(1+lowerRatio (bR n k)*b)*(1+lowerRatio (bR n k)*d) >
        -(19/500 : ℝ)*(61/50 : ℝ) := by
      have hfac : 0 < (1+lowerRatio (bR n k)*b)*(1+lowerRatio (bR n k)*d) := by
        change (1/4 : ℝ) < lowerRatio (bR n k) at hslo
        have hbpos : 0 < b := by linarith
        have hdpos : 0 < d := pe_pos _ _ tau_pos
        exact mul_pos (by nlinarith) (by nlinarith)
      have hmul := mul_lt_mul hca hright.le hfac
        (by norm_num : 0 ≤ (19/500 : ℝ))
      nlinarith
    have hpos : lowerScale (lowerFamilyPair .B n k 0)*(b-d)*
        (1+lowerRatio (bL n k)*a)*(1+lowerRatio (bL n k)*c) >
        (71/100 : ℝ)*(29/500 : ℝ)*(57/50 : ℝ) := by
      have hp : 0 < b-d := by linarith
      have hscale : 0 < lowerScale (lowerFamilyPair .B n k 0) := by linarith
      have hbase : (71/100 : ℝ)*(29/500 : ℝ) <
          lowerScale (lowerFamilyPair .B n k 0)*(b-d) :=
        mul_lt_mul hq' hbd.le (by norm_num) (by linarith)
      have hbase' := mul_lt_mul_of_pos_right hbase (by norm_num : (0:ℝ) < 57/50)
      have hfac := mul_lt_mul_of_pos_left hleft (mul_pos hscale hp)
      nlinarith
    nlinarith
  have hlen : (bL n k).length % 2 = (bR n k).length % 2 := by
    simp [bL, bR, repeat_len]
    omega
  have hcontact := contact_of_margin (bL n k, bR n k)
    [3,1,3,2,1,3] [3,3,3,1,2,1,3]
    [2,1,3,3,1,2,1,3] [3,3,2,1,3] hlen hdom
    (pe_pos _ _ tau_pos) (pe_pos _ _ tau_pos) (pe_pos _ _ tau_pos) (pe_pos _ _ tau_pos)
    (by simpa [a,b,c,d, bL, bR, lowerFamilyPair] using hmargin)
  unfold lowerContact at hcontact
  simp [bX, cX, bL, bR, List.replicate_succ', List.replicate_add,
    add_assoc, add_left_comm, add_comm] at hcontact ⊢
  linarith

private theorem lower_B_C1_overlap (hseams : lowerInitialSeams) (n k : ℕ) :
    (lowerFamilyH .B n k 0 ∩ lowerFamilyH .C n k 1).Nonempty := by
  rw [familyH_B, familyH_C]
  exact iIcc_cross (bX n k) (bY n k) (cX n k 1) (cY n k 1)
    ((-1 : ℝ)^(bL n k).length) (neg_one_pow_cases _)
    (seam_B_C1 hseams n k) (companion_B_C1 n k)

private theorem lower_C0_B2_overlap (hseams : lowerInitialSeams) (n k : ℕ) :
    (lowerFamilyH .C n k 0 ∩ lowerFamilyH .B n (k+2) 0).Nonempty := by
  rw [familyH_C, familyH_B]
  exact iIcc_cross' (cX n k 0) (cY n k 0) (bX n (k+2)) (bY n (k+2))
    ((-1 : ℝ)^(bL n k).length) (neg_one_pow_cases _)
    (seam_C0_B2 hseams n k) (companion_C0_B2 n k)


end M7StageB

open Freiman
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Stage13Finite

private theorem tau_pos : 0 < lowerTau := by
  unfold lowerTau
  have h : (1:ℝ) < Real.sqrt 3 := by
    rw [show (1:ℝ) = Real.sqrt 1 by norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

private theorem pe_pos : ∀ (w : List ℕ+) (t : ℝ), 0 < t → 0 < prefixEval w t
  | [], t, ht => ht
  | a::w, t, ht => by
      simp only [prefixEval]
      have hp := pe_pos w t ht
      positivity

private theorem pe_even (w : List ℕ+) (he : w.length % 2 = 0)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) : prefixEval w a < prefixEval w b := by
  have hb : 0 < b := ha.trans hab
  obtain ⟨fa,da,det⟩ := lower_initial_word_fraction w a ha
  obtain ⟨fb,db,_⟩ := lower_initial_word_fraction w b hb
  rw [neg_one_pow_eq_pow_mod_two,he,pow_zero] at det
  rw [fa,fb]
  unfold lowerInitialMatEval
  dsimp only [lowerInitialMatDen] at da db
  rw [div_lt_div_iff₀ da db]
  have hpol :
      ((lowerInitialWordMatrix w).a*b+(lowerInitialWordMatrix w).b)*
        ((lowerInitialWordMatrix w).c*a+(lowerInitialWordMatrix w).d) -
      ((lowerInitialWordMatrix w).a*a+(lowerInitialWordMatrix w).b)*
        ((lowerInitialWordMatrix w).c*b+(lowerInitialWordMatrix w).d) = b-a := by
    calc
      _ = ((lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d -
          (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c)*(b-a) := by ring
      _ = b-a := by rw [det]; ring
  linarith

private theorem pe_append : ∀ (u v : List ℕ+) (t : ℝ),
    prefixEval (u++v) t = prefixEval u (prefixEval v t)
  | [], v, t => rfl
  | a::u, v, t => by simp only [List.cons_append,prefixEval,pe_append u v t]

private theorem finite_orders :
    prefixEval [3,1,3,1,2,3,3,1,2,1,3] lowerTau < prefixEval [3,1,3,2,1,3] lowerTau ∧
    prefixEval [3,1,3,3,2,1,3] lowerTau < prefixEval [3,3,1,2,1,3] lowerTau ∧
    prefixEval [3,1,3,1,2,1,3,1,2,1,3] lowerTau < prefixEval [3,1,3,1,2,3,1,2,1,3] lowerTau ∧
    prefixEval [3,1,3,1,2,1,3,1,2,1,3] lowerTau < prefixEval [3,1,3,2,1,3] lowerTau := by
  have ht := tau_pos.le
  have hs := Real.sqrt_nonneg 3
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  repeat' apply And.intro
  all_goals
    rw [prefixEval_mobius _ _ ht,prefixEval_mobius _ _ ht]
    norm_num [wordContinuantP,wordContinuantPrevP,wordContinuantQ,
      wordContinuantPrevQ,wordContinuantData,lowerTau]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith

private theorem base_even (w : List ℕ+) (hw : w.length=4) (n : ℕ) :
    (w++lowerRepeat lowerPeriod n).length % 2 = 0 := by
  simp [lowerRepeat,lowerPeriod,hw,List.length_flatten] <;> omega

private theorem icc_inter (a b c d : ℝ) (hbd : b ≤ d) (hca : c ≤ a) :
    (Set.Icc (min a b) (max a b) ∩ Set.Icc (min c d) (max c d)).Nonempty := by
  refine ⟨max (min a b) (min c d), ?_⟩
  constructor
  · exact ⟨le_max_left _ _, max_le
      (le_trans (min_le_left _ _) (le_max_left _ _))
      ((min_le_left _ _).trans (hca.trans (le_max_left _ _)))⟩
  · exact ⟨le_max_right _ _, max_le
      ((min_le_right _ _).trans (hbd.trans (le_max_right _ _)))
      ((min_le_right _ _).trans (le_max_right _ _))⟩

private theorem aux_normalize (n : ℕ) :
    lowerNormalize (lowerFamilyPair .auxB n 0 0) = lowerFamilyPair .auxB n 0 0 := by
  obtain ⟨c,hc,_⟩ := lower_entry_context_auxB n 0 0
  have hr : lowerEnds (lowerNormalize (lowerFamilyPair .auxB n 0 0)).2 [3] := hc.2.2.1
  by_cases hw : lowerWidth (lowerFamilyPair .auxB n 0 0).2 ≤
      lowerWidth (lowerFamilyPair .auxB n 0 0).1
  · simp [lowerNormalize,hw]
  · simp only [lowerNormalize,if_neg hw,Prod.snd] at hr
    simp [lowerFamilyPair,lowerEnds,← List.reverse_prefix] at hr

private theorem repeat_succ (n : ℕ) :
    lowerRepeat lowerPeriod (n+1) = lowerRepeat lowerPeriod n ++ lowerPeriod := by
  simp [lowerRepeat,List.replicate_add,List.flatten_append]

private theorem a0_b1 (hseams : lowerInitialSeams) (n : ℕ) :
    (lowerFamilyH .A n 0 0 ∩ lowerFamilyH .B n 1 0).Nonempty := by
  let L := [3,2,1,1] ++ lowerRepeat lowerPeriod n
  let R := [4,3,2,2] ++ lowerRepeat lowerPeriod n
  let ax := 4 + prefixEval (L++[3,1,3,2,1,3]) lowerTau + prefixEval (R++[3,3,1,2,1,3]) lowerTau
  let ay := 4 + prefixEval (L++[3,1,3,1,2,1,3]) lowerTau + prefixEval (R++[3,1,2,1,3]) lowerTau
  let bx := 4 + prefixEval (L++[3,1,3,1,2,3,3,1,2,1,3]) lowerTau + prefixEval (R++[3,1,3,3,2,1,3]) lowerTau
  let byv := 4 + prefixEval (L++[3,1,3,1,2,3,1,2,1,3]) lowerTau + prefixEval (R++[3,1,3,3,1,2,1,3]) lowerTau
  have hA : lowerFamilyH .A n 0 0 = Set.Icc (min ax ay) (max ax ay) := by
    have hn := lower_initial_family_normalization .A n 0 0 (by decide)
    simp only [lowerFamilyH,hn]
    simp [lowerFamilyPair,ax,ay,L,R,List.append_assoc]
    congr 2 <;> ring
  have hB : lowerFamilyH .B n 1 0 = Set.Icc (min bx byv) (max bx byv) := by
    have hn := lower_initial_family_normalization .B n 1 0 (by decide)
    simp only [lowerFamilyH,hn]
    simp [lowerFamilyPair,bx,byv,L,R,List.append_assoc]
  have hyy : ay < byv := by
    have hs := hseams.2.2.2.2.1 n
    dsimp [lowerNContact] at hs
    dsimp [ay,byv,L,R]
    linarith
  have hxx : bx < ax := by
    have hl := pe_even L (base_even [3,2,1,1] (by rfl) n) _ _
      (pe_pos _ _ tau_pos) finite_orders.1
    have hr := pe_even R (base_even [4,3,2,2] (by rfl) n) _ _
      (pe_pos _ _ tau_pos) finite_orders.2.1
    dsimp only [bx,ax]
    simp only [pe_append]
    linarith
  rw [hA,hB]
  exact icc_inter ax ay bx byv hyy.le hxx.le

private theorem aux_b0 (hseams : lowerInitialSeams) (n : ℕ) :
    (lowerFamilyH .auxB n 0 0 ∩ lowerFamilyH .B n 0 0).Nonempty := by
  let L := [3,2,1,1] ++ lowerRepeat lowerPeriod n
  let R := [4,3,2,2] ++ lowerRepeat lowerPeriod n
  let ax := 4 + prefixEval (L++[3,1,3,1,2,1,3,1,2,3,1,2,1,3]) lowerTau +
    prefixEval (R++[3,1,3,1,2,1,3,2,1,3]) lowerTau
  let ay := 4 + prefixEval (L++[3,1,3,1,2,1,3,1,2,1,3]) lowerTau +
    prefixEval (R++[3,1,3,1,2,1,3,1,2,1,3]) lowerTau
  let bx := 4 + prefixEval (L++[3,1,3,1,2,3,1,2,1,3]) lowerTau +
    prefixEval (R++[3,1,3,2,1,3]) lowerTau
  let byv := 4 + prefixEval (L++[3,1,3,1,2,1,3]) lowerTau +
    prefixEval (R++[3,1,3,1,2,1,3]) lowerTau
  have hA : lowerFamilyH .auxB n 0 0 = Set.Icc (min ax ay) (max ax ay) := by
    simp only [lowerFamilyH,aux_normalize]
    simp only [lowerFamilyPair,repeat_succ]
    simp [ax,ay,L,R,lowerPeriod,List.append_assoc]
  have hB : lowerFamilyH .B n 0 0 = Set.Icc (min bx byv) (max bx byv) := by
    have hn := lower_initial_family_normalization .B n 0 0 (by decide)
    simp only [lowerFamilyH,hn]
    simp [lowerFamilyPair,bx,byv,L,R,List.append_assoc]
  have hyx : byv < ax := by
    have hs := hseams.2.2.2.2.2.2 n
    dsimp [lowerNContact] at hs
    dsimp [byv,ax,L,R]
    linarith
  have hxy : ay < bx := by
    have hl := pe_even L (base_even [3,2,1,1] (by rfl) n) _ _
      (pe_pos _ _ tau_pos) finite_orders.2.2.1
    have hr := pe_even R (base_even [4,3,2,2] (by rfl) n) _ _
      (pe_pos _ _ tau_pos) finite_orders.2.2.2
    dsimp only [ay,bx]
    simp only [pe_append]
    linarith
  rw [hA,hB,min_comm bx byv,max_comm bx byv]
  exact icc_inter ax ay byv bx hxy.le hyx.le

end Stage13Finite

open Set Filter Topology

namespace Freiman

private theorem mem_closure_iUnion_of_tendsto
    (S : ℕ → Set ℝ) (u : ℕ → ℝ) (x : ℝ)
    (hu : ∀ k, u k ∈ S k) (hlim : Tendsto u atTop (nhds x)) :
    x ∈ closure (⋃ k, S k) := by
  apply mem_closure_of_tendsto hlim
  filter_upwards [] with k
  exact mem_iUnion.2 ⟨k, hu k⟩

private theorem tendsto_parity {u : ℕ → ℝ} {x : ℝ}
    (h : Tendsto u atTop (nhds x)) (r : ℕ) :
    Tendsto (fun k => u (2*k+r)) atTop (nhds x) := by
  apply h.comp
  rw [tendsto_atTop]
  intro b
  exact eventually_atTop.2 ⟨b, fun a ha => by omega⟩

private theorem preconnected_twoStep_with_limit
    (S : ℕ → Set ℝ) (x : ℝ)
    (hS : ∀ k, IsPreconnected (S k))
    (hstep : ∀ k, (S k ∩ S (k+2)).Nonempty)
    (heven : x ∈ closure (⋃ k, S (2*k)))
    (hodd : x ∈ closure (⋃ k, S (2*k+1))) :
    IsPreconnected ({x} ∪ ⋃ k, S k) := by
  have hc (r : ℕ) : IsPreconnected (⋃ k, S (2*k+r)) := by
    apply IsPreconnected.iUnion_of_chain
    · intro k
      exact hS _
    · intro k
      change (S (2*k+r) ∩ S (2*(k+1)+r)).Nonempty
      rw [show 2 * (k + 1) + r = (2*k+r) + 2 by omega]
      exact hstep (2*k+r)
  have hce : IsPreconnected ({x} ∪ ⋃ k, S (2*k)) := by
    apply (hc 0).subset_closure
    · intro y hy
      exact Or.inr hy
    · intro y hy
      rcases hy with (rfl | hy)
      · exact heven
      · exact subset_closure hy
  have hco : IsPreconnected ({x} ∪ ⋃ k, S (2*k+1)) := by
    apply (hc 1).subset_closure
    · intro y hy
      exact Or.inr hy
    · intro y hy
      rcases hy with (rfl | hy)
      · exact hodd
      · exact subset_closure hy
  have hi : (({x} ∪ ⋃ k, S (2*k)) ∩ ({x} ∪ ⋃ k, S (2*k+1))).Nonempty :=
    ⟨x, Or.inl rfl, Or.inl rfl⟩
  have hu := IsPreconnected.union' hi hce hco
  convert hu using 1
  ext y
  simp only [mem_union, mem_singleton_iff, mem_iUnion]
  constructor
  · rintro (rfl | ⟨k, hk⟩)
    · exact Or.inl (Or.inl rfl)
    · obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' k
      · subst k
        exact Or.inl (Or.inr ⟨j, hk⟩)
      · subst k
        exact Or.inr (Or.inr ⟨j, hk⟩)
  · rintro ((rfl | ⟨k, hk⟩) | (rfl | ⟨k, hk⟩))
    · exact Or.inl rfl
    · exact Or.inr ⟨2*k, by simpa using hk⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨2*k+1, hk⟩

private theorem preconnected_twoStep_with_limit_of_tendsto
    (S : ℕ → Set ℝ) (x : ℝ) (u : ℕ → ℝ)
    (hS : ∀ k, IsPreconnected (S k))
    (hstep : ∀ k, (S k ∩ S (k+2)).Nonempty)
    (hu : ∀ k, u k ∈ S k)
    (hlim : Tendsto u atTop (nhds x)) :
    IsPreconnected ({x} ∪ ⋃ k, S k) := by
  apply preconnected_twoStep_with_limit S x hS hstep
  · exact mem_closure_iUnion_of_tendsto (fun k => S (2*k)) (fun k => u (2*k)) x
      (fun k => hu _) (tendsto_parity hlim 0)
  · exact mem_closure_iUnion_of_tendsto (fun k => S (2*k+1)) (fun k => u (2*k+1)) x
      (fun k => hu _) (tendsto_parity hlim 1)

set_option maxHeartbeats 800000 in
private theorem preconnected_stage_abstract
    (A B : ℕ → Set ℝ) (C : ℕ → ℕ → Set ℝ) (aux : Set ℝ)
    (aLim bLim : ℝ) (cLim : ℕ → ℝ)
    (aPoint bPoint : ℕ → ℝ) (cPoint : ℕ → ℕ → ℝ)
    (hApc : ∀ k, IsPreconnected (A k))
    (hBpc : ∀ k, IsPreconnected (B k))
    (hCpc : ∀ k p, IsPreconnected (C k p))
    (hauxpc : IsPreconnected aux)
    (hAA : ∀ k, (A k ∩ A (k+2)).Nonempty)
    (hCC : ∀ k p, (C k p ∩ C k (p+2)).Nonempty)
    (hBC1 : ∀ k, (B k ∩ C k 1).Nonempty)
    (hCB2 : ∀ k, (C k 0 ∩ B (k+2)).Nonempty)
    (hAB : (A 0 ∩ B 1).Nonempty)
    (haux : (aux ∩ B 0).Nonempty)
    (haPoint : ∀ k, aPoint k ∈ A k)
    (hbPoint : ∀ k, bPoint k ∈ B k)
    (hcPoint : ∀ k p, cPoint k p ∈ C k p)
    (haLim : Tendsto aPoint atTop (nhds aLim))
    (hbLim : Tendsto bPoint atTop (nhds bLim))
    (hcLim : ∀ k, Tendsto (cPoint k) atTop (nhds (cLim k))) :
    IsPreconnected {t |
      t = aLim ∨ t = bLim ∨ (∃ k, t = cLim k) ∨
      (∃ k, t ∈ A k) ∨ (∃ k, t ∈ B k) ∨
      (∃ k p, t ∈ C k p) ∨ t ∈ aux} := by
  have hAc : IsPreconnected ({aLim} ∪ ⋃ k, A k) :=
    preconnected_twoStep_with_limit_of_tendsto A aLim aPoint hApc hAA haPoint haLim
  have hCc (k : ℕ) : IsPreconnected ({cLim k} ∪ ⋃ p, C k p) :=
    preconnected_twoStep_with_limit_of_tendsto (C k) (cLim k) (cPoint k)
      (hCpc k) (hCC k) (hcPoint k) (hcLim k)
  let D : ℕ → Set ℝ := fun k => B k ∪ ({cLim k} ∪ ⋃ p, C k p)
  have hDpc (k : ℕ) : IsPreconnected (D k) := by
    apply IsPreconnected.union' _ (hBpc k) (hCc k)
    rcases hBC1 k with ⟨x, hxB, hxC⟩
    exact ⟨x, hxB, Or.inr (mem_iUnion.2 ⟨1, hxC⟩)⟩
  have hDD (k : ℕ) : (D k ∩ D (k+2)).Nonempty := by
    rcases hCB2 k with ⟨x, hxC, hxB⟩
    exact ⟨x, Or.inr (Or.inr (mem_iUnion.2 ⟨0, hxC⟩)), Or.inl hxB⟩
  have hbPointD (k : ℕ) : bPoint k ∈ D k := Or.inl (hbPoint k)
  have hDc : IsPreconnected ({bLim} ∪ ⋃ k, D k) :=
    preconnected_twoStep_with_limit_of_tendsto D bLim bPoint hDpc hDD hbPointD hbLim
  have hDaux : IsPreconnected (({bLim} ∪ ⋃ k, D k) ∪ aux) := by
    apply IsPreconnected.union' _ hDc hauxpc
    rcases haux with ⟨x, hxaux, hxB⟩
    exact ⟨x, Or.inr (mem_iUnion.2 ⟨0, Or.inl hxB⟩), hxaux⟩
  have hfinal : IsPreconnected
      (({aLim} ∪ ⋃ k, A k) ∪ (({bLim} ∪ ⋃ k, D k) ∪ aux)) := by
    apply IsPreconnected.union' _ hAc hDaux
    rcases hAB with ⟨x, hxA, hxB⟩
    exact ⟨x, Or.inr (mem_iUnion.2 ⟨0, hxA⟩),
      Or.inl (Or.inr (mem_iUnion.2 ⟨1, Or.inl hxB⟩))⟩
  convert hfinal using 1
  ext t
  simp only [D, mem_setOf_eq, mem_union, mem_singleton_iff, mem_iUnion]
  aesop

-- Exact topological assembly interface for the arithmetic seam proofs.
private theorem lower_initial_stage_preconnected_of_overlaps
    (hlimits : lowerInitialLimits) (n : ℕ)
    (hAA : ∀ k, (lowerFamilyH .A n k 0 ∩ lowerFamilyH .A n (k+2) 0).Nonempty)
    (hCC : ∀ k p, (lowerFamilyH .C n k p ∩ lowerFamilyH .C n k (p+2)).Nonempty)
    (hBC1 : ∀ k, (lowerFamilyH .B n k 0 ∩ lowerFamilyH .C n k 1).Nonempty)
    (hCB2 : ∀ k, (lowerFamilyH .C n k 0 ∩ lowerFamilyH .B n (k+2) 0).Nonempty)
    (hAB : (lowerFamilyH .A n 0 0 ∩ lowerFamilyH .B n 1 0).Nonempty)
    (haux : (lowerFamilyH .auxB n 0 0 ∩ lowerFamilyH .B n 0 0).Nonempty) :
    IsPreconnected (lowerInitialStage n) := by
  have hinf (f : LowerInitialFamily) (k p : ℕ) :
      sInf (lowerFamilyH f n k p) ∈ lowerFamilyH f n k p := by
    simp [lowerFamilyH]
  have h := preconnected_stage_abstract
    (fun k => lowerFamilyH .A n k 0)
    (fun k => lowerFamilyH .B n k 0)
    (fun k p => lowerFamilyH .C n k p)
    (lowerFamilyH .auxB n 0 0)
    (lowerFamilyLimitValue .A n 0) (lowerFamilyLimitValue .B n 0)
    (fun k => lowerFamilyLimitValue .C n k)
    (fun k => sInf (lowerFamilyH .A n k 0))
    (fun k => sInf (lowerFamilyH .B n k 0))
    (fun k p => sInf (lowerFamilyH .C n k p))
    (fun k => by exact isPreconnected_Icc)
    (fun k => by exact isPreconnected_Icc)
    (fun k p => by exact isPreconnected_Icc)
    (by exact isPreconnected_Icc)
    hAA hCC hBC1 hCB2 hAB haux
    (fun k => hinf .A k 0) (fun k => hinf .B k 0) (fun k p => hinf .C k p)
    (hlimits.1 n).1 (hlimits.2.1 n).1 (fun k => (hlimits.2.2.1 n k).1)
  simpa only [lowerInitialStage] using h

end Freiman

open Freiman

theorem solution
    (hseams : lowerInitialSeams) (hlimits : lowerInitialLimits) (n : ℕ) :
    IsPreconnected (lowerInitialStage n) := by
  exact Freiman.lower_initial_stage_preconnected_of_overlaps hlimits n
    (M7Stage13AC.lower_A_step_two hseams n)
    (M7Stage13AC.lower_C_step_two hseams n)
    (M7StageB.lower_B_C1_overlap hseams n)
    (M7StageB.lower_C0_B2_overlap hseams n)
    (Stage13Finite.a0_b1 hseams n)
    (Stage13Finite.aux_b0 hseams n)

#print axioms solution
