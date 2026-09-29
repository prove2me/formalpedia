-- Prove2me | solution 1 for CKLaneA3X.Encl.mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T01:47:38.136076+00:00
-- url     : https://prove2.me/submissions/1b917aa3-8144-47d1-8999-e1feea0ee6cf

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_enclosure

open CKLaneA3X



/-!
# CKLaneA3X.Poly — exact sparse polynomials for the high-u Taylor-model checker

Three-level representation (all kernel-evaluable via `List.rec`; no well-founded recursion):
* `LPoly` : Laurent polynomial in `L` (intended `L = log 2`): list of `(c, q)` meaning `q * L^c`.
* `SPoly` : polynomial in `σ` with `LPoly` coefficients: list of `(b, l)` meaning `σ^b * l`.
* `TPoly` : dense polynomial in `t` with `SPoly` coefficients: `[s₀, s₁, …]` means `s₀ + t*(s₁ + t*(…))`.

Only `eval`-soundness matters for the checker; sortedness is used for compactness but never for
soundness.
-/

namespace CKLaneA3X





/-! ## LPoly -/



theorem LPoly.eval_nil (L : ℝ) : LPoly.eval L [] = 0 := rfl
theorem LPoly.eval_cons (L : ℝ) (m : ℤ × ℚ) (l : LPoly) :
    LPoly.eval L (m :: l) = (m.2 : ℝ) * L ^ m.1 + LPoly.eval L l := rfl



theorem LPoly.add_nil (l2 : LPoly) : LPoly.add [] l2 = l2 := rfl
theorem LPoly.add_cons_nil (m1 : ℤ × ℚ) (t1 : LPoly) : LPoly.add (m1 :: t1) [] = m1 :: t1 := rfl
theorem LPoly.add_cons_cons (m1 m2 : ℤ × ℚ) (t1 t2 : LPoly) :
    LPoly.add (m1 :: t1) (m2 :: t2) =
      if m1.1 < m2.1 then m1 :: LPoly.add t1 (m2 :: t2)
      else if m2.1 < m1.1 then m2 :: LPoly.add (m1 :: t1) t2
      else if m1.2 + m2.2 = 0 then LPoly.add t1 t2 else (m1.1, m1.2 + m2.2) :: LPoly.add t1 t2 :=
  rfl

theorem LPoly.eval_add (L : ℝ) (hL : L ≠ 0) (l1 l2 : LPoly) :
    LPoly.eval L (LPoly.add l1 l2) = LPoly.eval L l1 + LPoly.eval L l2 := by
  induction l1 generalizing l2 with
  | nil => simp [LPoly.add_nil, LPoly.eval_nil]
  | cons m1 t1 ih1 =>
    induction l2 with
    | nil => simp [LPoly.add_cons_nil, LPoly.eval_nil]
    | cons m2 t2 ih2 =>
      rw [LPoly.add_cons_cons]
      split_ifs with h1 h2 h3
      · rw [LPoly.eval_cons, ih1, LPoly.eval_cons, LPoly.eval_cons]; ring
      · rw [LPoly.eval_cons, ih2]; simp only [LPoly.eval_cons]; ring
      · have he : m1.1 = m2.1 := by omega
        rw [ih1, LPoly.eval_cons, LPoly.eval_cons, he]
        have : ((m1.2 : ℝ) + (m2.2 : ℝ)) = 0 := by exact_mod_cast h3
        linear_combination (-(L ^ m2.1)) * this
      · have he : m1.1 = m2.1 := by omega
        rw [LPoly.eval_cons, ih1, LPoly.eval_cons, LPoly.eval_cons, he]
        push_cast; ring



theorem LPoly.eval_mulMono (L : ℝ) (hL : L ≠ 0) (c : ℤ) (q : ℚ) (l : LPoly) :
    LPoly.eval L (LPoly.mulMono c q l) = (q : ℝ) * L ^ c * LPoly.eval L l := by
  induction l with
  | nil => simp [LPoly.mulMono, LPoly.eval_nil]
  | cons m t ih =>
    show (((q * m.2 : ℚ)) : ℝ) * L ^ (c + m.1) + LPoly.eval L (LPoly.mulMono c q t) = _
    rw [ih, LPoly.eval_cons, zpow_add₀ hL]; push_cast; ring



theorem LPoly.eval_mul (L : ℝ) (hL : L ≠ 0) (l1 l2 : LPoly) :
    LPoly.eval L (LPoly.mul l1 l2) = LPoly.eval L l1 * LPoly.eval L l2 := by
  induction l1 with
  | nil => simp [LPoly.mul, LPoly.eval_nil]
  | cons m t ih =>
    show LPoly.eval L (LPoly.add (LPoly.mulMono m.1 m.2 l2) (LPoly.mul t l2)) = _
    rw [LPoly.eval_add L hL, LPoly.eval_mulMono L hL, ih, LPoly.eval_cons]; ring





/-! ## SPoly -/



theorem SPoly.eval_nil (σ L : ℝ) : SPoly.eval σ L [] = 0 := rfl
theorem SPoly.eval_cons (σ L : ℝ) (m : ℕ × LPoly) (s : SPoly) :
    SPoly.eval σ L (m :: s) = σ ^ m.1 * LPoly.eval L m.2 + SPoly.eval σ L s := rfl



theorem SPoly.add_nil (s2 : SPoly) : SPoly.add [] s2 = s2 := rfl
theorem SPoly.add_cons_nil (m1 : ℕ × LPoly) (t1 : SPoly) : SPoly.add (m1 :: t1) [] = m1 :: t1 := rfl
theorem SPoly.add_cons_cons (m1 m2 : ℕ × LPoly) (t1 t2 : SPoly) :
    SPoly.add (m1 :: t1) (m2 :: t2) =
      if m1.1 < m2.1 then m1 :: SPoly.add t1 (m2 :: t2)
      else if m2.1 < m1.1 then m2 :: SPoly.add (m1 :: t1) t2
      else if LPoly.add m1.2 m2.2 = [] then SPoly.add t1 t2
      else (m1.1, LPoly.add m1.2 m2.2) :: SPoly.add t1 t2 :=
  rfl

theorem SPoly.eval_add (σ L : ℝ) (hL : L ≠ 0) (s1 s2 : SPoly) :
    SPoly.eval σ L (SPoly.add s1 s2) = SPoly.eval σ L s1 + SPoly.eval σ L s2 := by
  induction s1 generalizing s2 with
  | nil => simp [SPoly.add_nil, SPoly.eval_nil]
  | cons m1 t1 ih1 =>
    induction s2 with
    | nil => simp [SPoly.add_cons_nil, SPoly.eval_nil]
    | cons m2 t2 ih2 =>
      rw [SPoly.add_cons_cons]
      split_ifs with h1 h2 h3
      · rw [SPoly.eval_cons, ih1, SPoly.eval_cons, SPoly.eval_cons]; ring
      · rw [SPoly.eval_cons, ih2]; simp only [SPoly.eval_cons]; ring
      · have he : m1.1 = m2.1 := by omega
        have hz : LPoly.eval L (LPoly.add m1.2 m2.2) = 0 := by rw [h3]; rfl
        rw [LPoly.eval_add L hL] at hz
        rw [ih1, SPoly.eval_cons, SPoly.eval_cons, he]
        linear_combination (-(σ ^ m2.1)) * hz
      · have he : m1.1 = m2.1 := by omega
        rw [SPoly.eval_cons, ih1, SPoly.eval_cons, SPoly.eval_cons, LPoly.eval_add L hL, he]
        ring



theorem SPoly.eval_mulMono (σ L : ℝ) (hL : L ≠ 0) (b : ℕ) (l : LPoly) (s : SPoly) :
    SPoly.eval σ L (SPoly.mulMono b l s) = σ ^ b * LPoly.eval L l * SPoly.eval σ L s := by
  induction s with
  | nil => simp [SPoly.mulMono, SPoly.eval_nil]
  | cons m t ih =>
    show SPoly.eval σ L
        (if LPoly.mul l m.2 = [] then SPoly.mulMono b l t
         else (b + m.1, LPoly.mul l m.2) :: SPoly.mulMono b l t) = _
    split_ifs with h
    · have hz : LPoly.eval L (LPoly.mul l m.2) = 0 := by rw [h]; rfl
      rw [LPoly.eval_mul L hL] at hz
      rw [ih, SPoly.eval_cons]
      linear_combination (-(σ ^ b * σ ^ m.1)) * hz
    · rw [SPoly.eval_cons, ih, SPoly.eval_cons, LPoly.eval_mul L hL, pow_add]; ring



theorem SPoly.eval_mul (σ L : ℝ) (hL : L ≠ 0) (s1 s2 : SPoly) :
    SPoly.eval σ L (SPoly.mul s1 s2) = SPoly.eval σ L s1 * SPoly.eval σ L s2 := by
  induction s1 with
  | nil => simp [SPoly.mul, SPoly.eval_nil]
  | cons m t ih =>
    show SPoly.eval σ L (SPoly.add (SPoly.mulMono m.1 m.2 s2) (SPoly.mul t s2)) = _
    rw [SPoly.eval_add σ L hL, SPoly.eval_mulMono σ L hL, ih, SPoly.eval_cons]; ring





/-! ## TPoly (dense in t) -/



theorem TPoly.eval_nil (t σ L : ℝ) : TPoly.eval t σ L [] = 0 := rfl
theorem TPoly.eval_cons (t σ L : ℝ) (s : SPoly) (P : TPoly) :
    TPoly.eval t σ L (s :: P) = SPoly.eval σ L s + t * TPoly.eval t σ L P := rfl



theorem TPoly.add_nil (P2 : TPoly) : TPoly.add [] P2 = P2 := rfl
theorem TPoly.add_cons_nil (s1 : SPoly) (t1 : TPoly) : TPoly.add (s1 :: t1) [] = s1 :: t1 := rfl
theorem TPoly.add_cons_cons (s1 s2 : SPoly) (t1 t2 : TPoly) :
    TPoly.add (s1 :: t1) (s2 :: t2) = SPoly.add s1 s2 :: TPoly.add t1 t2 := rfl

theorem TPoly.eval_add (t σ L : ℝ) (hL : L ≠ 0) (P1 P2 : TPoly) :
    TPoly.eval t σ L (TPoly.add P1 P2) = TPoly.eval t σ L P1 + TPoly.eval t σ L P2 := by
  induction P1 generalizing P2 with
  | nil => simp [TPoly.add_nil, TPoly.eval_nil]
  | cons s1 t1 ih =>
    cases P2 with
    | nil => simp [TPoly.add_cons_nil, TPoly.eval_nil]
    | cons s2 t2 =>
      rw [TPoly.add_cons_cons, TPoly.eval_cons, TPoly.eval_cons, TPoly.eval_cons, ih,
        SPoly.eval_add σ L hL]
      ring













theorem TPoly.take_nil (k : ℕ) : TPoly.take [] k = [] := rfl
theorem TPoly.take_zero (P : TPoly) : TPoly.take P 0 = [] := by cases P <;> rfl
theorem TPoly.take_cons_succ (s : SPoly) (P : TPoly) (k : ℕ) :
    TPoly.take (s :: P) (k + 1) = s :: TPoly.take P k := rfl
theorem TPoly.drop_nil (k : ℕ) : TPoly.drop [] k = [] := rfl
theorem TPoly.drop_zero (P : TPoly) : TPoly.drop P 0 = P := by cases P <;> rfl
theorem TPoly.drop_cons_succ (s : SPoly) (P : TPoly) (k : ℕ) :
    TPoly.drop (s :: P) (k + 1) = TPoly.drop P k := rfl

theorem TPoly.eval_take_drop (t σ L : ℝ) (P : TPoly) (k : ℕ) :
    TPoly.eval t σ L P = TPoly.eval t σ L (TPoly.take P k) + t ^ k * TPoly.eval t σ L (TPoly.drop P k) := by
  induction P generalizing k with
  | nil => simp [TPoly.take_nil, TPoly.drop_nil, TPoly.eval_nil]
  | cons s P ih =>
    cases k with
    | zero => simp [TPoly.take_zero, TPoly.drop_zero, TPoly.eval_nil]
    | succ k =>
      rw [TPoly.take_cons_succ, TPoly.drop_cons_succ, TPoly.eval_cons, TPoly.eval_cons, ih k]
      ring

end CKLaneA3X



/-!
# CKLaneA3X.Bound — rigorous magnitude bounds for `LPoly`/`SPoly`/`TPoly`

`L` ranges over `[Llo, Lhi]` (Mathlib `Real.log_two_gt_d9`, `Real.log_two_lt_d9`), `|σ| ≤ 1/2`,
`0 ≤ t ≤ Tq`.  All bound functions are kernel-evaluable (`List.rec`/`Nat.rec`).
-/

namespace CKLaneA3X



































/-! ## entry bounds for TPoly -/











/-! ## sums of entry bounds -/





theorem ldrop_zero (β : List ℚ) : ldrop β 0 = β := by cases β <;> rfl
theorem ldrop_nil (k : ℕ) : ldrop [] k = [] := rfl
theorem ldrop_cons_succ (b : ℚ) (β : List ℚ) (k : ℕ) : ldrop (b :: β) (k + 1) = ldrop β k := rfl



theorem bsum_nonneg (β : List ℚ) (h : Nonneg β) : 0 ≤ bsum β := by
  induction β with
  | nil => simp [bsum]
  | cons b β ih =>
    show 0 ≤ b + Tq * bsum β
    have hb : 0 ≤ b := h b (List.mem_cons_self)
    have hr : 0 ≤ bsum β := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have : (0 : ℚ) ≤ Tq := by norm_num [Tq]
    positivity

theorem EntryBnd.nonneg {P : TPoly} {β : List ℚ} (h : EntryBnd P β) : Nonneg β := by
  induction h with
  | nil => intro b hb; simp at hb
  | cons hsb _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · have := hsb 0 (by norm_num)
      have h0 : (0 : ℝ) ≤ _ := (abs_nonneg _).trans this
      exact_mod_cast h0
    · exact ih b hb'

theorem ldrop_nonneg (β : List ℚ) (h : Nonneg β) (k : ℕ) : Nonneg (ldrop β k) := by
  induction β generalizing k with
  | nil => simp [ldrop_nil, Nonneg]
  | cons b β ih =>
    cases k with
    | zero => rw [ldrop_zero]; exact h
    | succ k =>
      rw [ldrop_cons_succ]
      exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) k

/-- evaluation bound: `|P(t)| ≤ Σ β_i t^i ≤ bsum β` for `0 ≤ t ≤ T`. -/
theorem EntryBnd.eval_le {P : TPoly} {β : List ℚ} (h : EntryBnd P β) {t σ : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ (Tq : ℝ)) (hσ : |σ| ≤ 1 / 2) :
    |TPoly.eval t σ (Real.log 2) P| ≤ (bsum β : ℝ) := by
  induction h with
  | nil => simp [TPoly.eval_nil, bsum]
  | @cons s b P' β' hsb _ ih =>
    rw [TPoly.eval_cons]
    show _ ≤ ((b + Tq * bsum β' : ℚ) : ℝ)
    push_cast
    have h1 := hsb σ hσ
    have hnn : (0 : ℝ) ≤ bsum β' := by
      exact (abs_nonneg _).trans ih
    calc |SPoly.eval σ (Real.log 2) s + t * TPoly.eval t σ (Real.log 2) P'|
        ≤ |SPoly.eval σ (Real.log 2) s| + |t| * |TPoly.eval t σ (Real.log 2) P'| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ (b : ℝ) + (Tq : ℝ) * (bsum β' : ℝ) := by
          apply add_le_add h1
          rw [abs_of_nonneg ht0]
          exact mul_le_mul ht ih (abs_nonneg _) (by norm_num [Tq])

theorem EntryBnd.drop {P : TPoly} {β : List ℚ} (h : EntryBnd P β) (k : ℕ) :
    EntryBnd (TPoly.drop P k) (ldrop β k) := by
  induction h generalizing k with
  | nil => exact List.Forall₂.nil
  | @cons s b P' β' hsb hrest ih =>
    cases k with
    | zero => rw [TPoly.drop_zero, ldrop_zero]; exact List.Forall₂.cons hsb hrest
    | succ k => rw [TPoly.drop_cons_succ, ldrop_cons_succ]; exact ih k

end CKLaneA3X



/-!
# CKLaneA3X.TM — Taylor-model enclosures in `t` over the high-u domain

Domain: `0 < t ≤ 7/50`, `0 < ρ < 1`; polynomials are evaluated at `σ = ρ - 1/2`, `L = log 2`.
`Encl f P r n` : `|f t ρ - P(t, ρ-1/2, log 2)| ≤ r * t^n` on the domain.
-/

namespace CKLaneA3X



theorem Dom.sigma {t ρ : ℝ} (h : Dom t ρ) : |ρ - 1 / 2| ≤ 1 / 2 := by
  obtain ⟨_, _, h3, h4⟩ := h
  rw [abs_le]; constructor <;> linarith

theorem Tq_pos : (0 : ℝ) < (Tq : ℝ) := by norm_num [Tq]











theorem pow_le_T_pow {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (Tq : ℝ)) {a n : ℕ} (han : n ≤ a) :
    t ^ a ≤ (Tq : ℝ) ^ (a - n) * t ^ n := by
  have : t ^ a = t ^ (a - n) * t ^ n := by rw [← pow_add]; congr 1; omega
  rw [this]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0 ht _) (pow_nonneg ht0 _)







/-! ## zero prefix (valuation) -/



theorem zeroPrefix_eval (t σ L : ℝ) (P : TPoly) (v : ℕ) (h : zeroPrefix P v = true) :
    TPoly.eval t σ L P = t ^ v * TPoly.eval t σ L (TPoly.drop P v) := by
  induction P generalizing v with
  | nil => simp [TPoly.eval_nil, TPoly.drop_nil]
  | cons s P ih =>
    cases v with
    | zero => simp [TPoly.drop_zero]
    | succ v =>
      have h' : s.isEmpty = true ∧ zeroPrefix P v = true := by
        have : zeroPrefix (s :: P) (v + 1) = (s.isEmpty && zeroPrefix P v) := rfl
        rw [this] at h; simpa using h
      have hs : s = [] := List.isEmpty_iff.mp h'.1
      rw [TPoly.drop_cons_succ, TPoly.eval_cons, hs, SPoly.eval_nil, ih v h'.2]
      ring

/-- magnitude bound with valuation -/
theorem EntryBnd.eval_le_val {P : TPoly} {β : List ℚ} (h : EntryBnd P β) {v : ℕ}
    (hz : zeroPrefix P v = true) {t σ : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (Tq : ℝ)) (hσ : |σ| ≤ 1 / 2) :
    |TPoly.eval t σ (Real.log 2) P| ≤ t ^ v * (bsum (ldrop β v) : ℝ) := by
  rw [zeroPrefix_eval t σ _ P v hz, abs_mul, abs_of_nonneg (pow_nonneg ht0 _)]
  exact mul_le_mul_of_nonneg_left ((h.drop v).eval_le ht0 ht hσ) (pow_nonneg ht0 _)

/-! ## truncated product soundness -/

theorem scaleSTake_eval (t σ L : ℝ) (hL : L ≠ 0) (s : SPoly) (Q : TPoly) (k : ℕ) :
    TPoly.eval t σ L (TPoly.scaleSTake s Q k) = SPoly.eval σ L s * TPoly.eval t σ L (TPoly.take Q k) := by
  induction Q generalizing k with
  | nil =>
    show TPoly.eval t σ L [] = _
    simp [TPoly.take_nil, TPoly.eval_nil]
  | cons p Q ih =>
    cases k with
    | zero =>
      show TPoly.eval t σ L [] = _
      simp [TPoly.take_zero, TPoly.eval_nil]
    | succ k =>
      show TPoly.eval t σ L (SPoly.mul s p :: TPoly.scaleSTake s Q k) = _
      rw [TPoly.eval_cons, ih k, TPoly.take_cons_succ, TPoly.eval_cons, SPoly.eval_mul σ L hL]
      ring



theorem mulT_nil (Q : TPoly) (n : ℕ) : TPoly.mulT [] Q n = [] := rfl
theorem mulT_cons_zero (s : SPoly) (P Q : TPoly) : TPoly.mulT (s :: P) Q 0 = [] := rfl
theorem mulT_cons_succ (s : SPoly) (P Q : TPoly) (n : ℕ) :
    TPoly.mulT (s :: P) Q (n + 1) = TPoly.add (TPoly.scaleSTake s Q (n + 1)) ([] :: TPoly.mulT P Q n) :=
  rfl

theorem mulT_err {P Q : TPoly} {β γ : List ℚ} (hP : EntryBnd P β) (hQ : EntryBnd Q γ) (n : ℕ)
    {t σ : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (Tq : ℝ)) (hσ : |σ| ≤ 1 / 2) :
    |TPoly.eval t σ (Real.log 2) P * TPoly.eval t σ (Real.log 2) Q -
      TPoly.eval t σ (Real.log 2) (TPoly.mulT P Q n)| ≤ t ^ n * (HB β γ n : ℝ) := by
  have hL : Real.log 2 ≠ 0 := by positivity
  induction hP generalizing n with
  | nil => simp [mulT_nil, TPoly.eval_nil, HB]
  | @cons s b P' β' hsb hrest ih =>
    cases n with
    | zero =>
      rw [mulT_cons_zero, TPoly.eval_nil, sub_zero, pow_zero, one_mul, abs_mul]
      show _ ≤ ((bsum (b :: β') * bsum γ : ℚ) : ℝ)
      push_cast
      have hPc : EntryBnd (s :: P') (b :: β') := List.Forall₂.cons hsb hrest
      exact mul_le_mul (hPc.eval_le ht0 ht hσ) (hQ.eval_le ht0 ht hσ)
        (abs_nonneg _) ((abs_nonneg _).trans (hPc.eval_le ht0 ht hσ))
    | succ n =>
      rw [mulT_cons_succ, TPoly.eval_add _ _ _ hL, scaleSTake_eval _ _ _ hL, TPoly.eval_cons,
        TPoly.eval_cons (s := []), SPoly.eval_nil]
      have hsplit := TPoly.eval_take_drop t σ (Real.log 2) Q (n + 1)
      have ih' := ih n
      show _ ≤ t ^ (n + 1) * ((b * bsum (ldrop γ (n + 1)) + HB β' γ n : ℚ) : ℝ)
      push_cast
      set p := TPoly.eval t σ (Real.log 2) P'
      set q := TPoly.eval t σ (Real.log 2) Q
      set qt := TPoly.eval t σ (Real.log 2) (TPoly.take Q (n + 1))
      set qd := TPoly.eval t σ (Real.log 2) (TPoly.drop Q (n + 1))
      set m := TPoly.eval t σ (Real.log 2) (TPoly.mulT P' Q n)
      set sv := SPoly.eval σ (Real.log 2) s
      have hkey : (sv + t * p) * q - (sv * qt + (0 + t * m)) = sv * t ^ (n + 1) * qd + t * (p * q - m) := by
        rw [hsplit]; ring
      rw [hkey]
      have h1 : |sv| ≤ b := hsb σ hσ
      have h2 : |qd| ≤ bsum (ldrop γ (n + 1)) := (hQ.drop (n + 1)).eval_le ht0 ht hσ
      have hb0 : (0 : ℝ) ≤ b := (abs_nonneg _).trans h1
      calc |sv * t ^ (n + 1) * qd + t * (p * q - m)|
          ≤ |sv * t ^ (n + 1) * qd| + |t * (p * q - m)| := abs_add_le _ _
        _ = |sv| * t ^ (n + 1) * |qd| + t * |p * q - m| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht0 _), abs_of_nonneg ht0]
        _ ≤ b * t ^ (n + 1) * bsum (ldrop γ (n + 1)) + t * (t ^ n * HB β' γ n) := by
            apply add_le_add
            · apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (pow_nonneg ht0 _)) h2 (abs_nonneg _)
              exact mul_nonneg hb0 (pow_nonneg ht0 _)
            · exact mul_le_mul_of_nonneg_left ih' ht0
        _ = t ^ (n + 1) * (b * bsum (ldrop γ (n + 1)) + HB β' γ n) := by ring

theorem _root_.solution {f g : ℝ → ℝ → ℝ} {P Q R : TPoly} {β γ : List ℚ} {r1 r2 r : ℚ}
    {n1 n2 v1 v2 n : ℕ}
    (hf : Encl f P r1 n1) (bP : EntryBnd P β) (hg : Encl g Q r2 n2) (bQ : EntryBnd Q γ)
    (hz1 : zeroPrefix P v1 = true) (hz2 : zeroPrefix Q v2 = true)
    (hv1 : v1 ≤ n1) (hn1 : n ≤ v1 + n2) (hn2 : n ≤ v2 + n1)
    (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2)
    (hR : TPoly.mulT P Q n = R)
    (hrem : HB β γ n + (bsum (ldrop β v1) + r1 * Tq ^ (n1 - v1)) * r2 * Tq ^ (v1 + n2 - n)
        + bsum (ldrop γ v2) * r1 * Tq ^ (v2 + n1 - n) ≤ r) :
    Encl (fun t ρ => f t ρ * g t ρ) R r n := by
  intro t ρ hd
  have ht0 : 0 ≤ t := hd.1.le
  have ht := hd.2.1
  have hσ := hd.sigma
  set p := ev P t ρ
  set q := ev Q t ρ
  have e1 := hf t ρ hd
  have e2 := hg t ρ hd
  have hm := mulT_err bP bQ n ht0 ht hσ
  rw [← hR]
  change |f t ρ * g t ρ - TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.mulT P Q n)| ≤ _
  have hp : |p| ≤ t ^ v1 * (bsum (ldrop β v1) : ℝ) := bP.eval_le_val hz1 ht0 ht hσ
  have hq : |q| ≤ t ^ v2 * (bsum (ldrop γ v2) : ℝ) := bQ.eval_le_val hz2 ht0 ht hσ
  have hr1' : (0 : ℝ) ≤ r1 := by exact_mod_cast hr1
  have hr2' : (0 : ℝ) ≤ r2 := by exact_mod_cast hr2
  have hB1 : (0 : ℝ) ≤ bsum (ldrop β v1) := by exact_mod_cast bsum_nonneg _ (ldrop_nonneg _ bP.nonneg _)
  have hB2 : (0 : ℝ) ≤ bsum (ldrop γ v2) := by exact_mod_cast bsum_nonneg _ (ldrop_nonneg _ bQ.nonneg _)
  -- |f| ≤ t^v1 * K1
  have hf_abs : |f t ρ| ≤ t ^ v1 * ((bsum (ldrop β v1) : ℝ) + r1 * (Tq : ℝ) ^ (n1 - v1)) := by
    have h3 : |f t ρ| ≤ |p| + r1 * t ^ n1 := by
      have := abs_sub_abs_le_abs_sub (f t ρ) p
      linarith
    have h4 : t ^ n1 ≤ (Tq : ℝ) ^ (n1 - v1) * t ^ v1 := pow_le_T_pow ht0 ht hv1
    nlinarith [pow_nonneg ht0 v1, mul_le_mul_of_nonneg_left h4 hr1']
  have hsplit : f t ρ * g t ρ - TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.mulT P Q n) =
      f t ρ * (g t ρ - q) + q * (f t ρ - p) + (p * q - TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.mulT P Q n)) := by
    ring
  rw [hsplit]
  have hA : |f t ρ * (g t ρ - q)| ≤ ((bsum (ldrop β v1) : ℝ) + r1 * (Tq : ℝ) ^ (n1 - v1)) * r2 * (Tq : ℝ) ^ (v1 + n2 - n) * t ^ n := by
    rw [abs_mul]
    have h5 : t ^ (v1 + n2) ≤ (Tq : ℝ) ^ (v1 + n2 - n) * t ^ n := pow_le_T_pow ht0 ht hn1
    have hK : (0 : ℝ) ≤ (bsum (ldrop β v1) : ℝ) + r1 * (Tq : ℝ) ^ (n1 - v1) := by
      have : (0 : ℝ) ≤ (Tq : ℝ) ^ (n1 - v1) := pow_nonneg Tq_pos.le _
      positivity
    calc |f t ρ| * |g t ρ - q| ≤ (t ^ v1 * ((bsum (ldrop β v1) : ℝ) + r1 * (Tq : ℝ) ^ (n1 - v1))) * (r2 * t ^ n2) :=
          mul_le_mul hf_abs e2 (abs_nonneg _) (by positivity)
      _ = ((bsum (ldrop β v1) : ℝ) + r1 * (Tq : ℝ) ^ (n1 - v1)) * r2 * t ^ (v1 + n2) := by rw [pow_add]; ring
      _ ≤ ((bsum (ldrop β v1) : ℝ) + r1 * (Tq : ℝ) ^ (n1 - v1)) * r2 * ((Tq : ℝ) ^ (v1 + n2 - n) * t ^ n) :=
          mul_le_mul_of_nonneg_left h5 (mul_nonneg hK hr2')
      _ = _ := by ring
  have hB : |q * (f t ρ - p)| ≤ (bsum (ldrop γ v2) : ℝ) * r1 * (Tq : ℝ) ^ (v2 + n1 - n) * t ^ n := by
    rw [abs_mul]
    have h6 : t ^ (v2 + n1) ≤ (Tq : ℝ) ^ (v2 + n1 - n) * t ^ n := pow_le_T_pow ht0 ht hn2
    calc |q| * |f t ρ - p| ≤ (t ^ v2 * (bsum (ldrop γ v2) : ℝ)) * (r1 * t ^ n1) :=
          mul_le_mul hq e1 (abs_nonneg _) (by positivity)
      _ = (bsum (ldrop γ v2) : ℝ) * r1 * t ^ (v2 + n1) := by rw [pow_add]; ring
      _ ≤ (bsum (ldrop γ v2) : ℝ) * r1 * ((Tq : ℝ) ^ (v2 + n1 - n) * t ^ n) :=
          mul_le_mul_of_nonneg_left h6 (mul_nonneg hB2 hr1')
      _ = _ := by ring
  have hC : |p * q - TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.mulT P Q n)| ≤ t ^ n * (HB β γ n : ℝ) := hm
  have hrem' : (HB β γ n : ℝ) + ((bsum (ldrop β v1) : ℝ) + r1 * (Tq : ℝ) ^ (n1 - v1)) * r2 * (Tq : ℝ) ^ (v1 + n2 - n)
      + (bsum (ldrop γ v2) : ℝ) * r1 * (Tq : ℝ) ^ (v2 + n1 - n) ≤ r := by exact_mod_cast hrem
  calc |f t ρ * (g t ρ - q) + q * (f t ρ - p) + (p * q - TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.mulT P Q n))|
      ≤ |f t ρ * (g t ρ - q)| + |q * (f t ρ - p)| + |p * q - TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.mulT P Q n)| :=
        abs_add_three _ _ _
    _ ≤ _ + _ + _ := add_le_add (add_le_add hA hB) hC
    _ = ((HB β γ n : ℝ) + ((bsum (ldrop β v1) : ℝ) + r1 * (Tq : ℝ) ^ (n1 - v1)) * r2 * (Tq : ℝ) ^ (v1 + n2 - n)
      + (bsum (ldrop γ v2) : ℝ) * r1 * (Tq : ℝ) ^ (v2 + n1 - n)) * t ^ n := by ring
    _ ≤ r * t ^ n := mul_le_mul_of_nonneg_right hrem' (pow_nonneg ht0 _)

/-! ## division by t, truncation -/





end CKLaneA3X
