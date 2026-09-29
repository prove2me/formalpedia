-- Prove2me | solution 1 for CKLaneA3X.entryBounds_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T01:47:39.116568+00:00
-- url     : https://prove2.me/submissions/0895caaa-b76b-471b-9c68-65956477340d

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





















/-! ## SPoly -/



theorem SPoly.eval_nil (σ L : ℝ) : SPoly.eval σ L [] = 0 := rfl
theorem SPoly.eval_cons (σ L : ℝ) (m : ℕ × LPoly) (s : SPoly) :
    SPoly.eval σ L (m :: s) = σ ^ m.1 * LPoly.eval L m.2 + SPoly.eval σ L s := rfl





















/-! ## TPoly (dense in t) -/



































end CKLaneA3X



/-!
# CKLaneA3X.Bound — rigorous magnitude bounds for `LPoly`/`SPoly`/`TPoly`

`L` ranges over `[Llo, Lhi]` (Mathlib `Real.log_two_gt_d9`, `Real.log_two_lt_d9`), `|σ| ≤ 1/2`,
`0 ≤ t ≤ Tq`.  All bound functions are kernel-evaluable (`List.rec`/`Nat.rec`).
-/

namespace CKLaneA3X







theorem qpow_zero (x : ℚ) : qpow x 0 = 1 := rfl
theorem qpow_succ (x : ℚ) (k : ℕ) : qpow x (k + 1) = qpow x k * x := rfl

theorem qpow_eq (x : ℚ) (k : ℕ) : qpow x k = x ^ k := by
  induction k with
  | zero => simp [qpow_zero]
  | succ k ih => rw [qpow_succ, ih, pow_succ]



theorem Llo_pos : (0 : ℚ) < Llo := by norm_num [Llo]


theorem Lpow_spec {L : ℝ} (h1 : (Llo : ℝ) ≤ L) (h2 : L ≤ (Lhi : ℝ)) (c : ℤ) :
    ((Lpow c).1 : ℝ) ≤ L ^ c ∧ L ^ c ≤ ((Lpow c).2 : ℝ) := by
  have hlo : (0 : ℝ) < (Llo : ℝ) := by exact_mod_cast Llo_pos
  have hL : 0 < L := lt_of_lt_of_le hlo h1
  cases c with
  | ofNat k =>
    simp only [Lpow, qpow_eq, zpow_natCast, Int.ofNat_eq_natCast]
    push_cast
    exact ⟨pow_le_pow_left₀ hlo.le h1 k, pow_le_pow_left₀ hL.le h2 k⟩
  | negSucc k =>
    simp only [Lpow, qpow_eq, zpow_negSucc]
    push_cast
    have hhi : (0 : ℝ) < (Lhi : ℝ) := lt_of_lt_of_le hL h2
    constructor
    · rw [one_div, inv_pow]
      exact inv_anti₀ (pow_pos hL _) (pow_le_pow_left₀ hL.le h2 _)
    · rw [one_div, inv_pow]
      exact inv_anti₀ (pow_pos hlo _) (pow_le_pow_left₀ hlo.le h1 _)



theorem termIntv_spec {L : ℝ} (h1 : (Llo : ℝ) ≤ L) (h2 : L ≤ (Lhi : ℝ)) (c : ℤ) (q : ℚ) :
    ((termIntv c q).1 : ℝ) ≤ (q : ℝ) * L ^ c ∧ (q : ℝ) * L ^ c ≤ ((termIntv c q).2 : ℝ) := by
  obtain ⟨a, b⟩ := Lpow_spec h1 h2 c
  unfold termIntv
  split_ifs with hq
  · have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
    push_cast
    exact ⟨mul_le_mul_of_nonneg_left a hq', mul_le_mul_of_nonneg_left b hq'⟩
  · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.mp hq))
    push_cast
    exact ⟨mul_le_mul_of_nonpos_left b hq', mul_le_mul_of_nonpos_left a hq'⟩



theorem LPoly.intv_spec {L : ℝ} (h1 : (Llo : ℝ) ≤ L) (h2 : L ≤ (Lhi : ℝ)) (l : LPoly) :
    ((LPoly.intv l).1 : ℝ) ≤ LPoly.eval L l ∧ LPoly.eval L l ≤ ((LPoly.intv l).2 : ℝ) := by
  induction l with
  | nil => simp [LPoly.intv, LPoly.eval_nil]
  | cons m t ih =>
    obtain ⟨a, b⟩ := termIntv_spec h1 h2 m.1 m.2
    show (((termIntv m.1 m.2).1 + (LPoly.intv t).1 : ℚ) : ℝ) ≤ _ ∧
      _ ≤ (((termIntv m.1 m.2).2 + (LPoly.intv t).2 : ℚ) : ℝ)
    rw [LPoly.eval_cons]; push_cast
    exact ⟨add_le_add a ih.1, add_le_add b ih.2⟩



theorem LPoly.absB_spec {L : ℝ} (h1 : (Llo : ℝ) ≤ L) (h2 : L ≤ (Lhi : ℝ)) (l : LPoly) :
    |LPoly.eval L l| ≤ (LPoly.absB l : ℝ) := by
  obtain ⟨a, b⟩ := LPoly.intv_spec h1 h2 l
  unfold LPoly.absB
  push_cast
  rw [abs_le]
  constructor
  · have : -((|((LPoly.intv l).1 : ℝ)|)) ≤ ((LPoly.intv l).1 : ℝ) := neg_abs_le _
    have hm : (|((LPoly.intv l).1 : ℝ)|) ≤ max (|((LPoly.intv l).1 : ℝ)|) (|((LPoly.intv l).2 : ℝ)|) :=
      le_max_left _ _
    linarith
  · have : ((LPoly.intv l).2 : ℝ) ≤ (|((LPoly.intv l).2 : ℝ)|) := le_abs_self _
    have hm : (|((LPoly.intv l).2 : ℝ)|) ≤ max (|((LPoly.intv l).1 : ℝ)|) (|((LPoly.intv l).2 : ℝ)|) :=
      le_max_right _ _
    linarith



theorem SPoly.absB_spec {σ L : ℝ} (hσ : |σ| ≤ 1 / 2) (h1 : (Llo : ℝ) ≤ L) (h2 : L ≤ (Lhi : ℝ))
    (s : SPoly) : |SPoly.eval σ L s| ≤ (SPoly.absB s : ℝ) := by
  induction s with
  | nil => simp [SPoly.absB, SPoly.eval_nil]
  | cons m t ih =>
    show |SPoly.eval σ L (m :: t)| ≤ ((qpow (1 / 2) m.1 * LPoly.absB m.2 + SPoly.absB t : ℚ) : ℝ)
    rw [SPoly.eval_cons]
    push_cast
    rw [qpow_eq]; push_cast
    have hl := LPoly.absB_spec h1 h2 m.2
    have hp : |σ ^ m.1| ≤ (1 / 2 : ℝ) ^ m.1 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hσ _
    calc |σ ^ m.1 * LPoly.eval L m.2 + SPoly.eval σ L t|
        ≤ |σ ^ m.1 * LPoly.eval L m.2| + |SPoly.eval σ L t| := abs_add_le _ _
      _ = |σ ^ m.1| * |LPoly.eval L m.2| + |SPoly.eval σ L t| := by rw [abs_mul]
      _ ≤ (1 / 2 : ℝ) ^ m.1 * (LPoly.absB m.2 : ℝ) + (SPoly.absB t : ℝ) := by
          apply add_le_add _ ih
          exact mul_le_mul hp hl (abs_nonneg _) (by positivity)

/-! ## entry bounds for TPoly -/





theorem log2_lo : ((Llo : ℚ) : ℝ) ≤ Real.log 2 := by
  have := Real.log_two_gt_d9
  unfold Llo; push_cast; norm_num at this ⊢; linarith

theorem log2_hi : Real.log 2 ≤ ((Lhi : ℚ) : ℝ) := by
  have := Real.log_two_lt_d9
  unfold Lhi; push_cast; norm_num at this ⊢; linarith



/-! ## sums of entry bounds -/





















end CKLaneA3X



/-!
# CKLaneA3X.TMFun — functional Taylor-model operations (kernel-evaluable) with soundness

A `TMd` is `(P, r, n)`.  `Good f d` := `Encl f d.P d.r d.n ∧ 0 ≤ d.r`.
All remainders are rounded up to multiples of `2^-40` (`rup`) to keep rationals small.
-/

namespace CKLaneA3X







theorem le_rup (x : ℚ) : x ≤ rup x := by
  unfold rup
  rw [le_div_iff₀ (by norm_num)]
  exact Int.le_ceil _



theorem _root_.solution (P : TPoly) : EntryBnd P (entryBounds P) := by
  induction P with
  | nil => exact List.Forall₂.nil
  | cons s P ih =>
    refine List.Forall₂.cons ?_ ih
    intro σ hσ
    exact (SPoly.absB_spec hσ log2_lo log2_hi s).trans (by exact_mod_cast le_rup _)





























/-! ## Horner evaluation of a rational polynomial at a TM -/












/-! ## magnitude of a TM-enclosed function -/



end CKLaneA3X
