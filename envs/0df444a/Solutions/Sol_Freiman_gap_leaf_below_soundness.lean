-- Prove2me | solution 1 for Freiman.gap_leaf_below_soundness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:09:12.062197+00:00
-- url     : https://prove2.me/submissions/d32290ef-e7cb-4d2e-8e10-3989b4b9826b

import Definitions.Def_Freiman_gapCertificateData
import Theorems.Thm_Freiman_gap_cylinder_semantics

open Freiman

private theorem below_from_semantics (hsem : ∀ (a : ℤ → ℕ+) (i : ℤ) (s : GapState) (j : ℕ),
    gapDigits a → gapMatch a i s → j < s.word.length →
      (gapCylinderLower s.word j : ℝ) < localValue a (i+(j : ℤ)-(s.centre : ℤ)) ∧
      localValue a (i+(j : ℤ)-(s.centre : ℤ)) < (gapCylinderUpper s.word j : ℝ)) (lower upper : List GapRow) (mode : GapMode) (s : GapState) (a : ℤ → ℕ+) (i : ℤ) (hd : gapDigits a) (hc : gapCapped a) (hl : gapLowerValid a lower) (hu : gapUpperValid a upper) (hm : gapMatch a i s)  (hcheck : gapLeafCheck lower upper mode s (.below)) : gapModeOutcome mode a i := by
  have hlt := (hsem a i s s.centre hd hm hm.1).2
  have hidx : i + (s.centre : ℤ) - (s.centre : ℤ) = i := by omega
  rw [hidx] at hlt
  cases mode with
  | forbidden => exact hcheck.elim
  | upper cut =>
    change localValue a i < (cut : ℝ)
    have hle : (gapCylinderUpper s.word s.centre : ℝ) ≤ (cut : ℝ) := by exact_mod_cast hcheck
    exact hlt.trans_le hle
  | reduction =>
    intro hw
    have hle : (gapCylinderUpper s.word s.centre : ℝ) ≤ gapWindow := by
      change gapCylinderUpper s.word s.centre ≤ 2263914769 / 500000000 at hcheck
      simpa only [Rat.cast_div, Rat.cast_ofNat, gapWindow] using (Rat.cast_le (K := ℝ)).2 hcheck
    exact False.elim (not_lt_of_ge (hlt.trans_le hle).le hw)

theorem solution (lower upper : List GapRow) (mode : GapMode) (s : GapState)
    (a : ℤ → ℕ+) (i : ℤ) (hd : gapDigits a) (hc : gapCapped a)
    (hl : gapLowerValid a lower) (hu : gapUpperValid a upper) (hm : gapMatch a i s)
    (hcheck : gapLeafCheck lower upper mode s (.below)) : gapModeOutcome mode a i := by
  exact below_from_semantics gap_cylinder_semantics lower upper mode s a i hd hc hl hu hm hcheck
