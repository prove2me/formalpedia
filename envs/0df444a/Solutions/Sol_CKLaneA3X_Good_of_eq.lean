-- Prove2me | solution 1 for CKLaneA3X.Good.of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T01:47:39.7712+00:00
-- url     : https://prove2.me/submissions/7f95c92b-fea6-41ee-805b-6275cc9f1662

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
# CKLaneA3X.TM — Taylor-model enclosures in `t` over the high-u domain

Domain: `0 < t ≤ 7/50`, `0 < ρ < 1`; polynomials are evaluated at `σ = ρ - 1/2`, `L = log 2`.
`Encl f P r n` : `|f t ρ - P(t, ρ-1/2, log 2)| ≤ r * t^n` on the domain.
-/

namespace CKLaneA3X















theorem Encl.weaken {f : ℝ → ℝ → ℝ} {P : TPoly} {r r' : ℚ} {n : ℕ}
    (h : Encl f P r n) (hr : r ≤ r') : Encl f P r' n := by
  intro t ρ hd
  have ht : 0 ≤ t ^ n := pow_nonneg hd.1.le n
  exact (h t ρ hd).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hr) ht)









/-! ## zero prefix (valuation) -/







/-! ## truncated product soundness -/













/-! ## division by t, truncation -/





end CKLaneA3X



/-!
# CKLaneA3X.SeriesTM — TM-level series, reciprocal and exact-polynomial helpers
-/

namespace CKLaneA3X

open Finset

theorem _root_.solution {f : ℝ → ℝ → ℝ} {d : TMd} (h : Good f d) {P : TPoly} {r : ℚ} {n : ℕ}
    (hP : d.P = P) (hn : d.n = n) (hr : d.r ≤ r) : Good f ⟨P, r, n⟩ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, le_trans h2 hr⟩
  have := Encl.weaken h1 hr
  rw [hP, hn] at this
  exact this





/-! ## coefficient lists -/












/-! ## series TMs -/



end CKLaneA3X
