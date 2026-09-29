-- Prove2me | solution 1 for CKLaneA3X.good_divt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T05:04:24.166299+00:00
-- url     : https://prove2.me/submissions/6ea46ba4-445c-4228-a94a-fc807d1c210e

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


























/-! ## SPoly -/



theorem SPoly.eval_nil (σ L : ℝ) : SPoly.eval σ L [] = 0 := rfl






















/-! ## TPoly (dense in t) -/



theorem TPoly.eval_nil (t σ L : ℝ) : TPoly.eval t σ L [] = 0 := rfl
theorem TPoly.eval_cons (t σ L : ℝ) (s : SPoly) (P : TPoly) :
    TPoly.eval t σ L (s :: P) = SPoly.eval σ L s + t * TPoly.eval t σ L P := rfl
























theorem TPoly.drop_nil (k : ℕ) : TPoly.drop [] k = [] := rfl
theorem TPoly.drop_zero (P : TPoly) : TPoly.drop P 0 = P := by cases P <;> rfl
theorem TPoly.drop_cons_succ (s : SPoly) (P : TPoly) (k : ℕ) :
    TPoly.drop (s :: P) (k + 1) = TPoly.drop P k := rfl



end CKLaneA3X



/-!
# CKLaneA3X.TM — Taylor-model enclosures in `t` over the high-u domain

Domain: `0 < t ≤ 7/50`, `0 < ρ < 1`; polynomials are evaluated at `σ = ρ - 1/2`, `L = log 2`.
`Encl f P r n` : `|f t ρ - P(t, ρ-1/2, log 2)| ≤ r * t^n` on the domain.
-/

namespace CKLaneA3X

























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



/-! ## truncated product soundness -/













/-! ## division by t, truncation -/





end CKLaneA3X



/-!
# CKLaneA3X.ExactPoly — exact polynomial constructions (divided-difference polynomial), divt
-/

namespace CKLaneA3X

open Finset

theorem _root_.solution {f : ℝ → ℝ → ℝ} {d : TMd} (h : Good f d) (hz : zeroPrefix d.P 1 = true) (hn : 1 ≤ d.n) :
    Good (fun t ρ => f t ρ / t) ⟨TPoly.drop d.P 1, d.r, d.n - 1⟩ := by
  refine ⟨?_, h.2⟩
  intro t ρ hd
  have ht := hd.1
  have h1 := h.1 t ρ hd
  have he := zeroPrefix_eval t (ρ - 1 / 2) (Real.log 2) d.P 1 hz
  unfold ev at h1 ⊢
  rw [he, pow_one] at h1
  have : f t ρ / t - TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.drop d.P 1) =
      (f t ρ - t * TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.drop d.P 1)) / t := by field_simp
  show |f t ρ / t - TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.drop d.P 1)| ≤ (d.r : ℝ) * t ^ (d.n - 1)
  rw [this, abs_div, abs_of_pos ht, div_le_iff₀ ht]
  calc _ ≤ (d.r : ℝ) * t ^ d.n := h1
    _ = (d.r : ℝ) * t ^ (d.n - 1) * t := by
        rw [mul_assoc, ← pow_succ]; congr 2; omega



























end CKLaneA3X
