-- Prove2me | solution 1 for Diaz.four_nodes_candidate
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:27:26.394724+00:00
-- url     : https://prove2.me/submissions/72f5bd6f-9786-45a4-a7b8-a7e442ff00a7

import Mathlib
import Theorems.Thm_Diaz_four_nodes
import Theorems.Thm_Diaz_not_on_axes
import Theorems.Thm_Diaz_transcendental_of_candidate

namespace Diaz

section
open ComplexConjugate
variable {K : Subfield ℂ} {u : ℂ}

/-- If `u + conj u` is transcendental over the base then its square is
not in the base. -/
theorem sq_notMem_of_transcendental {L : Subfield ℂ}
    (h : Transcendental (↥L) (u + conj u)) : (u + conj u) ^ 2 ∉ L := by
  intro hmem
  refine h ⟨Polynomial.X ^ 2 - Polynomial.C (⟨_, hmem⟩ : L),
    (Polynomial.monic_X_pow_sub_C _ (by norm_num)).ne_zero, ?_⟩
  simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
  show (u + conj u) ^ 2 - (u + conj u) ^ 2 = 0
  ring
end

section
open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

/-- Transcendence over `ℚ` upgrades to transcendence over any base
algebraic over `ℚ` — in particular over the algebraic numbers, which is
the intended base.

Without this the imported axiom is a dead leaf: the results above take
transcendence over the base as a hypothesis, while Hermite–Lindemann
supplies it only over `ℚ`. The algebraicity hypothesis is necessary
rather than decorative: for a base containing `u` the conclusion is
false. -/
theorem transcendental_of_base {L : Subfield ℂ} [Algebra.IsAlgebraic ℚ (↥L)]
    {z : ℂ} (h : Transcendental ℚ z) : Transcendental (↥L) z :=
  fun hcon => h (hcon.restrictScalars ℚ)
end

section
open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

/-- The bridge, assembled: a candidate is transcendental over the base. -/
theorem transcendental_candidate_over_base {L : Subfield ℂ}
    [Algebra.IsAlgebraic ℚ (↥L)] (hu : u ≠ 0)
    (hexp : IsAlgebraic ℚ (Complex.exp u)) : Transcendental (↥L) u :=
  transcendental_of_base (transcendental_of_candidate hu hexp)
end

end Diaz

section
open ComplexConjugate
variable {K : Subfield ℂ} {u : ℂ}

open Diaz in
theorem solution {L : Subfield ℂ} [Algebra.IsAlgebraic ℚ (↥L)]
    (hu0 : u ≠ 0) (hexp : IsAlgebraic ℚ (Complex.exp u))
    (hρ : u * conj u ∈ L)
    {a b : ℚ} (h : ((a : ℂ) * u + (b : ℂ) * conj u)
      * conj ((a : ℂ) * u + (b : ℂ) * conj u) = u * conj u) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0)
      ∨ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by
  have hT : Transcendental (↥L) u := transcendental_candidate_over_base hu0 hexp
  -- `u + conj u ≠ 0` is the second half of the axis lemma, three declarations up
  have hsum0 : u + conj u ≠ 0 := by
    intro hz
    exact (not_on_axes hT hρ).2 (by linear_combination hz)
  -- and its exponential is algebraic, being `exp u` times its conjugate
  have hsumexp : IsAlgebraic ℚ (Complex.exp (u + conj u)) := by
    have : Complex.exp (u + conj u) = Complex.exp u * conj (Complex.exp u) := by
      rw [← Complex.exp_conj, ← Complex.exp_add]
    rw [this]
    refine hexp.mul ?_
    obtain ⟨q, hq0, hqa⟩ := hexp
    refine ⟨q, hq0, ?_⟩
    have := congrArg (starRingEnd ℂ) hqa
    simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, map_sum,
      Polynomial.sum] using this
  exact four_nodes hρ
    (sq_notMem_of_transcendental
      (transcendental_candidate_over_base hsum0 hsumexp)) h
end
