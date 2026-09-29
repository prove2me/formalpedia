-- Prove2me | solution 1 for Diaz.candidate_indistinguishable
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:31:30.789179+00:00
-- url     : https://prove2.me/submissions/075df499-6436-4f88-8b41-c135b5b17650

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_exists_conj_intertwining
import Theorems.Thm_Diaz_exists_transcendental_on_circle
import Theorems.Thm_Diaz_transcendental_of_candidate

namespace Diaz

section
open ComplexConjugate

theorem mem_Qbar_iff {a : ℂ} : a ∈ Qbar ↔ IsAlgebraic ℚ a := by
  simp only [Qbar, IntermediateField.mem_toSubfield]
  exact mem_algebraicClosure_iff
end

section
open ComplexConjugate

/-- `Qbar` is conjugation-stable, which every result above assumes of the
base.  If `p` kills `a` then it kills `conj a`, its coefficients being
rational and so fixed by conjugation. -/
theorem conj_mem_Qbar {a : ℂ} (h : a ∈ Qbar) : conj a ∈ Qbar := by
  rw [mem_Qbar_iff] at h ⊢
  obtain ⟨p, hp0, hpa⟩ := h
  refine ⟨p, hp0, ?_⟩
  have := congrArg (starRingEnd ℂ) hpa
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, map_sum,
    Polynomial.sum] using this
end

section
open ComplexConjugate
open Polynomial
variable {K : Subfield ℂ} {t : ℂ}

/-- The circle condition in the form the matrix results consume.

`exists_transcendental_on_circle` gives `t · conj t = r · conj r`, while
`Rigidity` states its hypotheses as `u · conj u = r ^ 2`.  These agree
exactly when `r` is real — the intended case, `r = √ρ` with `ρ = |u|²` —
which is not implied by `r ∈ L` and so has to be said. -/
theorem exists_transcendental_on_circle_sq {L : Subfield ℂ}
    [Algebra.IsAlgebraic ℚ (↥L)] {r : ℂ} (hr : r ∈ L) (hrr : conj r = r)
    (hr0 : r ≠ 0) :
    ∃ t : ℂ, t ≠ 0 ∧ Transcendental (↥L) t ∧ t * conj t = r ^ 2
      ∧ t * conj t ∈ L := by
  obtain ⟨t, ht0, hT, heq, hmem⟩ :=
    exists_transcendental_on_circle hr (by rw [hrr]; exact hr) hr0
  refine ⟨t, ht0, hT, ?_, hmem⟩
  rw [heq, hrr]; ring
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

open Diaz in
theorem solution
    {u r : ℂ} (hu0 : u ≠ 0) (hexp : IsAlgebraic ℚ (Complex.exp u))
    (hr : r ∈ Qbar) (hrr : conj r = r) (hr0 : r ≠ 0)
    (h : u * conj u = r ^ 2) :
    ∃ t : ℂ, t ≠ 0 ∧ Transcendental (↥Qbar) t ∧
      ∃ Φ : ℂ →+* ℂ, (∀ a ∈ Qbar, Φ a = a) ∧ Φ u = t
        ∧ ∀ z ∈ hull Qbar u, Φ (conj z) = conj (Φ z) := by
  obtain ⟨t, ht0, hT, hteq, htmem⟩ := exists_transcendental_on_circle_sq hr hrr hr0
  have hu : Transcendental (↥Qbar) u := transcendental_candidate_over_base hu0 hexp
  obtain ⟨Φ, hK, hΦu, hcomm⟩ :=
    exists_conj_intertwining (K := Qbar) (fun a ha => conj_mem_Qbar ha) hu hT
      (by rw [h]; exact pow_mem hr 2) (by rw [hteq, h])
  exact ⟨t, ht0, hT, Φ, hK, hΦu, hcomm⟩
end
