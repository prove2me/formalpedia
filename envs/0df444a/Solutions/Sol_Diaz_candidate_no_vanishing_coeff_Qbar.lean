-- Prove2me | solution 1 for Diaz.candidate_no_vanishing_coeff_Qbar
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:27:24.384655+00:00
-- url     : https://prove2.me/submissions/32e64f77-79fb-485c-863a-61dde8b48a5a

import Mathlib
import Definitions.Def_Diaz_Instantiation
import Definitions.Def_Diaz_Rigidity
import Theorems.Thm_Diaz_no_vanishing_coeff
import Theorems.Thm_Diaz_transcendental_of_candidate

namespace Diaz

section
open ComplexConjugate
variable {K : Subfield ℂ} {u r : ℂ}

theorem coeff_eq_matrix (u r : ℂ) (w v : Fin 2 → ℂ) :
    ∑ i, ∑ j, w i * (Hmat u r) i j * v j
      = w 0 * (u * v 0 + r * v 1) + w 1 * (r * v 0 + conj u * v 1) := by
  simp [Hmat, Fin.sum_univ_two]
  ring
end

section
open ComplexConjugate
variable {K : Subfield ℂ} {u r : ℂ}

/-- **No vanishing coefficient, in matrix form.** -/
theorem no_vanishing_coeff_matrix (hr : r ∈ K) (huK : u ∉ K)
    (h : u * conj u = r ^ 2)
    (w v : Fin 2 → ℂ) (hwK : ∀ i, w i ∈ K) (hvK : ∀ j, v j ∈ K)
    (hw : w ≠ 0) (hv : v ≠ 0) :
    ∑ i, ∑ j, w i * (Hmat u r) i j * v j ≠ 0 := by
  rw [coeff_eq_matrix]
  exact no_vanishing_coeff hr huK h w v hwK hvK hw hv
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

section
open ComplexConjugate
variable {K : Subfield ℂ} {u r : ℂ}

/-- If `u` is a Diaz candidate over a base algebraic over `ℚ`, then the
attached rank-one matrix has no vanishing coefficient over that base. -/
theorem candidate_no_vanishing_coeff {L : Subfield ℂ} [Algebra.IsAlgebraic ℚ (↥L)]
    {u r : ℂ} (hu0 : u ≠ 0) (hexp : IsAlgebraic ℚ (Complex.exp u))
    (hr : r ∈ L) (h : u * conj u = r ^ 2)
    (w v : Fin 2 → ℂ) (hwK : ∀ i, w i ∈ L) (hvK : ∀ j, v j ∈ L)
    (hw : w ≠ 0) (hv : v ≠ 0) :
    ∑ i, ∑ j, w i * (Hmat u r) i j * v j ≠ 0 := by
  have ht : Transcendental (↥L) u := transcendental_candidate_over_base hu0 hexp
  have huL : u ∉ L := fun hm => ht (isAlgebraic_algebraMap (R := ↥L) ⟨u, hm⟩)
  exact no_vanishing_coeff_matrix hr huL h w v hwK hvK hw hv
end

end Diaz

section
open ComplexConjugate

open Diaz in
theorem solution
    {u r : ℂ} (hu0 : u ≠ 0) (hexp : IsAlgebraic ℚ (Complex.exp u))
    (hr : r ∈ Qbar) (h : u * conj u = r ^ 2)
    (w v : Fin 2 → ℂ) (hwK : ∀ i, w i ∈ Qbar) (hvK : ∀ j, v j ∈ Qbar)
    (hw : w ≠ 0) (hv : v ≠ 0) :
    ∑ i, ∑ j, w i * (Hmat u r) i j * v j ≠ 0 :=
  candidate_no_vanishing_coeff hu0 hexp hr h w v hwK hvK hw hv
end
