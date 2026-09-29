-- Prove2me | solution 1 for Diaz.exists_transcendental_on_circle_Qbar
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:29:31.804504+00:00
-- url     : https://prove2.me/submissions/8ca1d882-3f30-4efb-90d4-066e3e286732

import Mathlib
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_exists_transcendental_on_circle

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

end Diaz

section
open ComplexConjugate

open Diaz in
theorem solution {r : ℂ} (hr : r ∈ Qbar) (hr0 : r ≠ 0) :
    ∃ t : ℂ, t ≠ 0 ∧ Transcendental (↥Qbar) t ∧ t * conj t = r * conj r
      ∧ t * conj t ∈ Qbar :=
  exists_transcendental_on_circle hr (conj_mem_Qbar hr) hr0
end
