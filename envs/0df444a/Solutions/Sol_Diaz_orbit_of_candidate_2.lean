-- Prove2me | solution 2 for Diaz.orbit_of_candidate
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:20:56.983525+00:00
-- url     : https://prove2.me/submissions/1b84e6f7-e420-4d4c-8361-73c05526f482

/-
`Diaz.orbit_of_candidate` as a composition of published nodes.

The membership half is exactly `Diaz.locus_stable`: the candidate locus is
stable under complex conjugation and under non-zero rational scaling, and
`{u, -u, ū, -ū}` is generated from `u` by those two operations (`-x` is the
scaling by `q = -1`).  The distinctness half is `Diaz.not_on_axes` over `Q̄`,
which applies because `Diaz.transcendental_of_candidate` puts `u` outside `Q̄`.
-/
import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_transcendental_of_candidate
import Theorems.Thm_Diaz_not_on_axes
import Theorems.Thm_Diaz_locus_stable

open ComplexConjugate
open Diaz

private theorem gr_mem_Qbar_iff (z : ℂ) : IsAlgebraic ℚ z ↔ z ∈ Qbar := by
  rw [Qbar, IntermediateField.mem_toSubfield, mem_algebraicClosure_iff]

open Diaz in
theorem solution {u : ℂ} (hu0 : u ≠ 0)
    (hexp : IsAlgebraic ℚ (Complex.exp u)) (hρ : IsAlgebraic ℚ (u * conj u)) :
    (∀ v ∈ ({u, -u, conj u, -conj u} : Set ℂ),
        v ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp v) ∧ v * conj v = u * conj u)
      ∧ u ≠ -u ∧ u ≠ conj u ∧ u ≠ -conj u
      ∧ -u ≠ conj u ∧ -u ≠ -conj u ∧ conj u ≠ -conj u := by
  -- membership: the locus is stable under conjugation and rational scaling
  obtain ⟨⟨hcu0, hexpc, hmodc⟩, hscale⟩ := Diaz.locus_stable hu0 hexp hρ
  obtain ⟨-, hscalec⟩ := Diaz.locus_stable hcu0 hexpc hmodc
  obtain ⟨hn0, hnexp, -⟩ := hscale (-1) (by norm_num)
  obtain ⟨hnc0, hncexp, -⟩ := hscalec (-1) (by norm_num)
  have e1 : (((-1 : ℚ) : ℂ)) * u = -u := by push_cast; ring
  have e2 : (((-1 : ℚ) : ℂ)) * conj u = -conj u := by push_cast; ring
  rw [e1] at hn0 hnexp
  rw [e2] at hnc0 hncexp
  -- distinctness: `u` is transcendental over `Q̄`, so it lies on neither axis
  have hT : Transcendental (↥Qbar) u :=
    fun hcon => Diaz.transcendental_of_candidate hu0 hexp (hcon.restrictScalars ℚ)
  obtain ⟨hax1, hax2⟩ := Diaz.not_on_axes (K := Qbar) hT ((gr_mem_Qbar_iff _).mp hρ)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro v (rfl | rfl | rfl | rfl)
    · exact ⟨hu0, hexp, rfl⟩
    · exact ⟨hn0, hnexp, by rw [map_neg]; ring⟩
    · exact ⟨hcu0, hexpc, by rw [Complex.conj_conj]; ring⟩
    · exact ⟨hnc0, hncexp, by rw [map_neg, Complex.conj_conj]; ring⟩
  · intro h; exact hu0 (by linear_combination h / 2)
  · exact fun h => hax1 h.symm
  · intro h; exact hax2 (by linear_combination h)
  · intro h; exact hax2 h.symm
  · intro h; exact hax1 (by linear_combination h)
  · intro h; exact hcu0 (by linear_combination h / 2)
