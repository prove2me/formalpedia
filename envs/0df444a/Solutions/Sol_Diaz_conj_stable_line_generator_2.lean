-- Prove2me | solution 2 for Diaz.conj_stable_line_generator
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:26:51.355972+00:00
-- url     : https://prove2.me/submissions/d0bcaa0c-3aa0-414f-99f2-1a49b3886a21

/-
`Diaz.conj_stable_line_generator` through `Diaz.involution_alignment`.

If `b ≠ 1`, the shifted point `w = y + a/(b-1)` satisfies `conj w = b w`
exactly — the rational shift absorbs the affine term — and `w ≠ 0`, because
`w = 0` would make `y` rational, which `hy` forbids. Since `b` is rational,
`conj b = b`, so `Diaz.involution_alignment` at `σ = conj`, `c = b` applies and
gives `b = 1 ∨ b = -1`; with `b ≠ 1` that is `b = -1`. The case `b = 1` is one
application of the involution to the hypothesis.

The previous accepted proof derived `b = ±1` by hand from
`(b+1)((1-b)y - a) = 0`, which is `involution_alignment`'s own factorisation
`(c-1)(c+1)u = 0` written out for this instance.
-/
import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_involution_alignment

open ComplexConjugate
open Diaz

open Diaz in
theorem solution {y : ℂ} (hy : ∀ q : ℚ, y ≠ (q : ℂ)) {a b : ℚ}
    (h : conj y = (a : ℂ) + (b : ℂ) * y) :
    (b = 1 ∧ a = 0 ∧ conj y = y)
      ∨ (b = -1 ∧ conj (y - (a : ℂ) / 2) = -(y - (a : ℂ) / 2)) := by
  have hcinv : ∀ z : ℂ, conj (conj z) = z := fun z => by simp
  have hbq : conj ((b : ℂ)) = (b : ℂ) := by simp
  by_cases hb1 : b = 1
  · subst hb1
    have h2 : y = (a : ℂ) + ((1 : ℚ) : ℂ) * conj y := by
      have := congrArg conj h
      rw [hcinv, map_add, map_mul, hbq] at this
      simpa using this
    have h1 : conj y = (a : ℂ) + y := by push_cast at h; linear_combination h
    have ha : (a : ℂ) = 0 := by push_cast at h2; linear_combination (-h1 - h2) / 2
    refine Or.inl ⟨rfl, by exact_mod_cast ha, ?_⟩
    rw [h1, ha]; ring
  · -- shift so that the relation becomes homogeneous
    have hbq1 : ((b : ℚ) - 1) ≠ 0 := fun hz => hb1 (by linarith)
    have hbC1 : ((b : ℂ) - 1) ≠ 0 := by
      intro hz
      exact hbq1 (by exact_mod_cast (by linear_combination hz : ((b : ℚ) - 1 : ℂ) = 0))
    set s : ℚ := a / (b - 1) with hs
    set w : ℂ := y + (s : ℂ) with hw
    have hsC : (s : ℂ) = (a : ℂ) / ((b : ℂ) - 1) := by rw [hs]; push_cast; ring
    have hw0 : w ≠ 0 := by
      intro hz
      exact hy (-s) (by rw [hw] at hz; push_cast; linear_combination hz)
    have hcw : conj w = (b : ℂ) * w := by
      have hcs : conj ((s : ℂ)) = (s : ℂ) := by simp
      rw [hw, map_add, hcs, h, hsC]
      field_simp
      ring
    have hb := Diaz.involution_alignment (starRingEnd ℂ) hcinv hw0 hbq hcw
    have hbm : b = -1 := by
      rcases hb with hz | hz
      · exact absurd (by exact_mod_cast hz : b = 1) hb1
      · exact_mod_cast hz
    subst hbm
    refine Or.inr ⟨rfl, ?_⟩
    have hc2 : conj (2 : ℂ) = 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
    have hca : conj ((a : ℂ) / 2) = (a : ℂ) / 2 := by
      rw [map_div₀, hc2]; norm_num
    rw [map_sub, hca, h]
    push_cast
    ring
