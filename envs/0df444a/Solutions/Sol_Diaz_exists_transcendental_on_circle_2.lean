-- Prove2me | solution 2 for Diaz.exists_transcendental_on_circle
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T12:38:59.070316+00:00
-- url     : https://prove2.me/submissions/e5b16731-40b4-4163-ac53-7e55938b523a

import Mathlib

open ComplexConjugate
open Polynomial
variable {K : Subfield ℂ} {t : ℂ}

theorem solution {L : Subfield ℂ}
    [Algebra.IsAlgebraic ℚ (↥L)] {r : ℂ} (hr : r ∈ L) (hrc : conj r ∈ L)
    (hr0 : r ≠ 0) :
    ∃ t : ℂ, t ≠ 0 ∧ Transcendental (↥L) t ∧ t * conj t = r * conj r
      ∧ t * conj t ∈ L := by
  classical
  set ρ : ℝ := Complex.normSq r with hρdef
  have hρpos : 0 < ρ := Complex.normSq_pos.2 hr0
  set c : ℝ := Real.sqrt ρ with hcdef
  have hcpos : 0 < c := Real.sqrt_pos.2 hρpos
  have hcsq : c ^ 2 = ρ := Real.sq_sqrt hρpos.le
  set f : ℝ → ℂ := fun x => Complex.mk x (Real.sqrt (ρ - x ^ 2)) with hfdef
  have hfinj : Function.Injective f := by
    intro x y h
    have := congrArg Complex.re h
    simpa [hfdef] using this
  have hfnorm : ∀ x ∈ Set.Ioo (-c) c, Complex.normSq (f x) = ρ := by
    intro x hx
    have hx2 : x ^ 2 < ρ := by
      rw [← hcsq]
      nlinarith [hx.1, hx.2, hcpos]
    have hs : Real.sqrt (ρ - x ^ 2) * Real.sqrt (ρ - x ^ 2) = ρ - x ^ 2 :=
      Real.mul_self_sqrt (by linarith)
    simp only [Complex.normSq_apply, hfdef]
    nlinarith [hs]
  -- some point of the circle is transcendental over ℚ
  have hex : ∃ x ∈ Set.Ioo (-c) c, Transcendental ℚ (f x) := by
    by_contra hcon
    push Not at hcon
    have hsub : Set.Ioo (-c) c ⊆ f ⁻¹' {z : ℂ | IsAlgebraic ℚ z} := by
      intro x hx
      have := hcon x hx
      rw [Transcendental, not_not] at this
      exact this
    have hcount : (Set.Ioo (-c) c).Countable :=
      Set.Countable.mono hsub ((Algebraic.countable ℚ ℂ).preimage hfinj)
    rw [Cardinal.Real.Ioo_countable_iff] at hcount
    linarith
  obtain ⟨x, hx, hxt⟩ := hex
  refine ⟨f x, ?_, ?_, ?_, ?_⟩
  · intro h
    have := hfnorm x hx
    rw [h] at this
    simp at this
    exact absurd this.symm (ne_of_gt hρpos)
  · exact (Algebra.IsAlgebraic.transcendental_iff (R := ℚ) (S := (↥L))).1 hxt
  · rw [Complex.mul_conj, Complex.mul_conj, hfnorm x hx, ← hρdef]
  · have hcast : ((ρ : ℝ) : ℂ) = r * conj r := (Complex.mul_conj r).symm
    rw [Complex.mul_conj, hfnorm x hx, hcast]
    exact mul_mem hr hrc
