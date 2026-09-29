-- Prove2me | solution 2 for Diaz.locus_stable
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:30:06.533988+00:00
-- url     : https://prove2.me/submissions/6974a262-251e-49ad-81f0-3dd921da13be

/-
`Diaz.locus_stable` through `Diaz.exp_ratMul_isAlgebraic`.

The rational-scaling half of this node has three clauses, and the middle one —
`exp (q u)` is algebraic — is verbatim the published node
`Diaz.exp_ratMul_isAlgebraic` ("rational multiples of a logarithm are
logarithms"). The previous accepted proof carried that argument inline: the same
`exp(qu)^den = exp(u)^num` identity, the same denominator/numerator case split.

The other clauses stay: `q u ≠ 0` is `mul_ne_zero`, `(qu)(q̄ū) = q²(u ū)` is one
`ring`, and the conjugation half is `Complex.exp_conj` plus the fact that `Q̄` is
stable under conjugation.
-/
import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_exp_ratMul_isAlgebraic

open ComplexConjugate
open Diaz

private theorem gr_mem_Qbar_iff {z : ℂ} : z ∈ Qbar ↔ IsAlgebraic ℚ z := by
  simp [Qbar, mem_algebraicClosure_iff]

private theorem gr_alg_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  have := (isAlgebraic_algHom_iff
      ((Complex.conjAe.restrictScalars ℚ).toAlgHom) (Complex.conjAe.injective)).mpr h
  simpa using this

open Diaz in
theorem solution {u : ℂ} (hu : u ≠ 0)
    (hexp : IsAlgebraic ℚ (Complex.exp u)) (hmod : IsAlgebraic ℚ (u * conj u)) :
    (conj u ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp (conj u)) ∧
        IsAlgebraic ℚ (conj u * conj (conj u))) ∧
      ∀ q : ℚ, q ≠ 0 →
        ((q : ℂ) * u ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp ((q : ℂ) * u)) ∧
          IsAlgebraic ℚ (((q : ℂ) * u) * conj ((q : ℂ) * u))) := by
  refine ⟨⟨by simpa using hu, ?_, ?_⟩, ?_⟩
  · rw [Complex.exp_conj]; exact gr_alg_conj hexp
  · have e : conj u * conj (conj u) = u * conj u := by rw [Complex.conj_conj]; ring
    rw [e]; exact hmod
  · intro q hq
    have hqc : ((q : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hq
    refine ⟨mul_ne_zero hqc hu, Diaz.exp_ratMul_isAlgebraic hexp q, ?_⟩
    have hcq : conj ((q : ℚ) : ℂ) = ((q : ℚ) : ℂ) := by simp
    have e : (((q : ℚ) : ℂ) * u) * conj (((q : ℚ) : ℂ) * u)
        = ((q : ℚ) : ℂ) ^ 2 * (u * conj u) := by
      rw [map_mul, hcq]; ring
    rw [e]
    exact gr_mem_Qbar_iff.mp
      (Qbar.mul_mem (Qbar.pow_mem (gr_mem_Qbar_iff.mpr (isAlgebraic_ratCast (A := ℂ) ℚ q)) 2)
        (gr_mem_Qbar_iff.mpr hmod))
