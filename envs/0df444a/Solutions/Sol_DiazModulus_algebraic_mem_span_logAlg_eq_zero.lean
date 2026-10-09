-- Prove2me | solution 1 for DiazModulus.algebraic_mem_span_logAlg_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-08T16:42:26.267738+00:00
-- url     : https://prove2.me/submissions/ca2ff379-b3a7-4b7b-b7d7-243cb22491e9

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_Schanuel_baker_linear_forms_in_logarithms

open Complex ComplexConjugate

/-! # An algebraic number in the `Q̄`-span of `ℒ` is zero

Baker's theorem in its homogeneous-plus-constant form: for `ℚ`-linearly independent logarithms
`λ₁, …, λₙ` of algebraic numbers and algebraic `b₀, b₁, …, bₙ`, not all zero,
`b₀ + b₁ λ₁ + ⋯ + bₙ λₙ ≠ 0`.

Choose a `ℚ`-linearly independent subset `B ⊆ ℒ` whose `ℚ`-span is the `ℚ`-span of `ℒ`
(`exists_linearIndependent`). Then `ℒ` lies in the `Q̄`-span of `B`, so `z = ∑ c(λ) λ` with
`λ` running over a finite subset of `B` and `c(λ) ∈ Q̄`. If `z ≠ 0`, Baker's theorem applied with
`b₀ = −z` (algebraic and non-zero) gives `−z + ∑ c(λ) λ ≠ 0`, while this sum is `−z + z = 0`.
-/

namespace R6_algSpanLog
open DiazModulus

theorem logAlg_le_span_basis :
    ∃ B ⊆ LogAlg, Submodule.span Qbar LogAlg ≤ Submodule.span Qbar B ∧
      LinearIndependent ℚ ((↑) : B → ℂ) := by
  obtain ⟨B, hBL, hspan, hind⟩ := exists_linearIndependent ℚ LogAlg
  refine ⟨B, hBL, Submodule.span_le.2 fun x hx => ?_, hind⟩
  have hx' : x ∈ Submodule.span ℚ B := hspan ▸ Submodule.subset_span hx
  exact Submodule.span_le_restrictScalars ℚ Qbar B hx'

end R6_algSpanLog

open DiazModulus R6_algSpanLog in
theorem solution (z : ℂ) (hz : z ∈ Qbar)
    (hspan : z ∈ Submodule.span Qbar LogAlg) : z = 0 := by
  classical
  by_contra hz0
  obtain ⟨B, hBL, hle, hind⟩ := logAlg_le_span_basis
  obtain ⟨c, hcB, hcz⟩ := Submodule.mem_span_set.1 (hle hspan)
  set s := c.support
  let e : Fin s.card ≃ s := s.equivFin.symm
  let f : Fin s.card → B := fun i => ⟨e i, hcB (e i).2⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact e.injective (Subtype.ext (congrArg (fun b : B => (b : ℂ)) hij))
  have hl : LinearIndependent ℚ (fun i => ((e i : s) : ℂ)) := hind.comp f hf
  have hsum : z = ∑ i, ((c (e i) : Qbar) : ℂ) * ((e i : s) : ℂ) := by
    rw [← hcz, Finsupp.sum, ← Finset.sum_coe_sort s]
    exact (Equiv.sum_comp e (fun x : s => c x • (x : ℂ))).symm
  apply Schanuel.baker_linear_forms_in_logarithms s.card (fun i => ((e i : s) : ℂ)) hl
    (fun i => hBL (hcB (e i).2)) (-z) (fun i => ((c (e i) : Qbar) : ℂ))
    (mem_Qbar_iff.1 (Qbar.neg_mem hz)) (fun i => mem_Qbar_iff.1 (c (e i)).2)
    (Or.inl (neg_ne_zero.2 hz0))
  rw [← hsum, neg_add_cancel]
