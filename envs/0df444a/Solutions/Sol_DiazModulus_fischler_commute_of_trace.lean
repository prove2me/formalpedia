-- Prove2me | solution 1 for DiazModulus.fischler_commute_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:34:40.942193+00:00
-- url     : https://prove2.me/submissions/c0c9ef49-0b0e-4b7f-843a-d004df3134fd

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Q̄-free entries and a vanishing trace force commuting

For algebraic `A`, `B` the commutator `K = AB − BA` has algebraic entries and
`Tr(M K) = Σ_{i,j} K_{ji} M_{ij}` is a `Q̄`-linear combination of the `n²` entries of `M`. If it vanishes,
the `Q̄`-freeness of these entries kills every coefficient, so `K = 0`. Since `U` and `V` are spanned by
their algebraic elements and `(A, B) ↦ AB − BA` is bilinear, the identity `AB = BA` extends from algebraic
`A ∈ U`, `B ∈ V` to all of `U × V`: first in `B` for fixed algebraic `A`, then in `A` for any `B ∈ V`. -/

namespace RC3_FCT
open DiazModulus

theorem vanish_span {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (f : E →ₗ[ℂ] F) {s : Set E} (h : ∀ x ∈ s, f x = 0) : ∀ x ∈ Submodule.span ℂ s, f x = 0 :=
  fun _x hx =>
  LinearMap.mem_ker.mp (Submodule.span_le.mpr (fun y hy => LinearMap.mem_ker.mpr (h y hy)) hx)

/-- The commutator of two algebraic matrices is algebraic. -/
theorem comm_alg {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, A i j ∈ Qbar)
    (hB : ∀ i j, B i j ∈ Qbar) (i j : Fin n) : (A * B - B * A) i j ∈ Qbar := by
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  exact Qbar.sub_mem (Qbar.sum_mem fun k _ => Qbar.mul_mem (hA i k) (hB k j))
    (Qbar.sum_mem fun k _ => Qbar.mul_mem (hB i k) (hA k j))

/-- `Tr(M K) = 0` with `K` algebraic forces `K = 0` when the entries of `M` are `Q̄`-free. -/
theorem eq_zero_of_trace {n : ℕ} (M K : Matrix (Fin n) (Fin n) ℂ)
    (hfree : LinearIndependent (↥Qbar) (fun p : Fin n × Fin n => M p.1 p.2))
    (hK : ∀ i j, K i j ∈ Qbar) (htr : (M * K).trace = 0) : K = 0 := by
  have hsum : ∑ p : Fin n × Fin n, (⟨K p.2 p.1, hK _ _⟩ : ↥Qbar) • M p.1 p.2 = 0 := by
    rw [← htr, Matrix.trace, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subfield.smul_def, smul_eq_mul, mul_comm]
  have h0 := Fintype.linearIndependent_iff.mp hfree _ hsum
  ext i j
  exact congrArg Subtype.val (h0 (j, i))

end RC3_FCT

open DiazModulus RC3_FCT in
theorem solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hfree : LinearIndependent (↥Qbar) (fun p : Fin n × Fin n => M p.1 p.2))
    (U V : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hU : Submodule.span ℂ {A | A ∈ U ∧ ∀ i j, A i j ∈ Qbar} = U)
    (hV : Submodule.span ℂ {B | B ∈ V ∧ ∀ i j, B i j ∈ Qbar} = V)
    (htr : ∀ A ∈ U, ∀ B ∈ V, (M * (A * B - B * A)).trace = 0) :
    ∀ A ∈ U, ∀ B ∈ V, A * B = B * A := by
  -- algebraic `A ∈ U`, any `B ∈ V`
  have h1 : ∀ A ∈ {A | A ∈ U ∧ ∀ i j, A i j ∈ Qbar}, ∀ B ∈ V, A * B - B * A = 0 := by
    intro A hA B hB
    rw [← hV] at hB
    refine vanish_span (LinearMap.mulLeft ℂ A - LinearMap.mulRight ℂ A) ?_ B hB
    intro B' hB'
    exact eq_zero_of_trace M _ hfree (comm_alg A B' hA.2 hB'.2) (htr A hA.1 B' hB'.1)
  intro A hA B hB
  rw [← hU] at hA
  have := vanish_span (LinearMap.mulRight ℂ B - LinearMap.mulLeft ℂ B)
    (fun A' hA' => by
      show A' * B - B * A' = 0
      exact h1 A' hA' B hB) A hA
  exact sub_eq_zero.mp this
