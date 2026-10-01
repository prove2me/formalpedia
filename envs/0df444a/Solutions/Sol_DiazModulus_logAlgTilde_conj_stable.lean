-- Prove2me | solution 1 for DiazModulus.logAlgTilde_conj_stable
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T09:17:44.242147+00:00
-- url     : https://prove2.me/submissions/a9d7aa74-7296-47cc-8095-d74dc9b97949

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_logAlg_conj_stable

open Complex ComplexConjugate

namespace TildeConj

/-- Complex conjugation as a `ℚ`-algebra map. -/
noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

/-- Conjugation preserves algebraicity over `ℚ`, so it maps `Qbar` to itself. -/
theorem conj_mem_Qbar {a : ℂ} (ha : a ∈ DiazModulus.Qbar) : conj a ∈ DiazModulus.Qbar := by
  obtain ⟨p, hp0, hp⟩ := DiazModulus.mem_Qbar_iff.1 ha
  refine DiazModulus.mem_Qbar_iff.2 ⟨p, hp0, ?_⟩
  rw [show (conj a : ℂ) = cjQ a from rfl, Polynomial.aeval_algHom_apply, hp, map_zero]

end TildeConj

open DiazModulus TildeConj in
/-- `ℒ̃` is stable under complex conjugation: conjugation fixes `1`, maps `ℒ` to itself, and
sends `c • x` to `conj c • conj x` with `conj c` again in `Qbar`. -/
theorem solution (z : ℂ) (h : z ∈ LogAlgTilde) : conj z ∈ LogAlgTilde := by
  unfold LogAlgTilde at h ⊢
  induction h using Submodule.span_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · rw [map_one]
      exact Submodule.subset_span (Set.mem_insert _ _)
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ (logAlg_conj_stable x hx))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have hcx : conj (c • x) = (⟨conj (c : ℂ), conj_mem_Qbar c.2⟩ : ↥Qbar) • conj x :=
      map_mul conj (c : ℂ) x
    rw [hcx]
    exact Submodule.smul_mem _ _ hx
