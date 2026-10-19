-- Prove2me | solution 1 for DiazModulus.mem_logAlg_adjoin_circle_point_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T17:58:04.703487+00:00
-- url     : https://prove2.me/submissions/c91784f7-55c8-4559-98e4-249c2fa349bf

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_Diaz_exp_ratMul_isAlgebraic

open Complex ComplexConjugate

/-! # The space `ℒ_u = span ℚ ℒ + ℚu + ℚū`, and its `Q̄`-span with `1`

The set `ℒ` of logarithms of algebraic numbers is already a `ℚ`-subspace of `ℂ`: it contains `0`
(`exp 0 = 1`), it is closed under addition (`exp (a + b) = exp a * exp b`), and under rational
multiples (`Diaz.exp_ratMul_isAlgebraic`). So by `Submodule.span_induction` every element of
`span ℚ ℒ` lies in `ℒ`. Membership in `ℒ_u = span ℚ ℒ ⊔ span ℚ {u, ū}` then unfolds through
`Submodule.mem_sup` and `Submodule.mem_span_pair` to `z = c + pu + qū` with `c ∈ ℒ`, `p, q ∈ ℚ`.

For the `Q̄`-span: every generator of `span Q̄ (insert 1 ℒ_u)` lies in `ℒ̃ ⊔ span Q̄ {u, ū}`, since
`1` and `c ∈ ℒ` lie in `ℒ̃` and the rational coefficients `p, q` are algebraic. Conversely
`ℒ̃ = span Q̄ (insert 1 ℒ)` is contained in `span Q̄ (insert 1 ℒ_u)` because `ℒ ⊆ ℒ_u`, and so are
`u` and `ū`, which lie in `ℒ_u`. -/

namespace R19_M1

open DiazModulus

/-- `ℒ` is closed under the `ℚ`-span: `span ℚ ℒ ⊆ ℒ`. -/
theorem mem_logAlg_of_mem_span {z : ℂ} (hz : z ∈ Submodule.span ℚ LogAlg) : z ∈ LogAlg := by
  induction hz using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    show IsAlgebraic ℚ (Complex.exp 0)
    rw [Complex.exp_zero]
    exact isAlgebraic_one
  | add x y _ _ hx hy =>
    show IsAlgebraic ℚ (Complex.exp (x + y))
    rw [Complex.exp_add]
    exact hx.mul hy
  | smul a x _ hx =>
    show IsAlgebraic ℚ (Complex.exp (a • x))
    rw [Rat.smul_def]
    exact Diaz.exp_ratMul_isAlgebraic hx a

/-- The rational multiples of `w` lie in the `Q̄`-span of any set containing `w`. -/
theorem ratMul_mem_span {s : Set ℂ} {w : ℂ} (hw : w ∈ s) (p : ℚ) :
    (p : ℂ) * w ∈ Submodule.span Qbar s := by
  have hp : (p : ℂ) ∈ Qbar := SubfieldClass.ratCast_mem Qbar p
  have h := Submodule.smul_mem (Submodule.span Qbar s) (⟨(p : ℂ), hp⟩ : Qbar)
    (Submodule.subset_span hw)
  simpa [Subfield.smul_def] using h

end R19_M1

open DiazModulus R19_M1 in
theorem solution
    (u : ℂ) :
    (∀ z : ℂ, z ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)) ↔
      ∃ c ∈ LogAlg, ∃ p q : ℚ, z = c + (p : ℂ) * u + (q : ℂ) * conj u) ∧
    Submodule.span Qbar (insert 1 ((Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ) : Submodule ℚ ℂ) : Set ℂ)) =
      LogAlgTilde ⊔ Submodule.span Qbar ({u, conj u} : Set ℂ) := by
  have hmem : ∀ z : ℂ, z ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)) ↔
      ∃ c ∈ LogAlg, ∃ p q : ℚ, z = c + (p : ℂ) * u + (q : ℂ) * conj u := by
    intro z
    rw [Submodule.mem_sup]
    constructor
    · rintro ⟨c, hc, w, hw, rfl⟩
      obtain ⟨p, q, rfl⟩ := Submodule.mem_span_pair.mp hw
      refine ⟨c, mem_logAlg_of_mem_span hc, p, q, ?_⟩
      simp only [Rat.smul_def]
      ring
    · rintro ⟨c, hc, p, q, rfl⟩
      refine ⟨c, Submodule.subset_span hc, (p : ℂ) * u + (q : ℂ) * conj u,
        Submodule.mem_span_pair.mpr ⟨p, q, by simp only [Rat.smul_def]⟩, by ring⟩
  refine ⟨hmem, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro z (rfl | hz)
    · exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_insert _ _))
    · obtain ⟨c, hc, p, q, rfl⟩ := (hmem z).mp hz
      refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
      · exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_insert_of_mem _ hc))
      · exact Submodule.mem_sup_right (ratMul_mem_span (Set.mem_insert _ _) p)
      · exact Submodule.mem_sup_right
          (ratMul_mem_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)) q)
  · refine sup_le ?_ ?_
    · refine Submodule.span_mono (Set.insert_subset_insert ?_)
      intro c hc
      exact Submodule.mem_sup_left (Submodule.subset_span hc)
    · rw [Submodule.span_le]
      intro w hw
      refine Submodule.subset_span (Set.mem_insert_of_mem _ ?_)
      exact Submodule.mem_sup_right (Submodule.subset_span hw)
