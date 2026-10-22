-- Prove2me | solution 1 for FullFormalization.exists_nonzero_orthogonal_of_finrank_succ
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:50:50.231299+00:00
-- url     : https://prove2.me/submissions/87cda7e8-6bb1-4f5a-ba33-57864ba72753

-- Generated from F:/20261008/FullFormalization\FullFormalization\HiddenDirection.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.HiddenDirection

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, section 24
  (lines ~2175-2251), Lemma 24.1 and equations (24.1)-(24.5).

  The source document fixes the dimension

      D = 2 N + 1                                              (23.1)

  and, after fixing the seed, obtains `N` query points `q_1, ..., q_N ∈ ℝ^D`
  which are completely determined by `N`, `D` and the public sampling rule;
  in particular the query positions do not depend on function values.  It then
  asks for a *nonzero* vector `v` with

      v_1 = ... = v_N = 0,                                     (24.1)
      ⟨v, q_i⟩ = 0        for i = 1, ..., N,                   (24.2)

  and proves (Lemma 24.1) that such a `v` necessarily exists.

  Formalisation notes.

  * `Fin N` is the Lean index type for `i = 1, ..., N`; the source index `i`
    corresponds to `Fin` value `i - 1`.  Accordingly (24.1) -- `v_1 = ... = v_N = 0`
    -- says that the first `N` coordinates `v 0, ..., v (N-1)` vanish, which is
    encoded as `∀ i : Fin N, v (Fin.castLE _ i) = 0`; the map
    `Fin.castLE (by omega : N ≤ 2 * N + 1)` is the inclusion of the first `N`
    coordinates into `Fin (2 * N + 1)`.

  * The ambient space is `EuclideanSpace ℝ (Fin (2 * N + 1))`, i.e. `Fin D → ℝ`
    with the Pi inner product, exactly as in the source.

  * Lemma 24.1 is *proved*, not assumed: `exists_nonzero_orthogonal_of_finrank_succ`
    below isolates the pure dimension argument of the source ("the last `N + 1`
    coordinates span a subspace of dimension `N + 1`; the `N` homogeneous
    orthogonality conditions impose at most `N` independent linear constraints;
    hence the common kernel has dimension at least `(N + 1) - N = 1`"), and
    `finrank_vanishingFirstBlock` computes the dimension of the constrained
    subspace.  No axiom, `sorry` or `unsafe` is used anywhere in this file.

  * (24.3) writes `u = v / ‖v‖`.  This Mathlib revision has no scalar-division
    instance on `EuclideanSpace`, so the division is written as multiplication
    by `‖v‖⁻¹` (`normalizeVec`); `normalizeVec_eq` records the equality with the
    source's `v / ‖v‖`.
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_HiddenDirection

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace FullFormalization

noncomputable section

variable {N : ℕ}

/-! ## Lemma 24.1, abstract dimension argument

The source's proof only uses: a subspace of dimension `N + 1` in a real inner
product space, and `N` homogeneous linear constraints `⟨·, q i⟩ = 0`.  We prove
that abstract statement first, so that the dimension count is auditable on its
own, independently of the concrete coordinates in `Fin (2 * N + 1)`. -/



/-! ## The concrete subspace of (24.1)

`firstBlockProj N` is the linear map `v ↦ (v 0, ..., v (N-1))` that reads off the
first `N` coordinates of a vector of `EuclideanSpace ℝ (Fin (2 * N + 1))`; its
kernel is the subspace cut out by the conditions (24.1). -/









/-! ## Lemma 24.1 for the source's query points -/



/-! ## The unit vector `u = v / ‖v‖` of (24.3)-(24.5) -/









end

end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
variable {N : ℕ}

open FullFormalization in

theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Submodule ℝ E) (hK : Module.finrank ℝ ↥K = N + 1) (q : Fin N → E) :
    ∃ v ∈ K, v ≠ 0 ∧ ∀ i, ⟪v, q i⟫ = 0 := by
  classical
  -- The `N` orthogonality conditions, as a linear map defined on the subspace `K`.
  let ψ : ↥K →ₗ[ℝ] (Fin N → ℝ) :=
    { toFun := fun x i => ⟪(x : E), q i⟫
      map_add' := by intro x y; funext i; simp [inner_add_left]
      map_smul' := by intro c x; funext i; simp [real_inner_smul_left] }
  -- Rank-nullity for `ψ`:  dim (range ψ) + dim (ker ψ) = dim K = N + 1.
  have hrn := LinearMap.finrank_range_add_finrank_ker ψ
  -- The range of `ψ` lies in `Fin N → ℝ`, so it has dimension at most `N`:
  -- "at most `N` independent homogeneous linear equations".
  have hle : Module.finrank ℝ ↥ψ.range ≤ N := by
    have h := Submodule.finrank_le ψ.range
    rwa [Module.finrank_fin_fun] at h
  rw [hK] at hrn
  -- Hence the common kernel has dimension at least `(N + 1) - N = 1`.
  have hker : Module.finrank ℝ ↥ψ.ker ≠ 0 := by omega
  have hne : ψ.ker ≠ ⊥ := by
    intro h
    exact hker ((Submodule.finrank_eq_zero).mpr h)
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨(b : E), b.2, ?_, ?_⟩
  · -- `b ≠ 0` in `K` upgrades to `(b : E) ≠ 0`.
    intro h
    exact hb0 (Subtype.ext (by simpa using h))
  · -- Membership in the kernel of `ψ` is exactly (24.2).
    intro i
    have h : ψ b = 0 := hb
    exact congrFun h i
