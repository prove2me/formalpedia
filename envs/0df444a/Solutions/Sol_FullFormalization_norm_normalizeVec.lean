-- Prove2me | solution 1 for FullFormalization.norm_normalizeVec
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:50:51.78799+00:00
-- url     : https://prove2.me/submissions/45cba0e5-ea4d-4c1f-8e0b-c6fd6571aa45

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

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : E} (hv : v ≠ 0) : ‖normalizeVec v‖ = 1 := by
  rw [normalizeVec, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
