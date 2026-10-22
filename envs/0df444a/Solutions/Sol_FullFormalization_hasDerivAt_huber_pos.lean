-- Prove2me | solution 1 for FullFormalization.hasDerivAt_huber_pos
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:53:58.936632+00:00
-- url     : https://prove2.me/submissions/92c22819-6b78-4cb6-915e-90e568fc4a48

-- Generated from F:/20261008/FullFormalization\FullFormalization\Huber1D.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.Huber1D

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, section 20
  (「定理 A 的 matching lower bound」, lines 1817-2046).

  The source fixes `L = 1`, `x⋆ = 0`, `x₀ = R > 0`, sets

      c = R / (2 d_N + 1)                                    (20.1)

  and defines the one-dimensional Huber function

      f x = x²/2            if |x| ≤ c
      f x = c |x| - c²/2    if |x| ≥ c                       (20.2)

  It then states (lines 1853-1858) that `f` is convex, differentiable, has a
  globally 1-Lipschitz gradient and has `0` as its unique minimizer, and proves
  the NAG trajectory identity

      x_j = R - d_j c                                        (20.3)

  together with the observation that the whole trajectory stays in the positive
  linear branch (`x_j ≥ c` for `j ≤ N`, source 20.2), whence

      (f(x_N) - f⋆) / R² = 2 / (N² + 7 N + 4)                (20.4)

  i.e. exactly `tau N` of `FullFormalization.Coefficients`.  This is the
  matching lower bound: the upper bound (19.1) is attained.

  ## Representation choices

  * The constant `c` is called `huberC` here: `d` is the coefficient sequence of
    `FullFormalization.Coefficients`, and `c` is used as a bound variable
    throughout the project, so a global `c` would be confusing.

  * `huber c : ℝ → ℝ` is stated for an arbitrary `c`; every property below
    carries the hypothesis `0 ≤ c` (or `0 < c`) that the source's `c`, being a
    quotient by the positive `2 d_N + 1`, always satisfies.

  * The gradient of `huber c` is the clipping `huberClamp c x = max (-c) (min c x)`
    of `x` to `[-c, c]`.  Its 1-Lipschitz property is `huberClamp_lipschitz`;
    it is monotone, which is how convexity of `huber c` is obtained (through
    `MonotoneOn.convexOn_of_deriv`).  Differentiability is proved by gluing the
    two branches at the kinks `±c`, where the one-sided derivatives agree.

  * **Index range of (20.3).**  The source writes `x_j = R - d_j c` for the
    iterates of the method.  The induction only ever queries `x_0, …, x_N`
    (the method stops at `x_N`), and it uses the branch hypothesis `x_j ≥ c`,
    which is *false* for `j > N`.  Accordingly `huber_traj` below is stated for
    `j ≤ N`, which is exactly the range on which (20.3) is true.  (For `N = 1`,
    `R = 1` one gets `c = 1/3`, `x_3 = -2/15` while `R - d_3 c = -1/4`: the
    unrestricted statement is false.)
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_Huber1D
import Definitions.Def_RationalNAG
import Theorems.Thm_FullFormalization_hasDerivAt_linear
import Theorems.Thm_FullFormalization_hasDerivAt_neglinear
import Theorems.Thm_FullFormalization_hasDerivAt_sq_div_two
import Theorems.Thm_FullFormalization_huberClamp_of_abs_lt
import Theorems.Thm_FullFormalization_huberClamp_of_c_le
import Theorems.Thm_FullFormalization_huberClamp_of_le_neg
import Theorems.Thm_FullFormalization_huber_of_abs_le
import Theorems.Thm_FullFormalization_huber_of_c_le
import Theorems.Thm_FullFormalization_huber_of_le_neg

open scoped Gradient RealInnerProductSpace
open Set
set_option linter.unusedSectionVars false

namespace FullFormalization

/-! ## Section 20.0: the Huber function -/









/-! ## Elementary values of `huber`, `huberClamp` and the coefficients -/

































/-! ## Elementary derivatives of the two branches -/







/-! ## Section 20, lines 1853-1858: the analytic properties of `huber`

The derivative is computed by gluing the two branches at the two kinks `±c`;
the one-sided derivatives agree there (both are `±c`), so the gluing goes
through `HasDerivWithinAt.union`. -/

















/-! ## Source line 1857-1858: `0` is the unique minimizer -/






/-! ## Section 20.1-20.2: the NAG trajectory -/







/-! ## Section 20.3: the attained value (20.4) -/







/-! ## Theorem A, lower bound: the Huber function attains the bound -/



end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
open Set
set_option linter.unusedSectionVars false

open FullFormalization in
theorem solution {c : ℝ} (hc : 0 < c) (x : ℝ) :
    HasDerivAt (huber c) (huberClamp c x) x := by
  have hcle : 0 ≤ c := hc.le
  have hltc : -c < c := by linarith
  rcases lt_trichotomy x c with hlt | heq | hgt
  · rcases lt_trichotomy x (-c) with hxl | hxl | hxl
    · -- x < -c: the negative linear branch
      rw [huberClamp_of_le_neg hcle (le_of_lt hxl)]
      exact ((hasDerivAt_neglinear c x).hasDerivWithinAt.congr_mono
        (fun y hy => huber_of_le_neg hcle hy)
        (huber_of_le_neg hcle (le_of_lt hxl))
        (Set.subset_univ _)).hasDerivAt (Iic_mem_nhds hxl)
    · -- x = -c: the left kink
      rw [hxl, huberClamp_of_le_neg hcle le_rfl]
      have hleft : HasDerivWithinAt (huber c) (-c) (Iic (-c)) (-c) :=
        (hasDerivAt_neglinear c (-c)).hasDerivWithinAt.congr_mono
          (fun y hy => huber_of_le_neg hcle hy)
          (huber_of_le_neg hcle le_rfl)
          (Set.subset_univ _)
      have hright : HasDerivWithinAt (huber c) (-c) (Icc (-c) c) (-c) :=
        (hasDerivAt_sq_div_two (-c)).hasDerivWithinAt.congr_mono
          (fun y hy => huber_of_abs_le (abs_le.mpr ⟨hy.1, hy.2⟩))
          (huber_of_abs_le (abs_le.mpr ⟨le_rfl, by linarith⟩))
          (Set.subset_univ _)
      have hset : Iic (-c) ∪ Icc (-c) c = Iic c := by
        ext y
        constructor
        · rintro (h | h)
          · exact le_trans h (le_of_lt hltc)
          · exact h.2
        · intro h
          rcases le_or_gt y (-c) with h' | h'
          · exact Or.inl h'
          · exact Or.inr ⟨le_of_lt h', h⟩
      exact (hleft.union hright).hasDerivAt (by rw [hset]; exact Iic_mem_nhds hltc)
    · -- -c < x < c: the quadratic branch
      rw [huberClamp_of_abs_lt (abs_lt.mpr ⟨hxl, hlt⟩)]
      exact ((hasDerivAt_sq_div_two x).hasDerivWithinAt.congr_mono
        (fun y hy => huber_of_abs_le (abs_le.mpr ⟨hy.1, hy.2⟩))
        (huber_of_abs_le (abs_le.mpr ⟨le_of_lt hxl, le_of_lt hlt⟩))
        (Set.subset_univ _)).hasDerivAt (Icc_mem_nhds hxl hlt)
  · -- x = c: the right kink
    rw [heq, huberClamp_of_c_le hcle le_rfl]
    have hleft : HasDerivWithinAt (huber c) c (Icc (-c) c) c :=
      (hasDerivAt_sq_div_two c).hasDerivWithinAt.congr_mono
        (fun y hy => huber_of_abs_le (abs_le.mpr ⟨hy.1, hy.2⟩))
        (huber_of_abs_le (abs_le.mpr ⟨by linarith, le_rfl⟩))
        (Set.subset_univ _)
    have hright : HasDerivWithinAt (huber c) c (Ici c) c :=
      (hasDerivAt_linear c c).hasDerivWithinAt.congr_mono
        (fun y hy => huber_of_c_le hcle hy)
        (huber_of_c_le hcle le_rfl)
        (Set.subset_univ _)
    have hset : Icc (-c) c ∪ Ici c = Ici (-c) := by
      ext y
      constructor
      · rintro (h | h)
        · exact h.1
        · exact le_trans (le_of_lt hltc) h
      · intro h
        rcases le_or_gt y c with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr (le_of_lt h')
    exact (hleft.union hright).hasDerivAt (by rw [hset]; exact Ici_mem_nhds hltc)
  · -- c < x: the positive linear branch
    rw [huberClamp_of_c_le hcle (le_of_lt hgt)]
    exact ((hasDerivAt_linear c x).hasDerivWithinAt.congr_mono
      (fun y hy => huber_of_c_le hcle hy)
      (huber_of_c_le hcle (le_of_lt hgt))
      (Set.subset_univ _)).hasDerivAt (Ici_mem_nhds hgt)
