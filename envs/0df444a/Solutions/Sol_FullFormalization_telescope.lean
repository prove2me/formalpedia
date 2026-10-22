-- Prove2me | solution 1 for FullFormalization.telescope
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:56:34.194978+00:00
-- url     : https://prove2.me/submissions/9567090f-c77e-4203-8254-3f81f7fd194c

-- Generated from F:/20261008/FullFormalization\FullFormalization\MasterCertificate.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.MasterCertificate

  Source section 12: the telescoping step that turns the four *local*
  certificate identities into the master certificate (7.1)

      τ‖r‖² - F_N = Σ_{j=0}^{N-1} a_j I_{j,j+1} + Σ_{j=0}^{N} b_j I_{⋆,j}
                    + Σ_{j=0}^{N-1} S_j.

  This file isolates the pure summation content.  The local identities enter
  as hypotheses:

    * `hinit`  — (9.1), rewritten as `-V_1 = a_0(I_{⋆,0} + I_{0,1}) + S_0`;
    * `hstep`  — (10.1) for `1 ≤ j ≤ N-2` together with (11.1) at `j = N-1`;
    * `hend`   — (11.2);
    * `hb0`    — `b_0 = a_0` (source line 1329: `b_0 = a_0 - a_{-1} = a_0`,
                 using `a_{-1} = 0` from (4.12)).

  Once the concrete local identities land, (7.1) is `telescope` applied to
  them — see `FORMALIZATION_STATUS.md`.
-/

import Mathlib

set_option linter.unusedSectionVars false

namespace FullFormalization



end FullFormalization

open FullFormalization

set_option linter.unusedSectionVars false

open FullFormalization in

theorem solution {N : ℕ} (hN : 2 ≤ N)
    (V : ℕ → ℝ) (a b Ii Is S : ℕ → ℝ) (tauR2 FN : ℝ)
    (hb0 : b 0 = a 0)
    (hinit : V 1 = -(a 0 * (Is 0 + Ii 0) + S 0))
    (hstep : ∀ j, 1 ≤ j → j ≤ N - 1 →
      V (j + 1) - V j = -(b j * Is j + a j * Ii j + S j))
    (hend : tauR2 - FN = -V N + b N * Is N) :
    tauR2 - FN = (∑ j ∈ Finset.range N, a j * Ii j)
      + (∑ j ∈ Finset.range (N + 1), b j * Is j)
      + (∑ j ∈ Finset.range N, S j) := by
  have hN1 : 1 ≤ N := by omega
  have hNm : N - 1 + 1 = N := Nat.sub_add_cancel hN1
  -- telescoping: `V N - V 1` is the sum of the local decrements
  have htel : V N - V 1 = -((∑ i ∈ Finset.range (N - 1), b (i + 1) * Is (i + 1))
      + (∑ i ∈ Finset.range (N - 1), a (i + 1) * Ii (i + 1))
      + (∑ i ∈ Finset.range (N - 1), S (i + 1))) := by
    have hsub := Finset.sum_range_sub (fun k => V (k + 1)) (N - 1)
    rw [hNm, zero_add] at hsub
    have hcongr : ∀ i ∈ Finset.range (N - 1),
        V (i + 1 + 1) - V (i + 1) =
          -(b (i + 1) * Is (i + 1) + a (i + 1) * Ii (i + 1) + S (i + 1)) := by
      intro i hi
      have hi' : i + 1 ≤ N - 1 := by
        have := Finset.mem_range.mp hi
        omega
      exact hstep (i + 1) (by omega) hi'
    have hA : (∑ i ∈ Finset.range (N - 1),
          -(b (i + 1) * Is (i + 1) + a (i + 1) * Ii (i + 1) + S (i + 1)))
        = -((∑ i ∈ Finset.range (N - 1), b (i + 1) * Is (i + 1))
            + (∑ i ∈ Finset.range (N - 1), a (i + 1) * Ii (i + 1))
            + (∑ i ∈ Finset.range (N - 1), S (i + 1))) := by
      simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib]
    exact hsub.symm.trans ((Finset.sum_congr rfl hcongr).trans hA)
  -- split each sum at its first index
  have hsplit_a : (∑ j ∈ Finset.range N, a j * Ii j)
      = (∑ i ∈ Finset.range (N - 1), a (i + 1) * Ii (i + 1)) + a 0 * Ii 0 := by
    conv_lhs => rw [← hNm]
    rw [Finset.sum_range_succ']
  have hsplit_b : (∑ j ∈ Finset.range N, b j * Is j)
      = (∑ i ∈ Finset.range (N - 1), b (i + 1) * Is (i + 1)) + b 0 * Is 0 := by
    conv_lhs => rw [← hNm]
    rw [Finset.sum_range_succ']
  have hsplit_S : (∑ j ∈ Finset.range N, S j)
      = (∑ i ∈ Finset.range (N - 1), S (i + 1)) + S 0 := by
    conv_lhs => rw [← hNm]
    rw [Finset.sum_range_succ']
  have hsplit_bN : (∑ j ∈ Finset.range (N + 1), b j * Is j)
      = (∑ j ∈ Finset.range N, b j * Is j) + b N * Is N :=
    Finset.sum_range_succ _ N
  rw [hsplit_bN, hsplit_b, hsplit_a, hsplit_S, hb0]
  linarith [htel, hend, hinit]
