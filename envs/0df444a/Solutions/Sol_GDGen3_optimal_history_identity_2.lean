-- Prove2me | solution 2 for GDGen3.optimal_history_identity
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:54:10.922162+00:00
-- url     : https://prove2.me/submissions/0e317dd6-6805-4774-a232-2e554b2f8296

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_internal_reduction
import Theorems.Thm_GDGen3_rootXi_zero
import Theorems.Thm_GDGen3_rootXi_pos
import Theorems.Thm_GDGen3_rootXi_quad
import Theorems.Thm_GDGen3_rootXi_quad7
import Theorems.Thm_GDGen3_rootXi_pin
import Theorems.Thm_GDGen3_M_boundary
import Theorems.Thm_GDGen3_inverse_power_boundary

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hboundary : 1 / r ^ N = 1 + (N : ℝ) * (1 + r))
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i) :
    (1 + r) * smallK N (1 + r) f (fun i => P i i) =
      2 * (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
        if i = j then 0 else ell r (rootXi r N) N i j * Qv (1 + r) f P i j) := by
  have h := internal_reduction r N hN (rootXi r N) hr hr1
    (fun i hi => rootXi_pos r hr hr1 N i hi) (rootXi_zero r N)
    (fun i hi => rootXi_quad r hr hr1 N i hi)
    (fun i hi => rootXi_quad7 r hr hr1 N i hi) (rootXi_pin r hr hr1 N hN) f P hP
  rw [h, M_boundary r hr hr1 N hN hboundary, inverse_power_boundary r hr N hboundary]
  unfold smallK
  ring
