-- Prove2me | solution 1 for FD1D.potentialRemainder_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:40.840544+00:00
-- url     : https://prove2.me/submissions/2a6ed2ee-7cb2-4647-bb9d-722de52fa1be

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
import Theorems.Thm_FD1D_nodeMass_nonneg


set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
namespace FD1D
theorem _root_.solution
    {L : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    {q : ∀ d, DyadicNode d → ℝ}
    (ha : 0 < a) (hq : ∀ d v, q d v ≤ 1) :
    0 ≤ potentialRemainder L a N q := by
  unfold potentialRemainder
  apply Finset.sum_nonneg
  intro d hd
  apply Finset.sum_nonneg
  intro v hv
  have hp : 0 ≤ nodeMass (d + 1) v := nodeMass_nonneg _ _
  have h1q : 0 ≤ 1 - q (d + 1) v := sub_nonneg.mpr (hq _ _)
  positivity
end FD1D
