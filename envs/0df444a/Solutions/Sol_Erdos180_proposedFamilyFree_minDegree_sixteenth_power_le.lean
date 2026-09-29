-- Prove2me | solution 1 for Erdos180.proposedFamilyFree_minDegree_sixteenth_power_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:04:29.293034+00:00
-- url     : https://prove2.me/submissions/679f19ca-239c-4009-99db-55e9079ebd0a

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Theorems.Thm_Erdos180_proposedFamilyFree_minDegree_polynomial_le

open Erdos180
open Finset SimpleGraph

theorem solution
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hn : 0 < n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hd : 2 ≤ d)
    (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    (d : ℝ) ^ 16 ≤ 1769472 * (n : ℝ) ^ 5 := by
  have hraw := proposedFamilyFree_minDegree_polynomial_le
    host hn hfree hbip d hdegree hthreshold
  have hshape :
      (d : ℝ) ^ 5 * ((d - 1 : ℕ) : ℝ) ^ 11 ≤
        864 * (n : ℝ) ^ 5 := by
    convert hraw using 1
    push_cast
    ring
  have hdone : 1 ≤ d := by omega
  have hhalf : (d : ℝ) ≤ 2 * ((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hdone, Nat.cast_one]
    have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  calc
    (d : ℝ) ^ 16 = (d : ℝ) ^ 5 * (d : ℝ) ^ 11 := by ring
    _ ≤ (d : ℝ) ^ 5 *
        (2 * ((d - 1 : ℕ) : ℝ)) ^ 11 := by
      gcongr
    _ = 2 ^ (11 : ℕ) *
        ((d : ℝ) ^ 5 * ((d - 1 : ℕ) : ℝ) ^ 11) := by ring
    _ ≤ 2 ^ (11 : ℕ) * (864 * (n : ℝ) ^ 5) := by
      gcongr
    _ = 1769472 * (n : ℝ) ^ 5 := by ring
