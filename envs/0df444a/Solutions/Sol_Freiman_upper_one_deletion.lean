-- Prove2me | solution 1 for Freiman.upper_one_deletion
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:35:39.108202+00:00
-- url     : https://prove2.me/submissions/5a1a0227-b58f-4be0-9e13-49116478dc45

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_deletion_both
import Theorems.Thm_Freiman_upper_deletion_left
import Theorems.Thm_Freiman_upper_deletion_right
import Theorems.Thm_Freiman_upper_deletion_small
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman
open Filter Topology

theorem solution (C D L R : upperInterval) (hC : 0 < upperLength C) (hCD : upperLength C ≤ upperLength D) (hs : upperNormalSplit D L R) :
    upperDerived C D ⊆ upperDerived C L ∪ upperDerived C R := by
  by_cases hL : upperLength C ≤ upperLength L
  · by_cases hR : upperLength C ≤ upperLength R
    · exact upper_deletion_both C D L R hC hCD hs hL hR
    · exact upper_deletion_left C D L R hC hCD hs hL (lt_of_not_ge hR)
  · by_cases hR : upperLength C ≤ upperLength R
    · exact upper_deletion_right C D L R hC hCD hs (lt_of_not_ge hL) hR
    · exact upper_deletion_small C D L R hC hCD hs (lt_of_not_ge hL) (lt_of_not_ge hR)
