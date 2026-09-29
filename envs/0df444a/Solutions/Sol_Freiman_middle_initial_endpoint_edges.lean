-- Prove2me | solution 1 for Freiman.middle_initial_endpoint_edges
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:49:21.235734+00:00
-- url     : https://prove2.me/submissions/d83149f6-cdf0-40af-aff0-c72fdc0b74c4

import Definitions.Def_Freiman_middleRoots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.GetD
open Freiman
set_option autoImplicit false
theorem solution :
    (∀ i : Fin 15, middleRootCertificate i) →
      (middleBounds (middleRoot 14)).1 < Real.sqrt 21 ∧ (128/25:ℝ)<(middleBounds (middleRoot 0)).2 := by
  intro hc
  constructor
  · apply (hc 14).2.2.1.trans
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ 21 by norm_num)
    have hp := Real.sqrt_nonneg (21:ℝ)
    norm_num [middleInnerLeft]
    nlinarith
  · apply lt_trans _ (hc 0).2.2.2
    norm_num [middleInnerRight]
#print axioms solution
