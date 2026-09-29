-- Prove2me | solution 1 for Freiman.trunk_diagonal_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:37.600727+00:00
-- url     : https://prove2.me/submissions/f6be635f-5321-415b-a375-aeff337bd3c5

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_diagonal_factor
import Theorems.Thm_Freiman_trunk_bilinear_corner_positive
import Theorems.Thm_Freiman_trunk_diagonal_corners
import Theorems.Thm_Freiman_trunk_diagonal_polynomial_from_corners

open Freiman

theorem solution (C : TrunkCatalog) (w : TrunkWitness) (hw : trunkWitnessValid C w) (hn : w.diagonal ≠ 0)
    (r s : ℝ) (hm : certRectangleMem w.rectangle r s) (hs : 0 ≤ (w.diagonal : ℝ)*(r-s)) :
    0 ≤ certPolyEval (trunkPolynomial C w) r s := by
  exact trunk_diagonal_polynomial_from_corners trunk_diagonal_factor trunk_bilinear_corner_positive C w hw hn
    (trunk_diagonal_corners C w hw hn) r s hm hs
