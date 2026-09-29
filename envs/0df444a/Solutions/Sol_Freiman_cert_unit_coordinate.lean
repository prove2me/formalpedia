-- Prove2me | solution 1 for Freiman.cert_unit_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:36:22.740392+00:00
-- url     : https://prove2.me/submissions/56915dbf-c3ac-4ca2-8664-67e206c9d085

import Definitions.Def_Freiman_certificates
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

open Freiman
open scoped BigOperators


theorem solution :
    ∀ a b x : ℝ, a < b → x ∈ Set.Icc a b → (x-a)/(b-a) ∈ Set.Icc (0:ℝ) 1 := by
  intro a b x hab hx
  have hd : 0 < b-a := sub_pos.mpr hab
  constructor
  · exact div_nonneg (sub_nonneg.mpr hx.1) hd.le
  · apply (div_le_one hd).mpr
    linarith [hx.2]


#print axioms solution
