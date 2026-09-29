-- Prove2me | solution 1 for Freiman.lower_initial_n_factorization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T00:23:49.533062+00:00
-- url     : https://prove2.me/submissions/23f5377f-28c6-4c3f-b2be-8dd91f9a7774

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution (c : LowerInitialNCase) (hv : lowerInitialNCertificateValid c) (x : ℝ) :
    lowerInitialNPolyEval c x = (x^2-86*x+1)*lowerInitialNQuotEval c x := by
  simp only [lowerInitialNCertificateValid] at hv
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := hv
  simp only [lowerInitialNPolyEval, lowerInitialNQuotEval, Fin.sum_univ_five, Fin.sum_univ_three,
    h0, h1, h2, h3, h4, certFieldVal, certFieldAdd, certFieldSub, certFieldScale,
    Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue]
  norm_num
  ring
