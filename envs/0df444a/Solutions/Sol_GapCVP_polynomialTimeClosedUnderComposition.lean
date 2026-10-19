-- Prove2me | solution 1 for GapCVP.polynomialTimeClosedUnderComposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/7d8b68f5-2782-4994-b24d-c8c56cf68ed4

import Mathlib
import Definitions.Def_GapCVP

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
namespace GapCVP
theorem _root_.solution :
    PolynomialTimeClosedUnderComposition := by
  simp only [GapCVP.PolynomialTimeClosedUnderComposition, decide_eq_true_eq] at *
  intro first second firstMachine secondMachine
  exact ⟨TMComposition.computableInPolyTime
    firstMachine.some secondMachine.some⟩
end GapCVP
