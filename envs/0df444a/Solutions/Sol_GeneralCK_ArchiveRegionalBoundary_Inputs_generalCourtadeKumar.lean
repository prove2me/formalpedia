-- Prove2me | solution 1 for GeneralCK.ArchiveRegionalBoundary.Inputs.generalCourtadeKumar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T23:04:55.676834+00:00
-- url     : https://prove2.me/submissions/fbc9ca7b-ccb6-4861-a11d-19ab4be2e71d

import Definitions.Def_GeneralCK_finite_law_regional
import Definitions.Def_GeneralCK_statement
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_GeneralCK_ArchiveRegionalBoundary_Inputs_toFiniteHybridBellman
import Theorems.Thm_GeneralCK_generalCourtadeKumar_of_finiteHybridBellman

namespace GeneralCK.ArchiveRegionalBoundary





theorem _root_.solution (h : Inputs) : GeneralCK.GeneralCourtadeKumar :=
  GeneralCK.generalCourtadeKumar_of_finiteHybridBellman h.toFiniteHybridBellman




end GeneralCK.ArchiveRegionalBoundary
