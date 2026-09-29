-- Prove2me | solution 1 for GeneralCK.ArchiveRegionalBoundary.Inputs.toFiniteHybridBellman
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T23:04:21.129788+00:00
-- url     : https://prove2.me/submissions/26199eac-21be-4d6d-9b15-6aa9e8e9f10d

import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_finite_law_regional
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
import Theorems.Thm_GeneralCK_finiteHybridBellman_of_canonical

namespace GeneralCK.ArchiveRegionalBoundary



theorem _root_.solution (h : Inputs) : GeneralCK.FiniteHybridBellman := by
  apply GeneralCK.finiteHybridBellman_of_canonical
  intro k μ hab hsum
  by_cases hb : μ.b ≤ 1 / 2
  · exact h.sameSide k μ hab hsum hb
  · exact h.oppositeSide k μ hab hsum (le_of_lt (lt_of_not_ge hb))






end GeneralCK.ArchiveRegionalBoundary
