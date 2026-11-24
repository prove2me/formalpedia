-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.strip_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:56.72431+00:00
-- url     : https://prove2.me/submissions/5e06d45d-6f70-4d85-9049-a0ca6e10a3b2

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_le_iff_lt_colHeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_strip_height


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
theorem _root_.solution {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (hν : Antitone ν) (hμ : Antitone μ)
    (hs : HStrip ν μ b) (c : ℤ) (m : Fin n) :
    (colHeight ν c ≠ colHeight μ c ∧ m.val = min (colHeight ν c) (colHeight μ c)) ↔
      c ∈ Finset.Ioc (μ m) (ν m) := by
  have e1 := Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.le_iff_lt_colHeight hμ c m
  have e2 := Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.le_iff_lt_colHeight hν c m
  have hs2 := Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.strip_height hν hμ hs c
  have hmin : min (Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight ν c) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight μ c) = Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight μ c :=
    min_eq_right (by rcases hs2 with h | h <;> omega)
  rw [hmin, Finset.mem_Ioc]
  constructor
  · rintro ⟨hne, hm⟩
    refine ⟨not_le.mp fun h => ?_, e2.mpr ?_⟩
    · have := e1.mp h
      omega
    · rcases hs2 with h | h
      · exact absurd h hne
      · omega
  · rintro ⟨h1, h2⟩
    have a1 : ¬ m.val < Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight μ c := fun h => not_le.mpr h1 (e1.mpr h)
    have a2 := e2.mp h2
    rcases hs2 with h | h <;> refine ⟨?_, ?_⟩ <;> omega
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
