-- Prove2me | solution 1 for BianchiIX.root_sdiff_survivingSet
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:00:22.339832+00:00
-- url     : https://prove2.me/submissions/b4843f36-f30d-479b-bee7-3ee10ec757d5

import Definitions.Def_BianchiIX_Statistics_StoppedMass
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim

open BianchiIX
noncomputable section
open Set MeasureTheory
open scoped ENNReal


theorem solution {X : Type*} (K : ℕ → Set X) (hK : Antitone K) :
    K 0 \ survivingSet K = ⋃ m, firstStoppedSet K m := by
  classical
  ext x
  simp only [survivingSet, firstStoppedSet, mem_sdiff, mem_iInter, not_forall, mem_iUnion]
  constructor
  · rintro ⟨h0, hex⟩
    have hN := Nat.find_spec hex
    have hNpos : 0 < Nat.find hex := by
      by_contra h
      have hz : Nat.find hex = 0 := by omega
      exact hN (hz ▸ h0)
    refine ⟨Nat.find hex - 1, ?_, ?_⟩
    · by_contra hprev
      exact Nat.find_min hex (by omega) hprev
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ Nat.find hex)] using hN
  · rintro ⟨m, hm, hn⟩
    exact ⟨hK (Nat.zero_le m) hm, m + 1, hn⟩
