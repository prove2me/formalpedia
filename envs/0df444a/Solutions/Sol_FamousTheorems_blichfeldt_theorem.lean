-- Prove2me | solution 1 for FamousTheorems.blichfeldt_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:13:25.620194+00:00
-- url     : https://prove2.me/submissions/7211f442-e7d7-4dbd-bfb7-9bf267a0810e

import Mathlib

open MeasureTheory Pointwise

theorem solution {E L : Type*} [MeasurableSpace E] {μ : Measure E} {F s : Set E} [AddGroup L] [Countable L]
    [AddAction L E] [MeasurableSpace L] [MeasurableVAdd L E] [VAddInvariantMeasure L E μ]
    (fund : IsAddFundamentalDomain L F μ) (hS : NullMeasurableSet s μ) (h : μ F < μ s) :
    ∃ x y : L, x ≠ y ∧ ¬Disjoint (x +ᵥ s) (y +ᵥ s) :=
  MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd fund hS h
