-- Prove2me | solution 1 for Convex.sum_mem_of_sum_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:36:37.419803+00:00
-- url     : https://prove2.me/submissions/ca0141aa-ab5b-4da8-9fec-ceafe9ab36db

import Definitions.Def_MarkovProcess_V3H_Semigroup_Generation_6c19e644
import Definitions.Def_MarkovProcess_V3H_Semigroup_InvariantSet_e2a740e2
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Invariant sets and strong semigroup limits

This file isolates the topological part of transferring an invariant set from
bounded Yosida approximations to the generated semigroup.  It also records the
finite-iterate consequence of invariance under a normalized resolvent.  The
Poisson-series argument transferring the latter invariance to each exponential
approximant is in `Semigroup/PoissonInvariant.lean`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology

noncomputable section

namespace MarkovProcess.Semigroup



namespace PreservesSet

variable {E F G : Type*} {C : Set E} {D : Set F} {K : Set G}







end PreservesSet

end MarkovProcess.Semigroup

namespace Convex

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end Convex

namespace MarkovProcess.Semigroup

namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



section CompleteSpace

variable [CompleteSpace E]





end CompleteSpace

end ContractiveResolvent

end MarkovProcess.Semigroup


open Convex
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Invariant sets and strong semigroup limits

This file isolates the topological part of transferring an invariant set from
bounded Yosida approximations to the generated semigroup.  It also records the
finite-iterate consequence of invariance under a normalized resolvent.  The
Poisson-series argument transferring the latter invariance to each exponential
approximant is in `Semigroup/PoissonInvariant.lean`.
-/

open Filter Set Topology




variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Convex

end Convex
open Convex
theorem solution {C : Set E} (hC : Convex ℝ C) (hzero : 0 ∈ C)
    (s : Finset ι) (w : ι → ℝ) (z : ι → E)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i ≤ 1)
    (hz : ∀ i ∈ s, z i ∈ C) :
    ∑ i ∈ s, w i • z i ∈ C := by
  classical
  let s' : Finset (Option ι) := insert none (s.image some)
  let w' : Option ι → ℝ
    | none => 1 - ∑ i ∈ s, w i
    | some i => w i
  let z' : Option ι → E
    | none => 0
    | some i => z i
  have hnone : none ∉ s.image some := by
    simp
  have hw' : ∀ i ∈ s', 0 ≤ w' i := by
    intro i hi
    rcases i with _ | i
    · exact sub_nonneg.mpr hsum
    · exact hw i (by
        have : some i ∈ s.image some := by
          simpa only [s', Finset.mem_insert, Option.some_ne_none, false_or] using hi
        simpa only [Finset.mem_image, Option.some.injEq, exists_eq_right] using this)
  have hz' : ∀ i ∈ s', z' i ∈ C := by
    intro i hi
    rcases i with _ | i
    · exact hzero
    · exact hz i (by
        have : some i ∈ s.image some := by
          simpa only [s', Finset.mem_insert, Option.some_ne_none, false_or] using hi
        simpa only [Finset.mem_image, Option.some.injEq, exists_eq_right] using this)
  have hsum' : ∑ i ∈ s', w' i = 1 := by
    simp [s', hnone, w']
  have hmem := hC.sum_mem hw' hsum' hz'
  simpa [s', hnone, z', w'] using hmem
