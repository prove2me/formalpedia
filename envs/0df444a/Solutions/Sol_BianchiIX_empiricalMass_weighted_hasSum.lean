-- Prove2me | solution 1 for BianchiIX.empiricalMass_weighted_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:07:57.96108+00:00
-- url     : https://prove2.me/submissions/5ec79b46-3bab-4836-86e9-81e0d86f8cb7

import Definitions.Def_BianchiIX_Statistics_EmpiricalMass
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Filter
open scoped Topology
open BianchiIX
noncomputable section
open scoped Classical


theorem solution {ι : Type*} (label : ℕ → ι) (N : ℕ) (f : ι → ℝ) :
    HasSum (fun i => empiricalMass label N i * f i)
      (((N + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range (N + 1), f (label j)) := by
  have hj (j : ℕ) : HasSum (fun i => (if i = label j then (1 : ℝ) else 0) * f i) (f (label j)) := by
    convert! hasSum_ite_eq (label j) (f (label j)) using 1
    funext i
    split_ifs with h <;> simp [h]
  have h := (hasSum_sum (fun j (_ : j ∈ Finset.range (N + 1)) => hj j)).mul_left
    (((N + 1 : ℕ) : ℝ)⁻¹)
  simpa only [empiricalMass, mul_assoc, Finset.sum_mul] using h
