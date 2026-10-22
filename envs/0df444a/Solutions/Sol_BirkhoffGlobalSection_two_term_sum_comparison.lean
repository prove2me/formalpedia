-- Prove2me | solution 1 for BirkhoffGlobalSection.two_term_sum_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:40:02.243719+00:00
-- url     : https://prove2.me/submissions/75642db1-fb6a-4aa7-a594-a083dfdf10f9

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.ProperSpace

open scoped Topology
open Set Metric Filter
open BirkhoffGlobalSection


open BirkhoffGlobalSection NormedSpace Set Metric Filter
open scoped Topology unitInterval BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem solution {ι : Type*} [Fintype ι]
    (f g : ι → ℝ) (u v : ι) (huv : u ≠ v)
    (hsame : ∀ i, i ≠ u → i ≠ v → f i = g i)
    (hle : (∑ i, f i) ≤ ∑ i, g i) : f u + f v ≤ g u + g v := by
  classical
  have hv : v ∈ (Finset.univ : Finset ι).erase u := by
    simp [huv.symm]
  have he : (∑ i ∈ ((Finset.univ : Finset ι).erase u).erase v, f i) =
      ∑ i ∈ ((Finset.univ : Finset ι).erase u).erase v, g i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hsame i (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      (Finset.mem_erase.mp hi).1
  have hf1 := Finset.sum_erase_add Finset.univ f (Finset.mem_univ u)
  have hg1 := Finset.sum_erase_add Finset.univ g (Finset.mem_univ u)
  have hf2 := Finset.sum_erase_add (Finset.univ.erase u) f hv
  have hg2 := Finset.sum_erase_add (Finset.univ.erase u) g hv
  linarith
