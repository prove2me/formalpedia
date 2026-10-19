-- Prove2me | solution 1 for Ehrhart.TorusDeckWeightedUnfolding.exists_finite_complex_fundamental_test_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/fd339222-9c75-4d9d-b128-508218168e1b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_coverFundamentalInterior_isOpen
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_self_mem_coverFundamentalInterior

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusDeckWeightedUnfolding
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open WeightedTorusDistributionBridge WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault
open WeightedTorusBochner TorusWeightedBaseAE
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold
namespace Ehrhart.TorusDeckWeightedUnfolding
theorem _root_.solution
    {n : ℕ}
    {ψ : LogSpace n → ℂ}
    (hψcompact : HasCompactSupport ψ) :
    ∃ (s : Finset (LogSpace n))
      (χ : LogSpace n → LogSpace n → ℝ),
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆
        coverFundamentalInterior (coverCenteredFundamentalBase i)) ∧
      (∀ z : LogSpace n,
        ψ z = ∑ i ∈ s, (χ i z : ℂ) * ψ z) := by
  classical
  let E := LogSpace n
  let U : E → Set E := fun z =>
    coverFundamentalInterior (coverCenteredFundamentalBase z)
  have hUopen : ∀ z : E, IsOpen (U z) := fun z =>
    coverFundamentalInterior_isOpen (coverCenteredFundamentalBase z)
  have hUcover : tsupport ψ ⊆ ⋃ z : E, U z := by
    intro z _
    exact Set.mem_iUnion_of_mem z
      (self_mem_coverFundamentalInterior z)
  obtain ⟨ρ, hρ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate
      (I := 𝓘(ℝ, E)) (isClosed_tsupport ψ) U hUopen hUcover
  have hfinite :
      {i : E | (Function.support (ρ i) ∩ tsupport ψ).Nonempty}.Finite :=
    ρ.locallyFinite.finite_nonempty_inter_compact hψcompact
  let s : Finset E := hfinite.toFinset
  refine ⟨s, fun i z => ρ i z, ?_, ?_, ?_⟩
  · intro i
    exact (ρ i).contMDiff.contDiff
  · intro i
    exact hρ i
  · intro z
    by_cases hz : z ∈ tsupport ψ
    · have hsubset : ρ.finsupport z ⊆ s := by
        intro i hi
        apply hfinite.mem_toFinset.mpr
        refine ⟨z, ?_, hz⟩
        exact (ρ.mem_finsupport z).mp hi
      have hone := ρ.sum_finsupport' z hz hsubset
      have honeC : (∑ i ∈ s, (ρ i z : ℂ)) = 1 := by
        exact_mod_cast hone
      calc
        ψ z = (1 : ℂ) * ψ z := by simp
        _ = (∑ i ∈ s, (ρ i z : ℂ)) * ψ z := by rw [honeC]
        _ = ∑ i ∈ s, (ρ i z : ℂ) * ψ z := by
          rw [Finset.sum_mul]
    · have hz0 : ψ z = 0 :=
        image_eq_zero_of_notMem_tsupport hz
      simp [hz0]
end Ehrhart.TorusDeckWeightedUnfolding
