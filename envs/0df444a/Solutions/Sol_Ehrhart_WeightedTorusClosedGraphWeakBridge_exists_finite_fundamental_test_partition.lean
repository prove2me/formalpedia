-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.exists_finite_fundamental_test_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/463ffcf0-a1b1-421d-921e-db2db2cc4701

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_coverRealTest_eq_zero_of_notMem_tsupport
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_coverFundamentalInterior_isOpen
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_self_mem_coverFundamentalInterior

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusClosedGraphWeakBridge
open Set Function MeasureTheory Filter
open WeightedTorusHilbert WeightedBrascampSaturation ComplexKillingSaturationBridge
open DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
  Manifold ContDiff
namespace Ehrhart.WeightedTorusClosedGraphWeakBridge
theorem _root_.solution {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψcompact : HasCompactSupport ψ) :
    ∃ (s : Finset (TorusCharacters.LogSpace n))
      (χ : TorusCharacters.LogSpace n →
        TorusCharacters.LogSpace n → ℝ),
      (∀ i, ContDiff ℝ 1 (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆
        coverFundamentalInterior (coverCenteredFundamentalBase i)) ∧
      (∀ z : TorusCharacters.LogSpace n,
        ψ z = ∑ i ∈ s, χ i z * ψ z) := by
  classical
  let E := TorusCharacters.LogSpace n
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
    exact (ρ i).contMDiff.contDiff.of_le (by simp)
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
      rw [← Finset.sum_mul, hone, one_mul]
    · rw [coverRealTest_eq_zero_of_notMem_tsupport hz]
      simp
end Ehrhart.WeightedTorusClosedGraphWeakBridge
