-- Prove2me | solution 1 for GarrettFA.isEquicontinuousSet_iff_of_isStrictColimit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:21:29.770955+00:00
-- url     : https://prove2.me/submissions/30da4529-07b7-4c77-934d-5b0421688e8d

import Mathlib
import Definitions.Def_GarrettFA_IsEquicontinuousSet
import Definitions.Def_GarrettFA_IsStrictColimit

open Topology Set Filter Pointwise Uniformity

namespace GABS

lemma good_nhd {𝕜 : Type*} [RCLike 𝕜] {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [Module ℝ Y]
    [IsScalarTower ℝ 𝕜 Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul 𝕜 Y]
    [LocallyConvexSpace ℝ Y] (U : Set Y) (hU : U ∈ 𝓝 (0 : Y)) :
    ∃ W ∈ 𝓝 (0 : Y), IsClosed W ∧ Convex ℝ W ∧ (∀ y ∈ W, -y ∈ W) ∧ W ⊆ U := by
  have : ContinuousConstSMul ℝ Y := ⟨fun r => by
    have := continuous_const_smul (algebraMap ℝ 𝕜 r) (T := Y)
    convert this using 1
    ext y; exact (algebraMap_smul 𝕜 r y).symm⟩
  obtain ⟨V1, hV1, hV1c, hV1U⟩ := exists_mem_nhds_isClosed_subset hU
  obtain ⟨C, ⟨hC0, hCc⟩, hCV⟩ := (LocallyConvexSpace.convex_basis_zero ℝ Y).mem_iff.mp hV1
  set C' := C ∩ -C with hC'
  have hC'0 : C' ∈ 𝓝 (0 : Y) := inter_mem hC0 (neg_mem_nhds_zero Y hC0)
  have hC'c : Convex ℝ C' := hCc.inter hCc.neg
  have hC's : -C' = C' := by
    rw [hC', Set.inter_neg, neg_neg, Set.inter_comm]
  refine ⟨closure C', mem_of_superset hC'0 subset_closure, isClosed_closure, hC'c.closure,
    ?_, ?_⟩
  · intro y hy
    have : -y ∈ -closure C' := by simpa using hy
    rwa [neg_closure, hC's] at this
  · exact (closure_minimal (inter_subset_left.trans hCV) hV1c).trans hV1U



end GABS
namespace GABS

lemma balancedCore_convex {𝕜 : Type*} [RCLike 𝕜] {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y]
    [Module ℝ Y] [IsScalarTower ℝ 𝕜 Y] (W : Set Y) (h0 : (0 : Y) ∈ W) (hW : Convex ℝ W) :
    Convex ℝ (balancedCore 𝕜 W) := by
  rw [balancedCore_eq_iInter h0]
  refine convex_iInter fun r => convex_iInter fun _ => ?_
  intro x hx y hy a b ha hb hab
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  refine ⟨a • u + b • v, hW hu hv ha hb hab, ?_⟩
  simp only [smul_add]
  rw [← algebraMap_smul 𝕜 a (r • u), ← algebraMap_smul 𝕜 b (r • v), ← algebraMap_smul 𝕜 a u,
    ← algebraMap_smul 𝕜 b v, smul_smul, smul_smul, smul_smul, smul_smul, mul_comm r, mul_comm r]

end GABS

open GABS in
theorem solution {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V] {F : ℕ → Submodule 𝕜 V} (hF : GarrettFA.IsStrictColimit 𝕜 F)
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [Module ℝ Y] [IsScalarTower ℝ 𝕜 Y]
    [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul 𝕜 Y] [LocallyConvexSpace ℝ Y]
    [T2Space Y]
    (E : Set (V →L[𝕜] Y)) :
    GarrettFA.IsEquicontinuousSet ((fun T : V →L[𝕜] Y => (T : V → Y)) '' E) ↔
      ∀ i, GarrettFA.IsEquicontinuousSet ((fun T : V →L[𝕜] Y => fun y : F i => T y) '' E) := by
  constructor
  · intro h i U hU
    obtain ⟨N, hN, hNU⟩ := h U hU
    refine ⟨{y : F i | (y : V) ∈ N}, ?_, ?_⟩
    · exact continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hN)
    · rintro _ ⟨T, hT, rfl⟩ y hy
      exact hNU (T : V → Y) ⟨T, hT, rfl⟩ hy
  · intro h U hU
    obtain ⟨W, hW0, -, hWcv, -, hWU⟩ := good_nhd (𝕜 := 𝕜) U hU
    have h0W : (0 : Y) ∈ W := mem_of_mem_nhds hW0
    set W' := balancedCore 𝕜 W with hW'
    have hW'0 : W' ∈ 𝓝 (0 : Y) := balancedCore_mem_nhds_zero hW0
    have hW'cv : Convex ℝ W' := balancedCore_convex W h0W hWcv
    have hW'b : Balanced 𝕜 W' := balancedCore_balanced W
    set A := {x : V | ∀ T ∈ E, T x ∈ W'} with hA
    have hAn : A ∈ 𝓝 (0 : V) := by
      apply hF.mem_nhds_of_absConvex A
      · intro a ha
        rintro _ ⟨x, hx, rfl⟩ T hT
        rw [T.map_smul]
        exact hW'b.smul_mem ha (hx T hT)
      · intro x hx y hy a b ha hb hab T hT
        rw [map_add, T.map_smul_of_tower, T.map_smul_of_tower]
        exact hW'cv (hx T hT) (hy T hT) ha hb hab
      · intro n
        obtain ⟨N, hN, hNU⟩ := h n W' hW'0
        refine mem_of_superset hN ?_
        intro y hy T hT
        exact hNU _ ⟨T, hT, rfl⟩ hy
    refine ⟨A, hAn, ?_⟩
    rintro _ ⟨T, hT, rfl⟩ x hx
    exact hWU (balancedCore_subset W (hx T hT))
