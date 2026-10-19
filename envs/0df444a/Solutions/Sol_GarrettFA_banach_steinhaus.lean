-- Prove2me | solution 1 for GarrettFA.banach_steinhaus
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:18:10.779831+00:00
-- url     : https://prove2.me/submissions/877daf06-2bb8-445c-b9f9-879a71c1def2

import Mathlib
import Definitions.Def_GarrettFA_IsEquicontinuousSet
import Definitions.Def_GarrettFA_IsFrechetSpace
import Definitions.Def_GarrettFA_IsLFSpace

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


lemma core {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [Module ℝ Y] [IsScalarTower ℝ 𝕜 Y]
    [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul 𝕜 Y]
    (E : Set (V →L[𝕜] Y))
    (hE : ¬ IsMeagre {x : V | Bornology.IsVonNBounded 𝕜 ((fun T : V →L[𝕜] Y => T x) '' E)})
    (W : Set Y) (hW0 : W ∈ 𝓝 (0 : Y)) (hWc : IsClosed W) (hWcv : Convex ℝ W)
    (hWs : ∀ y ∈ W, -y ∈ W) : {x : V | ∀ T ∈ E, T x ∈ W} ∈ 𝓝 (0 : V) := by
  set B := {x : V | Bornology.IsVonNBounded 𝕜 ((fun T : V →L[𝕜] Y => T x) '' E)} with hB
  set A := {x : V | ∀ T ∈ E, T x ∈ W} with hA
  have hAc : IsClosed A := by
    have : A = ⋂ T ∈ E, (T : V → Y) ⁻¹' W := by ext x; simp [hA]
    rw [this]
    exact isClosed_biInter fun T _ => hWc.preimage T.continuous
  have hAs : ∀ x ∈ A, -x ∈ A := by
    intro x hx T hT; rw [map_neg]; exact hWs _ (hx T hT)
  have hAcv : Convex ℝ A := by
    intro x hx y hy a b ha hb hab T hT
    rw [map_add, T.map_smul_of_tower, T.map_smul_of_tower]
    exact hWcv (hx T hT) (hy T hT) ha hb hab
  -- B ⊆ ⋃ n, (n+1) • A
  have hcover : B ⊆ ⋃ n : ℕ, ((n + 1 : ℕ) : 𝕜) • A := by
    intro x hx
    obtain ⟨r, -, hr⟩ := (hx hW0).exists_pos
    obtain ⟨n, hn⟩ := exists_nat_ge r
    set c : 𝕜 := ((n + 1 : ℕ) : 𝕜) with hc
    have hcn : ‖c‖ = n + 1 := by rw [hc, RCLike.norm_natCast]; push_cast; ring
    have hc0 : c ≠ 0 := by rw [hc]; exact_mod_cast Nat.succ_ne_zero n
    have hsub := hr c (by rw [hcn]; linarith)
    refine mem_iUnion.mpr ⟨n, ?_⟩
    have : c⁻¹ • x ∈ A := by
      intro T hT
      obtain ⟨w, hw, hwx⟩ := hsub ⟨T, hT, rfl⟩
      have hwx' : T x = c • w := hwx.symm
      rw [T.map_smul, hwx', inv_smul_smul₀ hc0]
      exact hw
    have := smul_mem_smul_set (a := c) this
    rwa [smul_inv_smul₀ hc0] at this
  -- some (n+1) • A has nonempty interior
  have hint : ∃ n : ℕ, (interior (((n + 1 : ℕ) : 𝕜) • A)).Nonempty := by
    by_contra hcon
    push Not at hcon
    apply hE
    refine IsMeagre.mono hcover (isMeagre_iUnion fun n => ?_)
    apply IsNowhereDense.isMeagre
    have hc0 : ((n + 1 : ℕ) : 𝕜) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [(hAc.smul_of_ne_zero hc0).isNowhereDense_iff]
    exact hcon n
  obtain ⟨n, z, hz⟩ := hint
  have hc0 : ((n + 1 : ℕ) : 𝕜) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [interior_smul₀ hc0] at hz
  obtain ⟨x0, hx0, -⟩ := hz
  -- A is a neighbourhood of 0
  have hAnhd : A ∈ 𝓝 (0 : V) := by
    set O := interior A
    have hO : IsOpen O := isOpen_interior
    have h1 : (fun y : V => x0 + y) ⁻¹' O ∈ 𝓝 (0 : V) :=
      (hO.preimage (continuous_const.add continuous_id)).mem_nhds (by simpa using hx0)
    have h2 : (fun y : V => x0 - y) ⁻¹' O ∈ 𝓝 (0 : V) :=
      (hO.preimage (continuous_const.sub continuous_id)).mem_nhds (by simpa using hx0)
    refine mem_of_superset (inter_mem h1 h2) ?_
    rintro y ⟨hy1, hy2⟩
    have a1 : x0 + y ∈ A := interior_subset hy1
    have a2 : -x0 + y ∈ A := by
      have := hAs _ (interior_subset hy2); simpa [neg_sub, sub_eq_neg_add] using this
    have := hAcv a1 a2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    convert this using 1
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, smul_neg, add_neg_cancel, zero_add]
    norm_num
  exact hAnhd

end GABS

open Topology Set Filter Pointwise Uniformity

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
theorem solution {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [AddCommGroup X] [Module 𝕜 X] [Module ℝ X]
    [IsScalarTower ℝ 𝕜 X] [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul 𝕜 X] [T2Space X]
    (hX : GarrettFA.IsFrechetSpace 𝕜 X ∨ GarrettFA.IsLFSpace 𝕜 X)
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [Module ℝ Y] [IsScalarTower ℝ 𝕜 Y]
    [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul 𝕜 Y] [LocallyConvexSpace ℝ Y]
    [T2Space Y]
    (E : Set (X →L[𝕜] Y))
    (hE : ∀ x : X, Bornology.IsVonNBounded 𝕜 ((fun T : X →L[𝕜] Y => T x) '' E)) :
    GarrettFA.IsEquicontinuousSet ((fun T : X →L[𝕜] Y => (T : X → Y)) '' E) := by
  intro U hU
  obtain ⟨W, hW0, hWc, hWcv, hWs, hWU⟩ := good_nhd (𝕜 := 𝕜) U hU
  have h0W : (0 : Y) ∈ W := mem_of_mem_nhds hW0
  set W' := balancedCore 𝕜 W with hW'
  have hW'0 : W' ∈ 𝓝 (0 : Y) := balancedCore_mem_nhds_zero hW0
  have hW'c : IsClosed W' := hWc.balancedCore
  have hW'cv : Convex ℝ W' := balancedCore_convex W h0W hWcv
  have hW'b : Balanced 𝕜 W' := balancedCore_balanced W
  have hW's : ∀ y ∈ W', -y ∈ W' := by
    intro y hy
    have := hW'b.smul_mem (show ‖(-1 : 𝕜)‖ ≤ 1 by simp) hy
    simpa using this
  set A := {x : X | ∀ T ∈ E, T x ∈ W'} with hA
  suffices hAn : A ∈ 𝓝 (0 : X) by
    refine ⟨A, hAn, ?_⟩
    rintro _ ⟨T, hT, rfl⟩ x hx
    exact hWU (balancedCore_subset W (hx T hT))
  rcases hX with hF | hL
  · have : TopologicalSpace.MetrizableSpace X := hF.2.1
    have : CompleteSpace X := hF.2.2
    have : (𝓤 X).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
    apply core E _ W' hW'0 hW'c hW'cv hW's
    have : {x : X | Bornology.IsVonNBounded 𝕜 ((fun T : X →L[𝕜] Y => T x) '' E)} = univ :=
      eq_univ_of_forall hE
    rw [this]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
  · obtain ⟨F, hFc, hFn⟩ := hL
    apply hFc.mem_nhds_of_absConvex A
    · intro a ha
      rintro _ ⟨x, hx, rfl⟩ T hT
      rw [T.map_smul]
      exact hW'b.smul_mem ha (hx T hT)
    · intro x hx y hy a b ha hb hab T hT
      rw [map_add, T.map_smul_of_tower, T.map_smul_of_tower]
      exact hW'cv (hx T hT) (hy T hT) ha hb hab
    · intro n
      have : TopologicalSpace.MetrizableSpace (F n) := (hFn n).1
      have : CompleteSpace (F n) := (hFn n).2.completeSpace_coe
      have : IsUniformAddGroup (F n) := (F n).toAddSubgroup.isUniformAddGroup
      have : (𝓤 (F n)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
      set En : Set (F n →L[𝕜] Y) := (fun T : X →L[𝕜] Y => T.comp (F n).subtypeL) '' E with hEn
      have hc := core En ?_ W' hW'0 hW'c hW'cv hW's
      · convert hc using 1
        ext z
        simp only [mem_setOf_eq, hEn, mem_image, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, hA]
        rfl
      · have : {x : F n | Bornology.IsVonNBounded 𝕜
            ((fun T : F n →L[𝕜] Y => T x) '' En)} = univ := by
          refine eq_univ_of_forall fun z => ?_
          have h := hE (z : X)
          show Bornology.IsVonNBounded 𝕜 ((fun T : F n →L[𝕜] Y => T z) '' En)
          have himg : (fun T : F n →L[𝕜] Y => T z) '' En = (fun T : X →L[𝕜] Y => T z) '' E := by
            ext y; simp [hEn]
          rw [himg]; exact h
        rw [this]
        exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
