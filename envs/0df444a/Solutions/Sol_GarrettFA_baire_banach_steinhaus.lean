-- Prove2me | solution 1 for GarrettFA.baire_banach_steinhaus
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:14:45.61221+00:00
-- url     : https://prove2.me/submissions/6fa9ccf6-2526-4095-97c4-6b53da4bb37b

import Mathlib
import Definitions.Def_GarrettFA_IsEquicontinuousSet

open Topology Set Filter Pointwise

namespace GABBS

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

end GABBS

open GABBS in
theorem solution {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V]
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [Module ℝ Y] [IsScalarTower ℝ 𝕜 Y]
    [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul 𝕜 Y] [LocallyConvexSpace ℝ Y]
    [T2Space Y]
    (E : Set (V →L[𝕜] Y))
    (hE : ¬ IsMeagre {x : V | Bornology.IsVonNBounded 𝕜 ((fun T : V →L[𝕜] Y => T x) '' E)}) :
    {x : V | Bornology.IsVonNBounded 𝕜 ((fun T : V →L[𝕜] Y => T x) '' E)} = Set.univ ∧
      GarrettFA.IsEquicontinuousSet ((fun T : V →L[𝕜] Y => (T : V → Y)) '' E) := by
  set B := {x : V | Bornology.IsVonNBounded 𝕜 ((fun T : V →L[𝕜] Y => T x) '' E)} with hB
  -- key: for every nbhd U of 0 in Y, the set A = {x | ∀ T ∈ E, T x ∈ W} is a nbhd of 0
  have key : ∀ U ∈ 𝓝 (0 : Y), ∃ N ∈ 𝓝 (0 : V), ∀ T ∈ E, ∀ x ∈ N, T x ∈ U := by
    intro U hU
    obtain ⟨W, hW0, hWc, hWcv, hWs, hWU⟩ := good_nhd (𝕜 := 𝕜) U hU
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
      rw [(hAc.smul₀ (((n + 1 : ℕ) : 𝕜))).isNowhereDense_iff]
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
    exact ⟨A, hAnhd, fun T hT x hx => hWU (hx T hT)⟩
  have hequi : GarrettFA.IsEquicontinuousSet ((fun T : V →L[𝕜] Y => (T : V → Y)) '' E) := by
    intro U hU
    obtain ⟨N, hN, hNU⟩ := key U hU
    refine ⟨N, hN, ?_⟩
    rintro _ ⟨T, hT, rfl⟩ x hx
    exact hNU T hT x hx
  refine ⟨?_, hequi⟩
  ext x
  simp only [mem_univ, iff_true]
  intro U hU
  obtain ⟨N, hN, hNU⟩ := key U hU
  have habs : Absorbs 𝕜 N {x} := absorbent_nhds_zero hN x
  refine Filter.Eventually.mono habs ?_
  intro a ha
  rintro _ ⟨T, hT, rfl⟩
  obtain ⟨n, hn, hnx⟩ := ha (mem_singleton x)
  have e : T x = a • T n := by rw [← hnx]; exact T.map_smul a n
  show T x ∈ a • U
  rw [e]
  exact smul_mem_smul_set (hNU T hT n hn)
