-- Prove2me | solution 1 for Formalism.E.hermDual_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:25.482943+00:00
-- url     : https://prove2.me/submissions/8af5cb8b-0452-463f-b432-5f136030ee01

import Definitions.Def_Formalism_FockGram_StatementHerm
import Definitions.Def_Formalism_FockGram_FockGramProofs_HermDualOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix LinearMap Module
noncomputable section
namespace Formalism.E
private theorem mem_hdual_span_iff_forall_pairing_mem_range {S K V ι : Type} [CommRing S] [Field K] [StarRing K]
    [Algebra S K] [AddCommGroup V] [Module K V] [Module S V] [IsScalarTower S K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K) (b : ι → V)
    (hstar : ∀ s : S, star (algebraMap S K s) ∈ Set.range (algebraMap S K)) (x : V) :
    x ∈ hdual B (Submodule.span S (Set.range b)) ↔
      ∀ i, B (b i) x ∈ Set.range (algebraMap S K) := by
  simp only [hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    Submodule.mem_one, Set.mem_range]
  constructor
  · intro h i
    exact h _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact h i
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨p, hp⟩ := hy
      obtain ⟨q, hq⟩ := hz
      exact ⟨p + q, by rw [map_add, hp, hq, map_add, LinearMap.add_apply]⟩
    | smul s y _ hy =>
      obtain ⟨p, hp⟩ := hy
      obtain ⟨t, ht⟩ := hstar s
      refine ⟨t * p, ?_⟩
      rw [map_mul, ht, hp, ← algebraMap_smul K s y, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, starRingEnd_apply]
private theorem eq_zero_of_gram_det_ne_zero_of_pairing_basis_eq_zero {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (B : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis ι K V)
    (hG : (Matrix.of fun i j => B (b i) (b j)).det ≠ 0) (z : V) (hz : ∀ i, B (b i) z = 0) :
    z = 0 := by
  have hc : (Matrix.of fun i j => B (b i) (b j)) *ᵥ (fun j => b.repr z j) = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← hz i]
    conv_rhs => rw [← b.sum_repr z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hv := Matrix.eq_zero_of_mulVec_eq_zero hG hc
  exact b.forall_coord_eq_zero_iff.1 fun i => by simpa [Basis.coord_apply] using congrFun hv i
private theorem isUnit_algebraNorm_int_iff_isUnit {S : Type} [CommRing S] [Module.Free ℤ S]
    [Module.Finite ℤ S] (x : S) : IsUnit (Algebra.norm ℤ x) ↔ IsUnit x := by
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det]
  constructor
  · intro hu
    obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).1 hu).2 1
    exact isUnit_iff_exists_inv.2 ⟨y, by simpa using hy⟩
  · intro hu
    exact hu.map (Algebra.lmul ℤ S)
end Formalism.E
end
end

set_option autoImplicit false
open Matrix LinearMap Module
noncomputable section
open Formalism Formalism.E
namespace Formalism.E
theorem _root_.solution (h : SubIndexNorm) : HermDual := by
  intro S K V ι _ _ _ _ _ _ _ _ _ _ B b hinj hstar
  have hL := mem_hdual_span_iff_forall_pairing_mem_range B b hstar
  have part1 : Submodule.span S (Set.range b) ≤ hdual B (Submodule.span S (Set.range b)) ↔
      ∀ i j, B (b i) (b j) ∈ Set.range (algebraMap S K) := by
    constructor
    · intro hle i j
      exact (hL _).1 (hle (Submodule.subset_span ⟨j, rfl⟩)) i
    · intro hG
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact (hL _).2 fun i => hG i j
  refine ⟨part1, ?_⟩
  intro _ _ GS hGS hdet
  have hLle := part1.2 fun i j => ⟨GS i j, (hGS i j).symm⟩
  obtain ⟨L, hLdef⟩ : ∃ L : Submodule S V, L = Submodule.span S (Set.range b) := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : Submodule S V, M = hdual B L := ⟨_, rfl⟩
  rw [← hLdef] at hLle ⊢
  rw [← hMdef] at hLle ⊢
  have hmemM : ∀ x, x ∈ M ↔ ∀ i, B (b i) x ∈ Set.range (algebraMap S K) := by
    rw [hMdef, hLdef]
    exact hL
  obtain ⟨G, hG⟩ : ∃ G : Matrix ι ι K, G = Matrix.of fun i j => B (b i) (b j) := ⟨_, rfl⟩
  have hGij : ∀ i j, G i j = B (b i) (b j) := fun i j => by rw [hG]; rfl
  have hGdet : G.det = algebraMap S K GS.det := by
    have e : G = (algebraMap S K).mapMatrix GS := by
      ext i j
      rw [hGij, hGS]
      rfl
    rw [e, RingHom.map_det]
  have hGdet0 : G.det ≠ 0 := by
    rw [hGdet]
    exact fun h0 => hdet (hinj (by rw [h0, map_zero]))
  have hnd := eq_zero_of_gram_det_ne_zero_of_pairing_basis_eq_zero B b (hG ▸ hGdet0)
  obtain ⟨d, hd⟩ : ∃ d : ι → V, ∀ k, d k = ∑ j, G⁻¹ j k • b j := ⟨_, fun k => rfl⟩
  have hBd : ∀ i k, B (b i) (d k) = if i = k then 1 else 0 := by
    intro i k
    have e := congrFun (congrFun (Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.2 hGdet0)) i) k
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    rw [← e, hd, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, hGij, mul_comm]
  have hdM : ∀ k, d k ∈ M := fun k => (hmemM _).2 fun i =>
    ⟨if i = k then 1 else 0, by rw [hBd]; split_ifs <;> simp⟩
  obtain ⟨dM, hdM'⟩ : ∃ dM : ι → M, ∀ k, (dM k : V) = d k :=
    ⟨fun k => ⟨d k, hdM k⟩, fun k => rfl⟩
  have hBsum : ∀ (g : ι → S) i, B (b i) (∑ k, g k • d k) = algebraMap S K (g i) := by
    intro g i
    rw [map_sum]
    simp_rw [LinearMap.map_smul_of_tower, hBd]
    simp [Algebra.smul_def]
  have hliD : LinearIndependent S dM := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg' : ∑ k, g k • d k = 0 := by
      have e := congrArg Subtype.val hg
      rw [Submodule.coe_sum] at e
      simpa [Submodule.coe_smul, hdM'] using e
    have e := hBsum g i
    rw [hg', map_zero] at e
    exact hinj (by rw [← e, map_zero])
  have hspD : ⊤ ≤ Submodule.span S (Set.range dM) := by
    rintro ⟨x, hx⟩ -
    choose s hs using (hmemM x).1 hx
    have hxe : x = ∑ k, s k • d k := by
      refine sub_eq_zero.1 (hnd _ fun i => ?_)
      rw [map_sub, hBsum, hs, sub_self]
    have e : (⟨x, hx⟩ : M) = ∑ k, s k • dM k := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul, hdM']
      exact hxe
    rw [e]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  obtain ⟨bD, hbD⟩ : ∃ bD : Basis ι S M, ∀ k, bD k = dM k :=
    ⟨Basis.mk hliD hspD, fun k => Basis.mk_apply _ _ _⟩
  have hbM : ∀ j, b j ∈ M := fun j => (hmemM _).2 fun i => ⟨GS i j, (hGS i j).symm⟩
  obtain ⟨bM, hbM'⟩ : ∃ bM : ι → M, ∀ j, (bM j : V) = b j :=
    ⟨fun j => ⟨b j, hbM j⟩, fun j => rfl⟩
  have hliB : LinearIndependent S bM := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hg' : ∑ k, algebraMap S K (g k) • b k = 0 := by
      have e := congrArg Subtype.val hg
      rw [Submodule.coe_sum] at e
      simpa [Submodule.coe_smul, hbM', algebraMap_smul] using e
    have e := Fintype.linearIndependent_iff.1 b.linearIndependent _ hg' j
    exact hinj (by rw [e, map_zero])
  obtain ⟨bN, hbN⟩ : ∃ bN : Basis ι S (Submodule.span S (Set.range bM)), ∀ j, (bN j : M) = bM j :=
    ⟨Basis.span hliB, fun j => congrArg Subtype.val (Basis.span_apply hliB j)⟩
  have key := h S M ι bD (Submodule.span S (Set.range bM)) bN
  have hbexp : ∀ j, bM j = ∑ k, GS k j • bD k := by
    intro j
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, hbD, hdM', hbM']
    refine (sub_eq_zero.1 (hnd _ fun i => ?_))
    rw [map_sub, hGS, show B (b i) (∑ k, GS k j • d k) = algebraMap S K (GS i j) from
      hBsum (fun k => GS k j) i, sub_self]
  have hdetS : bD.det (fun i => (bN i : M)) = GS.det := by
    rw [Basis.det_apply]
    congr 1
    ext i j
    rw [Basis.toMatrix_apply, hbN, hbexp, bD.repr_sum_self]
  have hspanN : ∀ x : M, x ∈ Submodule.span S (Set.range bM) ↔ (x : V) ∈ L := by
    intro x
    have e : Submodule.map M.subtype (Submodule.span S (Set.range bM)) = L := by
      rw [Submodule.map_span, ← Set.range_comp, hLdef]
      congr 2
      funext j
      exact hbM' j
    rw [← e, Submodule.mem_map]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
  have hidx : L.toAddSubgroup.relIndex M.toAddSubgroup = (Algebra.norm ℤ GS.det).natAbs := by
    rw [← hdetS, ← key]
    have hsub : L.toAddSubgroup.addSubgroupOf M.toAddSubgroup =
        (Submodule.span S (Set.range bM)).toAddSubgroup := by
      ext x
      rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup,
        hspanN]
    rw [AddSubgroup.relIndex, hsub]
    rfl
  refine ⟨hidx, ?_⟩
  rw [← isUnit_algebraNorm_int_iff_isUnit, Int.isUnit_iff_natAbs_eq, ← hidx, AddSubgroup.relIndex_eq_one,
    Submodule.toAddSubgroup_le]
  exact ⟨fun e => e.le, fun hle => le_antisymm hle hLle⟩
end Formalism.E
