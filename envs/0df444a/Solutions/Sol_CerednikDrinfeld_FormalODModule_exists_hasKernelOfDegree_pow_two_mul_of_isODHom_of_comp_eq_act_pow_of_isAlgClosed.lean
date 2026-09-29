-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_hasKernelOfDegree_pow_two_mul_of_isODHom_of_comp_eq_act_pow_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/42bd5957-e47c-5be2-a12a-3aa7c52975ae

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasHeight_hasKernelOfDegree_act_pow
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_of_X_pow_mem_span_of_field
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_X_pow_mem_span_comp
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_even_of_isIsogenyOfHeight_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_pow_two_mul_of_isODHom_of_comp_eq_act_pow_of_isAlgClosed
p2m_attr_erase "instance" "CerednikDrinfeld.BruhatTits.instGraphActionGLTree CerednikDrinfeld.BruhatTits.instMulActionGLVertex CerednikDrinfeld.BruhatTits.instGraphActionPGLTree CerednikDrinfeld.BruhatTits.instMulActionPGLVertex CerednikDrinfeld.Mumford.dartAction instTopologicallyFGOfFiniteType MvFormalGroup.CartierModule.instAddCommGroup MvFormalGroup.CartierModule.instNeg MvFormalGroup.CartierModule.instAdd MvFormalGroup.CartierModule.instZero MvFormalGroup.WittLaw.instTendstoCofiniteProdMk MvFormalGroup.CartierModule.instModuleWittVector"
p2m_attr_erase "simp" "CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply CerednikDrinfeld.BruhatTits.vertPermHom_apply CerednikDrinfeld.BruhatTits.gl_smul_mk CerednikDrinfeld.BruhatTits.pgl_mk_smul CerednikDrinfeld.HeckeData.mk.sizeOf_spec CerednikDrinfeld.Matching.mk.injEq CerednikDrinfeld.DegeneracyData.mk.sizeOf_spec CerednikDrinfeld.DegeneracyData.mk.injEq CerednikDrinfeld.ribbonGram_apply CerednikDrinfeld.HeckeData.mk.injEq CerednikDrinfeld.Matching.mk.sizeOf_spec ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply"
p2m_attr_erase "simp" "MvFormalGroup.CartierModule.toPowerSeries_sub MvFormalGroup.WittLaw.verFam_zero MvFormalGroup.WittLaw.verFam_succ MvFormalGroup.CartierModule.toPowerSeries_frobenius MvFormalGroup.CartierModule.toPowerSeries_verschiebung MvFormalGroup.WittLaw.blk_apply MvFormalGroup.WittLaw.weight_apply MvFormalGroup.CartierModule.toPowerSeries_map MvFormalGroup.CartierModule.toPowerSeries_precompFun MvFormalGroup.CartierModule.toPowerSeries_mapFun MvFormalGroup.CartierModule.mk.injEq MvFormalGroup.WittLaw.pairFam_apply MvFormalGroup.CartierModule.endAct_apply MvFormalGroup.WittLaw.frobFam_apply MvFormalGroup.CartierModule.toPowerSeries_zero MvFormalGroup.CartierModule.tangent_apply MvFormalGroup.CartierModule.toPowerSeries_precomp MvFormalGroup.CartierModule.Examples.toPowerSeries_addLinear MvFormalGroup.CartierModule.toPowerSeries_add MvFormalGroup.CartierModule.toPowerSeries_neg MvFormalGroup.CartierModule.mk.sizeOf_spec MvFormalGroup.CartierModule.inBlk_apply MvFormalGroup.WittLaw.teichFam_apply MvFormalGroup.CartierModule.toPowerSeries_homothety MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace DegFieldAux

variable {σ R : Type*} [CommRing R]

theorem exists_eq_sum_X_mul [DecidableEq σ] (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ d : σ →₀ ℕ, (∀ s ∈ T, d s = 0) → coeff d f = 0) →
      ∃ q : σ → MvPowerSeries σ R, f = ∑ s ∈ T, X s * q s := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    refine ⟨fun _ => 0, ?_⟩
    rw [Finset.sum_empty]
    ext d
    rw [map_zero]
    exact hf d (fun s hs => absurd hs (Finset.notMem_empty s))
  | @insert s T hs ih =>
    intro f hf
    let f₀ : MvPowerSeries σ R := fun d => if d s = 0 then coeff d f else 0
    have hf₀ : ∀ d, coeff d f₀ = if d s = 0 then coeff d f else 0 := fun d => rfl
    have hdvd : (X s : MvPowerSeries σ R) ∣ f - f₀ := by
      rw [X_dvd_iff]
      intro d hd
      rw [map_sub, hf₀, if_pos hd, sub_self]
    obtain ⟨q', hq'⟩ := hdvd
    obtain ⟨q, hq⟩ := ih f₀ (by
      intro d hd
      rw [hf₀]
      split_ifs with hds
      · exact hf d (fun t ht => by
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hds
          · exact hd t ht)
      · rfl)
    refine ⟨Function.update q s q', ?_⟩
    rw [Finset.sum_insert hs, Function.update_self]
    have hrest : ∑ t ∈ T, X t * Function.update q s q' t = ∑ t ∈ T, X t * q t := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Function.update_of_ne (ne_of_mem_of_not_mem ht hs)]
    rw [hrest, ← hq, ← hq']
    ring

theorem exists_eq_sum_X_mul_of_constantCoeff [Fintype σ] (f : MvPowerSeries σ R)
    (hf : constantCoeff f = 0) : ∃ q : σ → MvPowerSeries σ R, f = ∑ s, X s * q s := by
  classical
  obtain ⟨q, hq⟩ := exists_eq_sum_X_mul (Finset.univ : Finset σ) f (fun d hd => by
    have hd0 : d = 0 := Finsupp.ext fun s => hd s (Finset.mem_univ s)
    rw [hd0, coeff_zero_eq_constantCoeff_apply, hf])
  exact ⟨q, hq⟩

theorem subst_mem_span [Fintype σ] {τ : Type*} {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) :
    subst a f ∈ Ideal.span (Set.range a) := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha
  obtain ⟨q, hq⟩ := exists_eq_sum_X_mul_of_constantCoeff f hf
  rw [hq, ← coe_substAlgHom hsa, map_sum]
  refine Ideal.sum_mem _ fun s _ => ?_
  rw [map_mul, coe_substAlgHom hsa, subst_X hsa]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s, rfl⟩)

end DegFieldAux

theorem solution
    (r : ℕ) [Fact r.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k r]
    (j : Zp2 r →+* k)
    (Y Y' : FormalODModule r k) (hY : Y.IsSpecial j) (hY4 : Y.HasHeight 4)
    (hY' : Y'.IsSpecial j) (hY'4 : Y'.HasHeight 4)
    (σ τ : Series k) (hσ : FormalODModule.IsODHom Y Y' σ)
    (hτ0 : ∀ i, MvPowerSeries.constantCoeff (τ i) = 0)
    (d : ℕ) (hτσ : τ.comp σ = Y.act ((r : Zp2 r) ^ d)) :
    ∃ m : ℕ, FormalODModule.HasKernelOfDegree σ (r ^ (2 * m)) := by
  classical
  have hr : r.Prime := Fact.out
  have hσ0 : ∀ i, constantCoeff (σ i) = 0 := hσ.constantCoeff
  have hA0 : ∀ i, constantCoeff (Y.act ((r : Zp2 r) ^ d) i) = 0 := (Y.isLawHom_act _).1

  have hPdeg : FormalODModule.HasKernelOfDegree (Y.act ((r : Zp2 r) ^ d)) (r ^ (4 * d)) :=
    FormalODModule.HasHeight.hasKernelOfDegree_act_pow hY4 d

  obtain ⟨N, hN⟩ := FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree (Y.act ((r : Zp2 r) ^ d)) hA0 hPdeg
  have hle : Ideal.span (Set.range (Y.act ((r : Zp2 r) ^ d))) ≤ Ideal.span (Set.range σ) := by
    rw [← hτσ]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact DegFieldAux.subst_mem_span hσ0 (hτ0 i)
  have hNσ : ∃ N : ℕ, ∀ i : Fin 2, (X i : MvPowerSeries (Fin 2) k) ^ N ∈ Ideal.span (Set.range σ) :=
    ⟨N, fun i => hle (hN i)⟩

  obtain ⟨d₀, hd₀⟩ := FormalODModule.exists_hasKernelOfDegree_of_X_pow_mem_span_of_field σ hσ0 hNσ
  have hNτ : ∃ N : ℕ, ∀ i : Fin 2, (X i : MvPowerSeries (Fin 2) k) ^ N ∈ Ideal.span (Set.range τ) :=
    FormalODModule.exists_X_pow_mem_span_of_X_pow_mem_span_comp hσ0 hτ0 hd₀ ⟨N, by rw [hτσ]; exact hN⟩
  obtain ⟨d₁, hd₁⟩ := FormalODModule.exists_hasKernelOfDegree_of_X_pow_mem_span_of_field τ hτ0 hNτ
  have hcomp := FormalODModule.HasKernelOfDegree.comp hσ0 hτ0 hd₀ hd₁
  rw [hτσ] at hcomp
  have hdeg : d₀ * d₁ = r ^ (4 * d) := by
    have h1 := hcomp.2.2 k (RingHom.id k)
    have h2 := hPdeg.2.2 k (RingHom.id k)
    rw [h1] at h2
    exact h2
  have hdvd : d₀ ∣ r ^ (4 * d) := ⟨d₁, hdeg.symm⟩
  obtain ⟨h, -, rfl⟩ := (Nat.dvd_prime_pow hr).1 hdvd

  let Φb : SpecialFormalODModule r j := ⟨Y, hY, hY4⟩
  let Φb' : SpecialFormalODModule r j := ⟨Y', hY', hY'4⟩
  have heven : Even h :=
    SpecialFormalODModule.even_of_isIsogenyOfHeight_of_isAlgClosed r k j Φb Φb' σ h ⟨hσ, hd₀⟩
  obtain ⟨m, hm⟩ := heven
  refine ⟨m, ?_⟩
  rw [two_mul, ← hm]
  exact hd₀

end S_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_pow_two_mul_of_isODHom_of_comp_eq_act_pow_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_pow_two_mul_of_isODHom_of_comp_eq_act_pow_of_isAlgClosed (solution)
