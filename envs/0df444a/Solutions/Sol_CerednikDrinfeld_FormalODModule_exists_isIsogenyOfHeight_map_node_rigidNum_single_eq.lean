-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_isIsogenyOfHeight_map_node_rigidNum_single_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c196d845-9d0a-5b14-904f-ecb1c395a95c

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isIsogenyOfHeight_four_mul_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isODHom_and_isGradedSbar_and_isGradedPhiS_map_node
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_rigidNum_eq_sum_smul_of_isIsogenyOfHeight_map_node
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_det_eq_mul_pow_of_rigidNum_eq_sum_smul_map_node
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_matrix_smul_eq_map_and_nsmul_apply_rigidification_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_centralizer_mul_map_eq_pow_smul_one_and_hasKernelOfDegree_of_det_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isIsogenyOfHeight_comp_and_rigidNum_comp_eq_rigidNum_mulVec_of_centralizer
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_WittVector_nonempty_ringEquiv_quotient_pIdeal_of_perfectRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isIsogenyOfHeight_map_node_rigidNum_single_eq
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup CerednikDrinfeld.LubinTate.instIsCommMap CerednikDrinfeld.LubinTate.instFintypeGaloisFieldTwo CerednikDrinfeld.LubinTate.sigma_isComm CerednikDrinfeld.LubinTate.sigmaBar_isComm CerednikDrinfeld.BoxBasisLemma.instDecidableInBox CerednikDrinfeld.Standard.law_isComm MvFormalGroup.CartierModule.instModulePadicInt"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec CerednikDrinfeld.Standard.emb_inr CerednikDrinfeld.BoxBasisLemma.toFinsupp_apply CerednikDrinfeld.Standard.chi_zero CerednikDrinfeld.Standard.emb_inl CerednikDrinfeld.Standard.chi_one MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

namespace NodeNormAsm

theorem isMaximal_pIdeal (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k] :
    (pIdeal p (WittVector p k)).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (WittVector.irreducible p)

theorem charP_quot (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] :
    CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p :=
  CharP.quotient (WittVector p k) p (mem_nonunits_iff.2 (WittVector.irreducible p).not_isUnit)

theorem isAlgClosed_of_ringEquiv {F F' : Type} [Field F] [Field F'] [IsAlgClosed F] (e : F ≃+* F') :
    IsAlgClosed F' := by
  refine IsAlgClosed.of_exists_root F' fun q _ hqi => ?_
  set q' : Polynomial F := q.map e.symm.toRingHom with hq'def
  have hq' : q'.degree ≠ 0 := by
    rw [hq'def, Polynomial.degree_map_eq_of_injective e.symm.injective]
    exact (Polynomial.degree_pos_of_irreducible hqi).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q' hq'
  refine ⟨e x, ?_⟩
  have hqq : q = q'.map e.toRingHom := by
    rw [hq'def, Polynomial.map_map, RingEquiv.toRingHom_comp_symm_toRingHom, Polynomial.map_id]
  rw [hqq, Polynomial.eval_map]
  show Polynomial.eval₂ e.toRingHom (e.toRingHom x) q' = 0
  rw [Polynomial.eval₂_at_apply, hx.eq_zero, map_zero]

theorem mul_eq_smul_one_comm {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n K) (lam : K) (hlam : lam ≠ 0) (h : B * A = lam • 1) : A * B = lam • 1 := by
  have h1 : (lam⁻¹ • B) * A = 1 := by rw [Matrix.smul_mul, h, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  have h2 : A * (lam⁻¹ • B) = 1 := mul_eq_one_comm.1 h1
  have h3 : A * B = lam • (A * (lam⁻¹ • B)) := by
    rw [Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hlam, one_smul]
  rw [h3, h2]

end NodeNormAsm

set_option maxHeartbeats 6400000 in
open NodeNormAsm in

theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
(g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
(hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
(X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (γ : Fin 2 → CartierModule p X.F)
(hγ : X.IsHomogeneousVBasis (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) γ)
(hγa : X.HasStructureConstants γ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k))))
(hXs : X.IsSpecial (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) (hX4 : X.HasHeight 4)

(f₀ : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) →+* (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hf₀ : f₀.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) = RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hf₀ξ : f₀ (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0) (hf₀η : f₀ (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0)
    :
    ∃ (m : ℕ) (ρ₀ : Series (WittVector p k ⧸ pIdeal p (WittVector p k))),
      FormalODModule.IsIsogenyOfHeight Φ (X.map f₀) ρ₀ (4 * m) ∧
      ∃ (hOD₀ : FormalODModule.IsODHom (Rigidified.Φbar (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.Xbar (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.ρ (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))))
        (hcb : Rigidified.IsGradedSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
        (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
        (a : ℕ),
        ∀ i : Fin 2,
          p ^ a • (Rigidified.rigidNum ι hcΦ rΦ (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀ (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))) hcb hcΦg) (Pi.single i 1) =
            p ^ (a + m) • (![((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))), 0),
                ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nVarpi (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))), 0))] i) := by
  classical

  haveI hmax : (pIdeal p (WittVector p k)).IsMaximal := isMaximal_pIdeal p k
  letI instF : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := Ideal.Quotient.field _
  haveI hchar : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p := charP_quot p k
  obtain ⟨eK⟩ := WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k
  haveI hac : IsAlgClosed (WittVector p k ⧸ pIdeal p (WittVector p k)) := isAlgClosed_of_ringEquiv eK

  have hf₀' : ∀ y : (WittVector p k ⧸ pIdeal p (WittVector p k)), f₀ (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) y) = y := fun y => RingHom.congr_fun hf₀ y
  have hcompj : f₀.comp (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) = (Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι :=
    RingHom.ext fun x => by simp [RingHom.comp_apply, hf₀']
  have hX0s : (X.map f₀).IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) := by
    have h := CerednikDrinfeld.FormalODModule.IsSpecial.map _ f₀ X hXs
    rwa [hcompj] at h
  haveI hNq : IsNoetherianRing (FormalOmega.edgeQuot (WittVector p k ⧸ pIdeal p (WittVector p k)) (0 : (WittVector p k ⧸ pIdeal p (WittVector p k)))) := by
    unfold FormalOmega.edgeQuot; infer_instance
  haveI : IsNoetherianRing (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (FormalOmega.edgeQuot.discr (WittVector p k ⧸ pIdeal p (WittVector p k)) (0 : (WittVector p k ⧸ pIdeal p (WittVector p k))) p)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) hNq
  have hX04 : (X.map f₀).HasHeight 4 := by
    unfold FormalODModule.HasHeight
    rw [FormalODModule.map_act]
    exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f₀ _ (fun i => (X.isLawHom_act _).1 i) hX4

  obtain ⟨ρ, m₁, hρ⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_isIsogenyOfHeight_four_mul_of_isAlgClosed p (WittVector p k ⧸ pIdeal p (WittVector p k))
      ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ⟨Φ, hΦ, hΦ4⟩ ⟨X.map f₀, hX0s, hX04⟩

  obtain ⟨hOD₀, hcb, hcΦg⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.isODHom_and_isGradedSbar_and_isGradedPhiS_map_node
      p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg X γ hγ hγa hXs hX4 f₀ hf₀ hf₀ξ hf₀η m₁ ρ hρ

  have hp0 : (p : (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0 := (CharP.cast_eq_zero_iff (WittVector p k ⧸ pIdeal p (WittVector p k)) p p).2 dvd_rfl
  haveI hchar1 : CharP ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))) p :=
    CharP.quotient' p (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))) (fun x hx => by
      have hbot : pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)) = ⊥ := by rw [pIdeal, Ideal.span_singleton_eq_bot]; exact hp0
      rw [hbot, Ideal.mem_bot] at hx
      exact hx)
  obtain ⟨c, -⟩ : ∃ c : ℤ_[p] →+* WittVector p ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))), True :=
    ⟨(WittVector.map (ZMod.castHom (dvd_refl p) ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (WittVector.equiv p).symm.toRingHom, trivial⟩

  obtain ⟨a₀, A, hA⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_rigidNum_eq_sum_smul_of_isIsogenyOfHeight_map_node
      p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg X γ hγ hγa hXs hX4 f₀ hf₀ hf₀ξ hf₀η m₁ ρ hρ hOD₀ hcb hcΦg c
  obtain ⟨u, hdet⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_det_eq_mul_pow_of_rigidNum_eq_sum_smul_map_node
      p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg X γ hγ hγa hXs hX4 f₀ hf₀ hf₀ξ hf₀η m₁ ρ hρ hOD₀ hcb hcΦg c a₀ A hA

  obtain ⟨E, hNe, hE⟩ :=
    CerednikDrinfeld.FormalODModule.exists_ringHom_centralizer_matrix_smul_eq_map_and_nsmul_apply_rigidification_eq
      p k ι Φ hΦ hΦ4 hcΦ rΦ hrΦ
  obtain ⟨e, c₁, hEA, hed, he⟩ :=
    CerednikDrinfeld.FormalODModule.exists_centralizer_mul_map_eq_pow_smul_one_and_hasKernelOfDegree_of_det_eq
      p k ι Φ hΦ hΦ4 hcΦ rΦ hrΦ E hNe hE A (2 * m₁) u hdet
  obtain ⟨Ae, hAe, -⟩ := hE e

  obtain ⟨hiso, hOD₁, hcb₁, hcomp⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.isIsogenyOfHeight_comp_and_rigidNum_comp_eq_rigidNum_mulVec_of_centralizer
      p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg X γ hγ hγa hXs hX4 f₀ hf₀ hf₀ξ hf₀η m₁ ρ hρ hOD₀ hcb hcΦg
      E hNe hE e he (4 * c₁ + 2 * (2 * m₁)) hed Ae hAe (2 * m₁ + c₁)

  have hlam : ((p : ℚ_[p]) ^ (c₁ + 2 * m₁)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hAE : A.map ((↑) : ℤ_[p] → ℚ_[p]) * E e = ((p : ℚ_[p]) ^ (c₁ + 2 * m₁)) • 1 :=
    mul_eq_smul_one_comm _ _ _ hlam hEA
  have hAAe : A * Ae = ((p : ℤ_[p]) ^ (c₁ + 2 * m₁ + 1)) • 1 := by
    have hinj : Function.Injective (fun M : Matrix (Fin 2) (Fin 2) ℤ_[p] => M.map ((↑) : ℤ_[p] → ℚ_[p])) :=
      fun M M' h => Matrix.ext fun i j => PadicInt.ext (by simpa using congrFun (congrFun h i) j)
    apply hinj
    have hmm : (A * Ae).map ((↑) : ℤ_[p] → ℚ_[p]) = A.map ((↑) : ℤ_[p] → ℚ_[p]) * Ae.map ((↑) : ℤ_[p] → ℚ_[p]) :=
      Matrix.map_mul (f := PadicInt.Coe.ringHom (p := p))
    show (A * Ae).map ((↑) : ℤ_[p] → ℚ_[p]) = (((p : ℤ_[p]) ^ (c₁ + 2 * m₁ + 1)) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[p])).map ((↑) : ℤ_[p] → ℚ_[p])
    rw [hmm, ← hAe, Matrix.mul_smul, hAE, smul_smul]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> push_cast <;> ring

  refine ⟨2 * m₁ + c₁, ρ.comp (e : MvFormalGroup.End Φ.F).toPowerSeries, ?_, hOD₁, hcb₁, hcΦg, a₀ + 1, ?_⟩
  · have h4 : 4 * m₁ + (4 * c₁ + 2 * (2 * m₁)) = 4 * (2 * m₁ + c₁) := by ring
    rw [← h4]
    exact hiso
  · intro i
    have hvec : A.mulVec (Ae.mulVec (Pi.single i 1)) = (p : ℤ_[p]) ^ (c₁ + 2 * m₁ + 1) • Pi.single i 1 := by
      rw [Matrix.mulVec_mulVec, hAAe, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [pow_succ, mul_smul, hcomp, hA, hvec, Fintype.sum_eq_single i (fun j hj => by
      rw [Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero, map_zero, zero_smul])]
    rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, map_pow, map_natCast, ← Nat.cast_pow,
      Nat.cast_smul_eq_nsmul, ← mul_smul, ← pow_add]
    congr 1
    ring

end S_CerednikDrinfeld_FormalODModule_exists_isIsogenyOfHeight_map_node_rigidNum_single_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_isIsogenyOfHeight_map_node_rigidNum_single_eq (solution)
