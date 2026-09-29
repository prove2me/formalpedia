-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_isAlgClosed_of_lieZero_le_ker_wittVector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/a87d75f4-b845-5b25-a2ba-61fcbcb17acb

import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_nsmul_rigidNum_mem_eta
import Theorems.Thm_CerednikDrinfeld_FormalODModule_nMap_bijOn_eta_of_eq_baseChangeEq_mk
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_isCompl_nPiece_zero_one
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_mem_etaPiece_add_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsODHom_map_mem_gradedPiece
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_bijOn_etaPiece_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_eq_zero_of_nsmul_rigidNum_eq_zero_of_isAlgClosed
import Theorems.Thm_PadicInt_exists_forall_apply_eq_pow_smul_imp_exists_eq_smul_of_injective
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_eq_of_isNilpotent
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_isAlgClosed_of_lieZero_le_ker_wittVector
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.Rigidified

namespace W1Aux

variable {p : ℕ} [Fact p.Prime]

theorem isBaseChangeAlong'_of_eq {B S : Type} [CommRing B] [CommRing S] (j : Zp2 p →+* B)
    (g : B →+* S) (X : FormalODModule p B)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (X' : FormalODModule p S) (hX : X.map g = X') (j' : Zp2 p →+* S) (hj : g.comp j = j')
    (hc' : IsCompl (X'.gradedPiece j' 0) (X'.gradedPiece j' 1))
    (hF : X.F.map g = X'.F) :
    IsBaseChangeAlong' g (X.toGradedCartierModuleData j hc) (X'.toGradedCartierModuleData j' hc')
      (CartierModule.baseChangeEq g hF) := by
  subst hX; subst hj
  exact CerednikDrinfeld.FormalODModule.isBaseChangeAlong_toGradedCartierModuleData_baseChange p j g X γ hγ hc hc'

theorem natL_of_eq {B B' : Type} [CommRing B] [CommRing B'] (j : Zp2 p →+* B) (φ : B →+* B')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
    (D : GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (j' : Zp2 p →+* B') (hj : φ.comp j = j')
    (D' : GradedCartierModuleData p B' j') (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : IsBaseChangeAlong' φ D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L)
    (L' : D'.M →+ D'.NMod) (hL' : D'.IsCanonicalLMap L') :
    ∀ x : D.M, L' (f x) = D.nMap D' f hf.2.2.1 hf.2.2.2.1 (L x) := by
  subst hj
  exact CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_isNilpotent p j φ hB hB' D hD D' hD' f hf L hL L' hL'

theorem redBij_of_eq {S : Type} [CommRing S] (hS : IsNilpotent (p : S))
    (j : Zp2 p →+* S) (X : FormalODModule p S)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (Xb : FormalODModule p (S ⧸ pIdeal p S)) (hXb : X.map (Ideal.Quotient.mk (pIdeal p S)) = Xb)
    (jb : Zp2 p →+* S ⧸ pIdeal p S) (hjb : (Ideal.Quotient.mk (pIdeal p S)).comp j = jb)
    (hcb : IsCompl (Xb.gradedPiece jb 0) (Xb.gradedPiece jb 1))
    (hF : X.F.map (Ideal.Quotient.mk (pIdeal p S)) = Xb.F)
    (red : CartierModule p X.F →+ CartierModule p Xb.F)
    (hred : red = CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p S)) hF)
    (hredV : ∀ x, red ((X.toGradedCartierModuleData j hc).verschiebung x) =
      (Xb.toGradedCartierModuleData jb hcb).verschiebung (red x))
    (hredPi : ∀ x, red ((X.toGradedCartierModuleData j hc).varpi x) =
      (Xb.toGradedCartierModuleData jb hcb).varpi (red x))
    (L : _) (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (Lb : _) (hLb : (Xb.toGradedCartierModuleData jb hcb).IsCanonicalLMap Lb)
    (hLL : ∀ x, Lb (red x) = (X.toGradedCartierModuleData j hc).nMap (Xb.toGradedCartierModuleData jb hcb) red hredV hredPi (L x)) :
    Set.BijOn ((X.toGradedCartierModuleData j hc).nMap (Xb.toGradedCartierModuleData jb hcb) red hredV hredPi)
      ((X.toGradedCartierModuleData j hc).eta L hL.isCartierLMap.map_verschiebung : Set _)
      ((Xb.toGradedCartierModuleData jb hcb).eta Lb hLb.isCartierLMap.map_verschiebung : Set _) :=
  CerednikDrinfeld.FormalODModule.nMap_bijOn_eta_of_eq_baseChangeEq_mk p hS j X γ hγ hc Xb hXb jb hjb hcb hF red hred
    hredV hredPi L hL Lb hLb hLL

theorem isHausdorff_of_isNilpotent {S : Type} [CommRing S] (hS : IsNilpotent ((p : ℕ) : S)) :
    IsHausdorff (Ideal.span {((p : ℕ) : S)}) S := by
  obtain ⟨N, hN⟩ := hS
  refine ⟨fun x hx => ?_⟩
  have := hx N
  rwa [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_smul, SModEq.bot] at this

theorem nMap_mem_nPiece {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j') (f : D.M →+ D'.M)
    (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    (hpc : ∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i)
    (m : Fin 2) (n : D.NMod) (hn : n ∈ D.nPiece m) : D.nMap D' f hV hPi n ∈ D'.nPiece m := by
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := AddSubgroup.mem_map.mp hn
  obtain ⟨ha, hb⟩ := AddSubgroup.mem_prod.mp hab
  rw [nMap_nMk]
  exact AddSubgroup.mem_map.mpr ⟨(f a, f b), AddSubgroup.mem_prod.mpr ⟨hpc m a ha, hpc m b hb⟩, rfl⟩

end W1Aux

open W1Aux

theorem W1_core'
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] (ψ : O →+* B)
    (t : Rigidified p Φ B) (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    {S : Type} [CommRing S] [Algebra ℤ_[p] S] (g : B →+* S) (hS : IsNilpotent (p : S))
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (L : _) (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L)
    :
    Set.InjOn (t.etaRed ι ψ g hc hcb)
        (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).eta L hL.isCartierLMap.map_verschiebung : Set _) ∧
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsSpecialCartierModule ∧
      ∀ w : Fin 2 → ℤ_[p],
        ∃ z ∈ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).etaPiece L hL.isCartierLMap.map_verschiebung 0,
          t.etaRed ι ψ g hc hcb z = p • Rigidified.rigidNum ι hcΦ rΦ ψ t hOD g hcb hcΦg w := by
  classical

  have hp0 : IsNilpotent ((p : ℕ) : S ⧸ pIdeal p S) :=
    ⟨1, by rw [pow_one]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))⟩

  have hmk : (Ideal.Quotient.mk (pIdeal p S)).comp g = (reduceMap (p := p) g).comp (Ideal.Quotient.mk (pIdeal p B)) := by
    ext b; rfl
  have hXm : (t.XS g).map (Ideal.Quotient.mk (pIdeal p S)) = t.XbarS g := by
    show (t.X.map g).map (Ideal.Quotient.mk (pIdeal p S)) = (t.X.map (Ideal.Quotient.mk (pIdeal p B))).map (reduceMap (p := p) g)
    rw [FormalODModule.map_map, FormalODModule.map_map, hmk]
  have hjb : (Ideal.Quotient.mk (pIdeal p S)).comp (Rigidified.jS ι ψ g) = Rigidified.jSbar ι ψ g := by
    show (Ideal.Quotient.mk (pIdeal p S)).comp (g.comp (structureMap ι ψ)) = (reduceMap (p := p) g).comp ((Ideal.Quotient.mk (pIdeal p B)).comp (structureMap ι ψ))
    rw [← RingHom.comp_assoc, hmk, RingHom.comp_assoc]
  have hF : (t.XS g).F.map (Ideal.Quotient.mk (pIdeal p S)) = (t.XbarS g).F := t.XS_F_map_mk g

  obtain ⟨Sl, _, jl, φl, _, _, Dl, _, fl, hfl, Ll, _, _⟩ := hL.exists_lift
  obtain ⟨γl, _, hγf⟩ := hfl.2.2.2.2.2
  have hγ : (t.XS g).IsHomogeneousVBasis (Rigidified.jS ι ψ g) (fun i => fl (γl i)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData p _ _ hc _ hγf

  have hbca : IsBaseChangeAlong' (Ideal.Quotient.mk (pIdeal p S)) ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p S)) hF) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc _ hXm _ hjb hcb hF
  have hγb : (t.XbarS g).IsHomogeneousVBasis (Rigidified.jSbar ι ψ g)
      (fun i => CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p S)) hF (fl (γl i))) := by
    refine ⟨fun i => ?_, isUnit_det_tangent_baseChangeEq _ hF _ hγ.2⟩
    exact (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hcb i _).mp
      (hbca.2.2.2.2.1 i _ ((FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hc i _).mpr (hγ.1 i)))
  obtain ⟨Lb, hLb⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
    (Rigidified.jSbar ι ψ g) (isHausdorff_of_isNilpotent hp0) _ _ hγb hcb
  have hD : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsSpecialCartierModule :=
    (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ hc).2
  have hDb : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).IsSpecialCartierModule :=
    (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγb hcb).2

  have hLLb : ∀ x, Lb (CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p S)) hF x) =
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p S)) hF) hbca.2.2.1 hbca.2.2.2.1 (L x) :=
    natL_of_eq _ (Ideal.Quotient.mk (pIdeal p S)) hS hp0 ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) hD _ hjb ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) hDb _ hbca L hL Lb hLb

  have hbij := redBij_of_eq hS (Rigidified.jS ι ψ g) (t.XS g) _ hγ hc (t.XbarS g) hXm (Rigidified.jSbar ι ψ g) hjb hcb hF
    (t.redC g) rfl (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) L hL Lb hLb hLLb
  refine ⟨fun a ha b hb hab => hbij.injOn ha hb hab, hD, fun w => ?_⟩

  obtain ⟨LΦ, hLΦc⟩ := hLΦ
  have hrΦ' : ∀ w', rΦ w' ∈ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).eta LΦ hLΦc.isCartierLMap.map_verschiebung :=
    fun w' => (AddSubgroup.mem_inf.mp ((hrΦ LΦ hLΦc).mapsTo (Set.mem_univ w'))).1
  have hy_eta : p • Rigidified.rigidNum ι hcΦ rΦ ψ t hOD g hcb hcΦg w ∈ ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).eta Lb hLb.isCartierLMap.map_verschiebung :=
    CerednikDrinfeld.SpecialFormal.Rigidified.nsmul_rigidNum_mem_eta ι hcΦ rΦ LΦ hLΦc.isCartierLMap hrΦ' ψ t hOD g hcb hcΦg
      Lb hLb.isCartierLMap w

  have hjj : Rigidified.jPhiS ι ψ g = Rigidified.jSbar ι ψ g := RingHom.ext fun x => rfl
  let fΦ : CartierModule p Φ.F →+ CartierModule p (t.XbarS g).F :=
    (Rigidified.rhoC ψ t hOD.1 g).comp (Rigidified.bcPhi (Φ := Φ) ψ g)
  have hfV : ∀ x, fΦ ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).verschiebung x) = ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).verschiebung (fΦ x) := fun x => by
    show Rigidified.rhoC ψ t hOD.1 g (Rigidified.bcPhi (Φ := Φ) ψ g (verschiebungInt x)) =
      verschiebungInt (Rigidified.rhoC ψ t hOD.1 g (Rigidified.bcPhi (Φ := Φ) ψ g x))
    rw [Rigidified.bcPhi_verschiebungInt, Rigidified.rhoC_verschiebungInt]
  have hfPi : ∀ x, fΦ ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).varpi x) = ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).varpi (fΦ x) := fun x => by
    show Rigidified.rhoC ψ t hOD.1 g (Rigidified.bcPhi (Φ := Φ) ψ g (endAct Φ.varpiEnd x)) =
      endAct (t.XbarS g).varpiEnd (Rigidified.rhoC ψ t hOD.1 g (Rigidified.bcPhi (Φ := Φ) ψ g x))
    rw [Rigidified.bcPhi_endAct_varpiEnd, Rigidified.rhoC_endAct_varpiEnd ψ t hOD g]
  have hfpc : ∀ (i : Fin 2) (x : CartierModule p Φ.F), x ∈ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).piece i →
      fΦ x ∈ ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).piece i := by
    intro i x hx
    have hx' : x ∈ Φ.gradedPiece (Rigidified.jbar ι) i :=
      (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hcΦ i _).mp hx
    have h1 := CerednikDrinfeld.FormalODModule.baseChange_mem_gradedPiece (residueMap ψ) Φ (Rigidified.jbar ι) i hx'
    have h2 := CerednikDrinfeld.FormalODModule.baseChange_mem_gradedPiece (reduceMap (p := p) g) _ _ i h1
    have h3 := CerednikDrinfeld.FormalODModule.IsODHom.map_mem_gradedPiece p (Rigidified.jPhiS ι ψ g)
      (Rigidified.PhibarS (Φ := Φ) ψ g) (t.XbarS g) _ (hOD.map (reduceMap (p := p) g)) i _ h2
    rw [hjj] at h3
    exact (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hcb i _).mpr h3
  have key : Rigidified.rigidNum ι hcΦ rΦ ψ t hOD g hcb hcΦg w =
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) fΦ hfV hfPi (rΦ w) := by
    obtain ⟨⟨a, b⟩, hab⟩ := (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nMk_surjective (rΦ w)
    show (((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb)
        (Rigidified.rhoC ψ t hOD.1 g) (Rigidified.rhoC_verschiebungInt ψ t hOD.1 g)
        (Rigidified.rhoC_endAct_varpiEnd ψ t hOD g))
      (((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nMap
        ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg)
        (Rigidified.bcPhi (Φ := Φ) ψ g) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ g)
        (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ g)) (rΦ w)) = _
    rw [← hab, nMap_nMk, nMap_nMk, nMap_nMk]
    rfl
  have hrw0 : rΦ w ∈ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nPiece 0 :=
    (AddSubgroup.mem_inf.mp ((hrΦ LΦ hLΦc).mapsTo (Set.mem_univ w))).2
  have hy_piece : p • Rigidified.rigidNum ι hcΦ rΦ ψ t hOD g hcb hcΦg w ∈ ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nPiece 0 := by
    refine AddSubgroup.nsmul_mem _ ?_ _
    rw [key]
    exact nMap_mem_nPiece (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ) ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) fΦ hfV hfPi hfpc 0 (rΦ w) hrw0

  obtain ⟨z, hz, hzy⟩ := hbij.surjOn hy_eta
  obtain ⟨z₀, hz₀, z₁, hz₁, hzz⟩ :=
    CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_mem_etaPiece_add_eq p _ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) L hL z hz
  have hred_piece : ∀ (m : Fin 2) (u : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod), u ∈ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nPiece m →
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) u ∈ ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nPiece m :=
    fun m u hu => nMap_mem_nPiece ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) _ _ _ hbca.2.2.2.2.1 m u hu
  have h0 := hred_piece 0 z₀ (AddSubgroup.mem_inf.mp hz₀).2
  have h1 := hred_piece 1 z₁ (AddSubgroup.mem_inf.mp hz₁).2
  have hNb := CerednikDrinfeld.GradedCartierModuleData.isCompl_nPiece_zero_one p _ ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb)
  have hsum : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) z₀ +
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) z₁ =
      p • Rigidified.rigidNum ι hcΦ rΦ ψ t hOD g hcb hcΦg w := by
    rw [← map_add, ← hzz]; exact hzy
  have h1' : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) z₁ ∈ ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nPiece 0 := by
    have : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) z₁ =
        p • Rigidified.rigidNum ι hcΦ rΦ ψ t hOD g hcb hcΦg w -
        ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) z₀ := by
      rw [← hsum]; abel
    rw [this]; exact AddSubgroup.sub_mem _ hy_piece h0
  have hz1red : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) z₁ = 0 := by
    have := AddSubgroup.mem_inf.mpr ⟨h1', h1⟩
    rwa [hNb.inf_eq_bot, AddSubgroup.mem_bot] at this
  have hz1 : z₁ = 0 := by
    apply hbij.injOn (AddSubgroup.mem_inf.mp hz₁).1 (AddSubgroup.zero_mem _)
    rw [hz1red, map_zero]
  refine ⟨z₀, hz₀, ?_⟩
  show ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) z₀ = _
  rw [← hsum, hz1, map_zero, add_zero]

namespace U2Aux

variable {p : ℕ} [hp : Fact p.Prime]

theorem natCast_p_ne_zero : ((p : ℕ) : ℤ_[p]) ≠ 0 := by
  exact_mod_cast hp.out.ne_zero

theorem natCast_p_ne_zero_Q : ((p : ℕ) : ℚ_[p]) ≠ 0 := by
  exact_mod_cast hp.out.ne_zero

theorem nsmul_eq_pow_smul {n : ℕ} (k : ℕ) (a : Fin n → ℤ_[p]) :
    p ^ k • a = ((p : ℤ_[p]) ^ k) • a := by
  rw [← Nat.cast_smul_eq_nsmul ℤ_[p], Nat.cast_pow]

theorem pow_smul_cancel {n : ℕ} (k : ℕ) (a b : Fin n → ℤ_[p])
    (h : ((p : ℤ_[p]) ^ k) • a = ((p : ℤ_[p]) ^ k) • b) : a = b := by
  funext i
  have hi := congr_fun h i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  exact mul_left_cancel₀ (pow_ne_zero k natCast_p_ne_zero) hi

theorem pow_smul_cancel_Q {n : ℕ} (k : ℕ) (a b : Fin n → ℚ_[p])
    (h : ((p : ℚ_[p]) ^ k) • a = ((p : ℚ_[p]) ^ k) • b) : a = b := by
  funext i
  have hi := congr_fun h i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  exact mul_left_cancel₀ (pow_ne_zero k natCast_p_ne_zero_Q) hi

theorem coe_smul_eq {n : ℕ} (c : ℤ_[p]) (w : Fin n → ℤ_[p]) :
    (fun j => (((c • w) j : ℤ_[p]) : ℚ_[p])) = (c : ℚ_[p]) • fun j => ((w j : ℤ_[p]) : ℚ_[p]) := by
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, PadicInt.coe_mul]

theorem iterate {n : ℕ} (f : (Fin n → ℤ_[p]) →+ (Fin n → ℤ_[p])) (M : ℕ)
    (hM : ∀ w y : Fin n → ℤ_[p], f w = ((p : ℤ_[p]) ^ M) • y → ∃ v : Fin n → ℤ_[p], w = (p : ℤ_[p]) • v) :
    ∀ (j : ℕ) (w y : Fin n → ℤ_[p]), f w = ((p : ℤ_[p]) ^ (M + j)) • y →
      ∃ v : Fin n → ℤ_[p], w = ((p : ℤ_[p]) ^ (j + 1)) • v := by
  intro j
  induction j with
  | zero =>
    intro w y h
    obtain ⟨v, hv⟩ := hM w y (by simpa using h)
    exact ⟨v, by rw [hv, zero_add, pow_one]⟩
  | succ j ih =>
    intro w y h
    obtain ⟨w1, rfl⟩ := hM w (((p : ℤ_[p]) ^ (j + 1)) • y)
      (by rw [h, smul_smul, ← pow_add])
    have h1 : f ((p : ℤ_[p]) • w1) = (p : ℤ_[p]) • f w1 := by
      rw [Nat.cast_smul_eq_nsmul, map_nsmul, Nat.cast_smul_eq_nsmul]
    have h2 : f w1 = ((p : ℤ_[p]) ^ (M + j)) • y := by
      apply pow_smul_cancel 1
      rw [pow_one, ← h1, h, smul_smul, ← pow_succ', add_assoc]
    obtain ⟨v, hv⟩ := ih w1 y h2
    exact ⟨v, by rw [hv, smul_smul, ← pow_succ']⟩

theorem isUnit_of_not_mem {B : Type} [Field B] (x : PrimeSpectrum B) (f : B) (hf : f ∉ x.asIdeal) : IsUnit f := by
  rcases eq_or_ne f 0 with rfl | h
  · exact (hf (Ideal.zero_mem _)).elim
  · exact isUnit_iff_ne_zero.mpr h

theorem charP_of_isNilpotent {B : Type} [Field B] (hB : IsNilpotent ((p : ℕ) : B)) : CharP B p := by
  obtain ⟨n, hn⟩ := hB
  exact (CharP.charP_iff_prime_eq_zero hp.out).mpr (pow_eq_zero_iff'.mp hn).1

end U2Aux

open U2Aux

theorem fibre_bound
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [Algebra ℤ_[p] K] (ψ' : WittVector p k →+* K) (hK : IsNilpotent (p : K))
    (t' : Rigidified p Φ K) (ht' : t'.IsAdmissible ι ψ')
    (hc : t'.IsGradedS ι ψ' (Rigidified.awayHom (1 : K))) (hcb : t'.IsGradedSbar ι ψ' (Rigidified.awayHom (1 : K)))
    (hcΦ1 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ' (Rigidified.awayHom (1 : K)))
    (L' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).M →+
      ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod)
    (hL' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).IsCanonicalLMap L') :
    ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).IsSpecialCartierModule ∧
    ∃ b : ℕ, ∀ (v : Fin 2 → ℚ_[p]) (z : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod),
      t'.IsEtaSection ι hcΦ rΦ ψ' ht'.2.2.1 (Rigidified.awayHom (1 : K)) hc hcb hcΦ1 L' hL' 0 z v →
      ∃ w : Fin 2 → ℤ_[p], (p : ℚ_[p]) ^ b • v = fun j => ((w j : ℤ_[p]) : ℚ_[p]) := by
  classical
  have hS : IsNilpotent ((p : ℕ) : Rigidified.Baway (1 : K)) := by
    obtain ⟨n, hn⟩ := hK
    exact ⟨n, by rw [← map_natCast (Rigidified.awayHom (1 : K)) p, ← map_pow, hn, map_zero]⟩
  obtain ⟨hinj, hD, hW⟩ := W1_core' p ι Φ hcΦ rΦ hLΦ hrΦ ψ' t' ht'.2.2.1 (Rigidified.awayHom (1 : K)) hS hc hcb hcΦ1 L' hL'
  refine ⟨hD, ?_⟩

  obtain ⟨r₀, hr₀⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.exists_bijOn_etaPiece_of_isAlgClosed p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ
    K ψ' hK t' ht' hc hcb hcΦ1 L' hL' 0
  have hr₀eta : ∀ u, r₀ u ∈ (((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).eta L' hL'.isCartierLMap.map_verschiebung : Set _) :=
    fun u => (AddSubgroup.mem_inf.mp (hr₀.mapsTo (Set.mem_univ u))).1

  have he : ∀ a b, t'.etaRed ι ψ' (Rigidified.awayHom (1 : K)) hc hcb (r₀ a) = t'.etaRed ι ψ' (Rigidified.awayHom (1 : K)) hc hcb (r₀ b) → a = b :=
    fun a b hab => hr₀.injOn (Set.mem_univ a) (Set.mem_univ b) (hinj (hr₀eta a) (hr₀eta b) hab)

  have hfex : ∀ w : Fin 2 → ℤ_[p], ∃ u : Fin 2 → ℤ_[p],
      t'.etaRed ι ψ' (Rigidified.awayHom (1 : K)) hc hcb (r₀ u) =
        p • t'.rigidNum ι hcΦ rΦ ψ' ht'.2.2.1 (Rigidified.awayHom (1 : K)) hcb hcΦ1 w := by
    intro w
    obtain ⟨z, hz, hzw⟩ := hW w
    obtain ⟨u, -, rfl⟩ := hr₀.surjOn hz
    exact ⟨u, hzw⟩
  choose f₀ hf₀ using hfex
  let f : (Fin 2 → ℤ_[p]) →+ (Fin 2 → ℤ_[p]) := AddMonoidHom.mk' f₀ (fun a b => he _ _ (by
    rw [map_add, map_add, hf₀, hf₀, hf₀, map_add, nsmul_add]))
  have hf : ∀ w, f w = f₀ w := fun w => rfl
  have hfinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).mpr fun w hw => ?_
    refine CerednikDrinfeld.SpecialFormal.Rigidified.eq_zero_of_nsmul_rigidNum_eq_zero_of_isAlgClosed p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ
      K ψ' hK t' ht' hc hcb hcΦ1 L' hL' w 1 ?_
    rw [pow_one, ← hf₀ w, ← hf, hw, map_zero, map_zero]
  obtain ⟨M, hM⟩ := PadicInt.exists_forall_apply_eq_pow_smul_imp_exists_eq_smul_of_injective p f hfinj
  refine ⟨M, fun v z hz => ?_⟩
  rw [Rigidified.isEtaSection_zero_iff] at hz
  obtain ⟨hzeta, m, kk, w', hvw, hrel⟩ := hz
  obtain ⟨a, -, hra⟩ := hr₀.surjOn hzeta

  have hkey : t'.etaRed ι ψ' (Rigidified.awayHom (1 : K)) hc hcb (r₀ (p ^ kk • f₀ w')) =
      t'.etaRed ι ψ' (Rigidified.awayHom (1 : K)) hc hcb (r₀ (p ^ (kk + t'.n + m + 1) • a)) := by
    simp only [map_nsmul]
    rw [hf₀, hra, smul_smul, mul_comm, ← smul_smul, hrel, smul_smul, ← pow_succ']
  have hkey' : f w' = ((p : ℤ_[p]) ^ (t'.n + m + 1)) • a := by
    have h1 := he _ _ hkey
    rw [nsmul_eq_pow_smul, nsmul_eq_pow_smul, show kk + t'.n + m + 1 = kk + (t'.n + m + 1) by omega, pow_add,
      ← smul_smul] at h1
    exact pow_smul_cancel kk _ _ h1
  rcases le_or_gt M (t'.n + m + 1) with hle | hlt
  · obtain ⟨j, hj⟩ : ∃ j, t'.n + m + 1 = M + j := ⟨t'.n + m + 1 - M, by omega⟩
    rw [hj] at hkey'
    obtain ⟨u, hu⟩ := iterate f M hM j w' a hkey'
    refine ⟨((p : ℤ_[p]) ^ (t'.n + 2)) • u, ?_⟩
    apply pow_smul_cancel_Q m
    rw [smul_smul, mul_comm, ← smul_smul, hvw, hu, coe_smul_eq, coe_smul_eq, smul_smul, smul_smul]
    congr 1
    push_cast
    rw [← pow_add, ← pow_add, show M + (j + 1) = m + (t'.n + 2) by omega]
  · refine ⟨((p : ℤ_[p]) ^ (M - m)) • w', ?_⟩
    rw [coe_smul_eq, ← hvw, smul_smul]
    congr 1
    push_cast
    rw [← pow_add, show M - m + m = M by omega]

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero (Rigidified.jbar ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [Field B] [IsAlgClosed B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) :
    ∀ x : PrimeSpectrum B, ∃ b : ℕ, ∀ v : Fin 2 → ℚ_[p],
      (∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
          (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
          ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v) →
      ∃ w : Fin 2 → ℤ_[p], (p : ℚ_[p]) ^ b • v = fun j => ((w j : ℤ_[p]) : ℚ_[p]) := by
  intro x
  classical
  haveI : CharP B p := charP_of_isNilpotent hB
  have ht1 : (t.map (RingHom.id B)).IsAdmissible ι ((RingHom.id B).comp ψ) :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι ψ (RingHom.id B) t ht
  have hS : IsNilpotent ((p : ℕ) : Rigidified.Baway (1 : B)) := by
    obtain ⟨n, hn⟩ := hB
    exact ⟨n, by rw [← map_natCast (Rigidified.awayHom (1 : B)) p, ← map_pow, hn, map_zero]⟩
  by_cases hex : ∃ (hc1 : (t.map (RingHom.id B)).IsGradedS ι ((RingHom.id B).comp ψ) (Rigidified.awayHom (1 : B)))
      (hcb1 : (t.map (RingHom.id B)).IsGradedSbar ι ((RingHom.id B).comp ψ) (Rigidified.awayHom (1 : B)))
      (hcΦ1 : Rigidified.IsGradedPhiS (Φ := Φ) ι ((RingHom.id B).comp ψ) (Rigidified.awayHom (1 : B)))
      (L1 : (((t.map (RingHom.id B)).XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ((RingHom.id B).comp ψ) (Rigidified.awayHom (1 : B))) hc1).M →+ (((t.map (RingHom.id B)).XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ((RingHom.id B).comp ψ) (Rigidified.awayHom (1 : B))) hc1).NMod),
      (((t.map (RingHom.id B)).XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ((RingHom.id B).comp ψ) (Rigidified.awayHom (1 : B))) hc1).IsCanonicalLMap L1
  · obtain ⟨hc1, hcb1, hcΦ1, L1, hL1⟩ := hex
    obtain ⟨hD, b, hb⟩ := fibre_bound p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ B ((RingHom.id B).comp ψ) hB (t.map (RingHom.id B)) ht1 hc1 hcb1 hcΦ1 L1 hL1
    refine ⟨b, fun v hv => ?_⟩
    obtain ⟨fB, hfB, hc, hcb, hcΦf, L, hL, z, hz⟩ := hv
    obtain ⟨hc', hcb', hcΦ', L', hL', z', hz', -⟩ :=
      CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
        p ι Φ hcΦ rΦ ψ hB t ht fB hc hcb hcΦf L hL 0 z v hz (RingHom.id B) (RingHom.id_comp _) hB
        (isUnit_of_not_mem x fB hfB) ht1
    have hLeq : L' = L1 :=
      CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.eq_of_isNilpotent p
        (Rigidified.jS ι ((RingHom.id B).comp ψ) (Rigidified.awayHom (1 : B))) hS (((t.map (RingHom.id B)).XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ((RingHom.id B).comp ψ) (Rigidified.awayHom (1 : B))) hc1) hD L' L1 hL' hL1
    subst hLeq
    exact hb v z' hz'
  · refine ⟨0, fun v hv => ?_⟩
    obtain ⟨fB, hfB, hc, hcb, hcΦf, L, hL, z, hz⟩ := hv
    obtain ⟨hc', hcb', hcΦ', L', hL', -⟩ :=
      CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
        p ι Φ hcΦ rΦ ψ hB t ht fB hc hcb hcΦf L hL 0 z v hz (RingHom.id B) (RingHom.id_comp _) hB
        (isUnit_of_not_mem x fB hfB) ht1
    exact (hex ⟨hc', hcb', hcΦ', L', hL'⟩).elim

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_isAlgClosed_of_lieZero_le_ker_wittVector
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_isAlgClosed_of_lieZero_le_ker_wittVector (solution)
