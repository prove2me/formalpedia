-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_ringHom_basis_forall_etaRed_nVarpi_iff_and_smul_rigidNum_eq_nMk_mulVec_of_lieOne_le_ker_of_isAlgClosed_wittVector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d4f2bf22-d13c-5fde-b2ab-47c1d80f42d9

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_nMap_bijOn_eta_of_eq_baseChangeEq_mk
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isCanonicalLMap_phibarS_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalODModule_length_gradedSubmodule_quotient_range_mapLinear_eq_of_isIsogenyOfHeight_two_mul_of_isSpecial
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_nMap_bcPhi_apply_mem_etaPiece_zero_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsODHom_map_mem_gradedPiece
import Theorems.Thm_PadicInt_addMonoidHom_map_smul_of_free
import Theorems.Thm_WittVector_exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range
import Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_forall_mem_etaPiece_zero_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_mem_etaPiece_add_eq
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_isCompl_nPiece_zero_one
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_lieZero_lieOne_map_and_eq_span_image
import Theorems.Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_zero_of_lieZero_le_ker_lieVarpi
import Theorems.Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_one_of_lieOne_le_ker_lieVarpi
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_forall_mem_etaPiece_one_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_ringHom_basis_forall_etaRed_nVarpi_iff_and_smul_rigidNum_eq_nMk_mulVec_of_lieOne_le_ker_of_isAlgClosed_wittVector
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

noncomputable section

namespace RFFrame

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

section A1

variable (p : ℕ) [Fact p.Prime] {B : Type} [Field B] [Algebra ℤ_[p] B]

abbrev S (B : Type) [Field B] : Type := Rigidified.Baway (1 : B)

abbrev Sb (p : ℕ) (B : Type) [Field B] : Type := S B ⧸ pIdeal p (S B)

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

theorem natCast_eq_zero_B (hB : IsNilpotent (p : B)) : (p : B) = 0 := hB.eq_zero

theorem charP_B (hB : IsNilpotent (p : B)) : CharP B p :=
  (CharP.charP_iff_prime_eq_zero Fact.out).mpr (natCast_eq_zero_B p hB)

def eBS (B : Type) [Field B] : B ≃+* S B := (IsLocalization.atOne B (S B)).toRingEquiv

theorem eBS_apply (x : B) : eBS B x = Rigidified.awayHom (1 : B) x := rfl

theorem natCast_eq_zero_S (hB : IsNilpotent (p : B)) : (p : S B) = 0 := by
  rw [← map_natCast (Rigidified.awayHom (1 : B)) p, natCast_eq_zero_B p hB, map_zero]

theorem isNilpotent_S (hB : IsNilpotent (p : B)) : IsNilpotent (p : S B) :=
  ⟨1, by rw [pow_one, natCast_eq_zero_S p hB]⟩

theorem pIdeal_S_eq_bot (hB : IsNilpotent (p : B)) : pIdeal p (S B) = ⊥ := by
  rw [pIdeal, natCast_eq_zero_S p hB, Ideal.span_singleton_eq_bot]

def eSSb (hB : IsNilpotent (p : B)) : S B ≃+* Sb p B :=
  ((Ideal.quotEquivOfEq (pIdeal_S_eq_bot p hB)).trans (RingEquiv.quotientBot (S B))).symm

theorem eSSb_apply (hB : IsNilpotent (p : B)) (x : S B) :
    eSSb p hB x = Ideal.Quotient.mk (pIdeal p (S B)) x := rfl

def eBSb (hB : IsNilpotent (p : B)) : B ≃+* Sb p B := (eBS B).trans (eSSb p hB)

theorem isNilpotent_Sb : IsNilpotent (p : Sb p B) :=
  ⟨1, by
    rw [pow_one]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))⟩

@[reducible] def fieldS : Field (S B) := (MulEquiv.isField (Field.toIsField B) (eBS B).symm.toMulEquiv).toField

@[reducible] def fieldSb (hB : IsNilpotent (p : B)) : Field (Sb p B) :=
  (MulEquiv.isField (Field.toIsField B) (eBSb p hB).symm.toMulEquiv).toField

theorem charP_S (hB : IsNilpotent (p : B)) : CharP (S B) p :=
  haveI := charP_B p hB
  charP_of_injective_ringHom (f := (eBS B).toRingHom) (fun a b h => (eBS B).injective h) p

theorem charP_Sb (hB : IsNilpotent (p : B)) : CharP (Sb p B) p :=
  haveI := charP_B p hB
  charP_of_injective_ringHom (f := (eBSb p hB).toRingHom) (fun a b h => (eBSb p hB).injective h) p

theorem isAlgClosed_S [IsAlgClosed B] : @IsAlgClosed (S B) fieldS :=
  letI := fieldS (B := B)
  isAlgClosed_of_ringEquiv (eBS B)

theorem isAlgClosed_Sb [IsAlgClosed B] (hB : IsNilpotent (p : B)) : @IsAlgClosed (Sb p B) (fieldSb p hB) :=
  letI := fieldSb p hB
  isAlgClosed_of_ringEquiv (eBSb p hB)

theorem perfectRing_Sb [IsAlgClosed B] (hB : IsNilpotent (p : B)) : PerfectRing (Sb p B) p := by
  letI := fieldSb p hB
  haveI := isAlgClosed_Sb p hB
  haveI := charP_Sb p hB
  infer_instance

theorem perfectRing_S [IsAlgClosed B] (hB : IsNilpotent (p : B)) : PerfectRing (S B) p := by
  letI := fieldS (B := B)
  haveI := isAlgClosed_S (B := B)
  haveI := charP_S p hB
  infer_instance

end A1

section A2

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
  {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [CommRing B] (ψ : O →+* B)
  (t : Rigidified p Φ B)

theorem jPhiS_eq_jSbar {S' : Type} [CommRing S'] (g : B →+* S') :
    Rigidified.jPhiS ι ψ g = Rigidified.jSbar (p := p) ι ψ g := by
  apply RingHom.ext
  intro a
  show reduceMap g (residueMap ψ (Ideal.Quotient.mk (pIdeal p O) (ι a))) =
    reduceMap g (Ideal.Quotient.mk (pIdeal p B) (ψ (ι a)))
  rw [residueMap, Ideal.quotientMap_mk]

theorem mk_comp_eq_reduceMap_comp_mk {S' : Type} [CommRing S'] (g : B →+* S') :
    (Ideal.Quotient.mk (pIdeal p S')).comp g = (reduceMap (p := p) g).comp (Ideal.Quotient.mk (pIdeal p B)) := by
  apply RingHom.ext; intro b
  show Ideal.Quotient.mk (pIdeal p S') (g b) = reduceMap g (Ideal.Quotient.mk (pIdeal p B) b)
  rw [reduceMap, residueMap, Ideal.quotientMap_mk]

theorem XS_map_mk {S' : Type} [CommRing S'] (g : B →+* S') :
    (t.XS g).map (Ideal.Quotient.mk (pIdeal p S')) = t.XbarS g := by
  show (t.X.map g).map _ = (t.X.map _).map _
  rw [FormalODModule.map_map, FormalODModule.map_map, mk_comp_eq_reduceMap_comp_mk]

theorem mk_comp_jS {S' : Type} [CommRing S'] (g : B →+* S') :
    (Ideal.Quotient.mk (pIdeal p S')).comp (Rigidified.jS ι ψ g) = Rigidified.jSbar ι ψ g := by
  show (Ideal.Quotient.mk (pIdeal p S')).comp (g.comp (ψ.comp ι)) = _
  rw [← RingHom.comp_assoc, mk_comp_eq_reduceMap_comp_mk]
  rfl

theorem isSpecial_XS {S' : Type} [CommRing S'] (g : B →+* S') (ht : t.IsAdmissible ι ψ) :
    (t.XS g).IsSpecial (Rigidified.jS ι ψ g) :=
  CerednikDrinfeld.FormalODModule.IsSpecial.map _ g t.X ht.1

theorem isSpecial_XbarS {S' : Type} [CommRing S'] (g : B →+* S') (ht : t.IsAdmissible ι ψ) :
    (t.XbarS g).IsSpecial (Rigidified.jSbar ι ψ g) := by
  rw [← XS_map_mk, ← mk_comp_jS]
  exact CerednikDrinfeld.FormalODModule.IsSpecial.map _ _ _ (isSpecial_XS ι ψ t g ht)

theorem isSpecial_PhibarS {S' : Type} [CommRing S'] (g : B →+* S') (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) :
    (Rigidified.PhibarS (Φ := Φ) ψ g).IsSpecial (Rigidified.jPhiS ι ψ g) :=
  CerednikDrinfeld.FormalODModule.IsSpecial.map _ _ _ (CerednikDrinfeld.FormalODModule.IsSpecial.map _ _ _ hΦ)

theorem isSpecial_PhibarS' {S' : Type} [CommRing S'] (g : B →+* S') (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) :
    (Rigidified.PhibarS (Φ := Φ) ψ g).IsSpecial (Rigidified.jSbar (p := p) ι ψ g) := by
  rw [← jPhiS_eq_jSbar]; exact isSpecial_PhibarS ι ψ g hΦ

theorem hasHeight_map {R R' : Type u} [CommRing R] [IsNoetherianRing R] [CommRing R'] (f : R →+* R')
    (X : FormalODModule p R) (hX : X.HasHeight 4) : (X.map f).HasHeight 4 := by
  show FormalODModule.HasKernelOfDegree ((X.map f).act (p : Zp2 p)) (p ^ 4)
  rw [FormalODModule.map_act]
  exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f _ (X.isLawHom_act _).1 hX

end A2

section A2'

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsNoetherianRing O] (ι : Zp2 p →+* O)
  {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [Field B] (ψ : O →+* B)
  (t : Rigidified p Φ B)

theorem hasHeight_XS {S' : Type} [CommRing S'] (g : B →+* S') (ht : t.IsAdmissible ι ψ) :
    (t.XS g).HasHeight 4 := hasHeight_map g t.X ht.2.1

theorem hasHeight_XbarS {S' : Type} [CommRing S'] (g : B →+* S') (ht : t.IsAdmissible ι ψ) :
    (t.XbarS g).HasHeight 4 :=
  hasHeight_map _ _ (hasHeight_map _ _ ht.2.1)

theorem hasHeight_PhibarS {S' : Type} [CommRing S'] (g : B →+* S') (hΦ4 : Φ.HasHeight 4) :
    (Rigidified.PhibarS (Φ := Φ) ψ g).HasHeight 4 :=
  hasHeight_map _ _ (hasHeight_map _ _ hΦ4)

theorem isIsogenyOfHeight_rho {S' : Type} [CommRing S'] (g : B →+* S') (ht : t.IsAdmissible ι ψ) :
    FormalODModule.IsIsogenyOfHeight (Rigidified.PhibarS (Φ := Φ) ψ g) (t.XbarS g)
      (t.ρ.map (reduceMap g)) (4 * t.n) :=
  ⟨ht.2.2.1.map (reduceMap g),
    CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map (reduceMap g) t.ρ (fun i => ht.constantCoeff_ρ i) ht.2.2.2⟩

theorem isIsogenyOfHeight_rho' {S' : Type} [CommRing S'] (g : B →+* S') (ht : t.IsAdmissible ι ψ) :
    FormalODModule.IsIsogenyOfHeight (Rigidified.PhibarS (Φ := Φ) ψ g) (t.XbarS g)
      (t.ρ.map (reduceMap g)) (2 * (2 * t.n)) := by
  rw [← mul_assoc]; exact isIsogenyOfHeight_rho ι ψ t g ht

end A2'

section A3

open CerednikDrinfeld.GradedCartierModuleData

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

theorem isHausdorff_of_isNilpotent {S' : Type} [CommRing S'] (hS : IsNilpotent ((p : ℕ) : S')) :
    IsHausdorff (Ideal.span {((p : ℕ) : S')}) S' := by
  obtain ⟨N, hN⟩ := hS
  refine ⟨fun x hx => ?_⟩
  have := hx N
  rwa [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_smul, SModEq.bot] at this

variable {O : Type} [CommRing O] (ι : Zp2 p →+* O)
  {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [CommRing B] (ψ : O →+* B)
  (t : Rigidified p Φ B)

theorem prepBar {S' : Type} [CommRing S'] [Algebra ℤ_[p] S'] (g : B →+* S')
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).M →+
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L) :
    ∃ (hbca : IsBaseChangeAlong' (Ideal.Quotient.mk (pIdeal p S'))
        ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc)
        ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g)),
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsSpecialCartierModule ∧
      ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).IsSpecialCartierModule ∧
      ∃ Lb, ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).IsCanonicalLMap Lb := by
  obtain ⟨Sl, _, jl, φl, _, _, Dl, _, fl, hfl, Ll, _, _⟩ := hL.exists_lift
  obtain ⟨γl, _, hγf⟩ := hfl.2.2.2.2.2
  have hγ : (t.XS g).IsHomogeneousVBasis (Rigidified.jS ι ψ g) (fun i => fl (γl i)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
      p _ _ hc _ hγf
  have hbca : IsBaseChangeAlong' (Ideal.Quotient.mk (pIdeal p S'))
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc)
      ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc _ (XS_map_mk t g) _ (mk_comp_jS ι ψ g) hcb (t.XS_F_map_mk g)
  have hγb : (t.XbarS g).IsHomogeneousVBasis (Rigidified.jSbar ι ψ g) (fun i => t.redC g (fl (γl i))) := by
    refine ⟨fun i => ?_, isUnit_det_tangent_baseChangeEq _ (t.XS_F_map_mk g) _ hγ.2⟩
    exact (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hcb i _).mp
      (hbca.2.2.2.2.1 i _ ((FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hc i _).mpr (hγ.1 i)))
  have hpq : IsNilpotent ((p : ℕ) : S' ⧸ pIdeal p S') :=
    ⟨1, by
      rw [pow_one]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))⟩
  exact ⟨hbca,
    (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ hc).2,
    (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγb hcb).2,
    CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
      (Rigidified.jSbar ι ψ g) (isHausdorff_of_isNilpotent hpq) _ _ hγb hcb⟩

theorem exists_isCanonicalLMap_XbarS {S' : Type} [CommRing S'] [Algebra ℤ_[p] S'] (g : B →+* S')
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).M →+
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L) :
    ∃ Lb, ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).IsCanonicalLMap Lb :=
  (prepBar ι ψ t g hc hcb L hL).2.2.2

theorem etaRed_bijOn {S' : Type} [CommRing S'] [Algebra ℤ_[p] S'] (g : B →+* S') (hS : IsNilpotent (p : S'))
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).M →+
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L)
    (Lb : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).M →+
      ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).NMod)
    (hLb : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).IsCanonicalLMap Lb) :
    Set.BijOn (t.etaRed ι ψ g hc hcb)
      (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).eta L
          hL.isCartierLMap.map_verschiebung : Set _)
      (((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).eta Lb
          hLb.isCartierLMap.map_verschiebung : Set _) := by
  obtain ⟨hbca, hD, hDb, -⟩ := prepBar ι ψ t g hc hcb L hL
  obtain ⟨Sl, _, jl, φl, _, _, Dl, _, fl, hfl, Ll, _, _⟩ := hL.exists_lift
  obtain ⟨γl, _, hγf⟩ := hfl.2.2.2.2.2
  have hγ : (t.XS g).IsHomogeneousVBasis (Rigidified.jS ι ψ g) (fun i => fl (γl i)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
      p _ _ hc _ hγf
  have hpq : IsNilpotent ((p : ℕ) : S' ⧸ pIdeal p S') :=
    ⟨1, by
      rw [pow_one]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))⟩
  have hLL : ∀ x, Lb (t.redC g x) =
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap
        ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g)
        hbca.2.2.1 hbca.2.2.2.1 (L x) :=
    natL_of_eq _ _ hS hpq _ hD _ (mk_comp_jS ι ψ g) _ hDb (t.redC g) hbca L hL Lb hLb
  exact CerednikDrinfeld.FormalODModule.nMap_bijOn_eta_of_eq_baseChangeEq_mk p hS (Rigidified.jS ι ψ g) (t.XS g)
    _ hγ hc (t.XbarS g) (XS_map_mk t g) (Rigidified.jSbar ι ψ g) (mk_comp_jS ι ψ g) hcb (t.XS_F_map_mk g)
    (t.redC g) rfl (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) L hL Lb hLb hLL

end A3

section A4

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]

theorem exists_isCanonicalLMap_PhibarS (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero (Rigidified.jbar ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [Field B] [IsAlgClosed B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (hc : t.IsGradedS ι ψ (Rigidified.awayHom (1 : B))) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : B)))
    (hcΦ1 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : B)))
    (L : ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).M →+ ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).NMod)
    (hL : ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).IsCanonicalLMap L) :
    ∃ LΦ : ((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : B))) hcΦ1).M →+ ((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : B))) hcΦ1).NMod,
      ((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ (Rigidified.awayHom (1 : B))) hcΦ1).IsCanonicalLMap LΦ :=
  haveI := charP_B p hB
  CerednikDrinfeld.SpecialFormal.Rigidified.exists_isCanonicalLMap_phibarS_of_isAlgClosed p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ
    B ψ hB t ht hc hcb hcΦ1 L hL

variable {k}

theorem isCompl_gradedPiece_PhibarS_jSbar {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [CommRing B] (ψ : O →+* B)
    {S' : Type} [CommRing S'] (g : B →+* S')
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g) :
    IsCompl ((Rigidified.PhibarS (Φ := Φ) ψ g).gradedPiece (Rigidified.jSbar ι ψ g) 0)
      ((Rigidified.PhibarS (Φ := Φ) ψ g).gradedPiece (Rigidified.jSbar ι ψ g) 1) := by
  rw [← jPhiS_eq_jSbar]; exact hcΦg

theorem rhoC_graded_colength (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    {B : Type} [Field B] [IsAlgClosed B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : B)))
    (hcΦ1 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : B))) (i : Fin 2) :
    Function.Injective (MvFormalGroup.CartierModule.mapLinear (p := p)
        (isIsogenyOfHeight_rho' ι ψ t (Rigidified.awayHom (1 : B)) ht).1.1.toHom) ∧
    Submodule.map (MvFormalGroup.CartierModule.mapLinear (p := p)
        (isIsogenyOfHeight_rho' ι ψ t (Rigidified.awayHom (1 : B)) ht).1.1.toHom)
        ((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : B))).gradedSubmodule
          (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) (i : ℕ)) ≤
      (t.XbarS (Rigidified.awayHom (1 : B))).gradedSubmodule (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) (i : ℕ) ∧
    Module.length (WittVector p (Sb p B))
        (↥((t.XbarS (Rigidified.awayHom (1 : B))).gradedSubmodule (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) (i : ℕ)) ⧸
          Submodule.comap ((t.XbarS (Rigidified.awayHom (1 : B))).gradedSubmodule
              (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) (i : ℕ)).subtype
            (Submodule.map (MvFormalGroup.CartierModule.mapLinear (p := p)
                (isIsogenyOfHeight_rho' ι ψ t (Rigidified.awayHom (1 : B)) ht).1.1.toHom)
              ((Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : B))).gradedSubmodule
                (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) (i : ℕ)))) = 2 * t.n := by
  letI := fieldSb p hB (B := B)
  haveI := charP_Sb p hB (B := B)
  haveI := isAlgClosed_Sb p hB (B := B)
  haveI : PerfectRing (Sb p B) p := perfectRing_Sb p hB
  have := CerednikDrinfeld.FormalODModule.length_gradedSubmodule_quotient_range_mapLinear_eq_of_isIsogenyOfHeight_two_mul_of_isSpecial
    p (Sb p B) (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B)))
    (Rigidified.PhibarS (Φ := Φ) ψ (Rigidified.awayHom (1 : B))) (t.XbarS (Rigidified.awayHom (1 : B)))
    (isSpecial_PhibarS' ι ψ _ hΦ) (isSpecial_XbarS ι ψ t _ ht)
    (hasHeight_PhibarS ψ _ hΦ4) (hasHeight_XbarS ι ψ t _ ht)
    (isCompl_gradedPiece_PhibarS_jSbar p ι ψ _ hcΦ1) hcb (t.ρ.map (reduceMap (Rigidified.awayHom (1 : B)))) (2 * t.n)
    (isIsogenyOfHeight_rho' ι ψ t (Rigidified.awayHom (1 : B)) ht) i
  exact this

end A4

end RFFrame

end

namespace RCBlocks

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.FormalODModule

variable {p : ℕ} [Fact p.Prime]

theorem nMap_mem_nPiece {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    (hf : ∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i)
    (i : Fin 2) (z : D.NMod) (hz : z ∈ D.nPiece i) : D.nMap D' f hV hPi z ∈ D'.nPiece i := by
  obtain ⟨⟨m, m'⟩, hm, rfl⟩ := AddSubgroup.mem_map.mp hz
  obtain ⟨hm1, hm2⟩ := AddSubgroup.mem_prod.mp hm
  exact AddSubgroup.mem_map.mpr ⟨(f m, f m'), AddSubgroup.mem_prod.mpr ⟨hf i m hm1, hf i m' hm2⟩,
    (nMap_nMk D D' f hV hPi m m').symm⟩

variable {O : Type} [CommRing O] (ι : Zp2 p →+* O)
  {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [CommRing B] (ψ : O →+* B)
  (t : Rigidified p Φ B)

theorem exists_etaRed_eq_iff_mem_etaPiece {S' : Type} [CommRing S'] [Algebra ℤ_[p] S'] (g : B →+* S')
    (hS : IsNilpotent (p : S'))
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).M →+
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L)
    (Lb : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).M →+
      ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).NMod)
    (hLb : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).IsCanonicalLMap Lb)
    (i : Fin 2) (x : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).NMod) :
    (∃ z ∈ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).etaPiece L
        hL.isCartierLMap.map_verschiebung i, t.etaRed ι ψ g hc hcb z = x) ↔
      x ∈ ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).etaPiece Lb
        hLb.isCartierLMap.map_verschiebung i := by
  obtain ⟨hbca, -, -, -⟩ := RFFrame.prepBar ι ψ t g hc hcb L hL
  have hbij := RFFrame.etaRed_bijOn ι ψ t g hS hc hcb L hL Lb hLb
  have hpc : ∀ (i : Fin 2) (z : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod),
      z ∈ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nPiece i →
        t.etaRed ι ψ g hc hcb z ∈ ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nPiece i := by
    intro i z hz
    unfold Rigidified.etaRed
    exact nMap_mem_nPiece ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc)
      ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb)
      (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) hbca.2.2.2.2.1 i z hz
  have hdisj : ∀ y : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).NMod,
      y ∈ ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nPiece 0 →
      y ∈ ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nPiece 1 → y = 0 :=
    fun y => AddSubgroup.disjoint_def.mp (CerednikDrinfeld.GradedCartierModuleData.isCompl_nPiece_zero_one p _
      ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb)).disjoint
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hze, hzp⟩ := AddSubgroup.mem_inf.mp hz
    exact AddSubgroup.mem_inf.mpr ⟨hbij.mapsTo hze, hpc i z hzp⟩
  · intro hx
    obtain ⟨hxe, hxp⟩ := AddSubgroup.mem_inf.mp hx
    obtain ⟨z, hze, hzx⟩ := hbij.surjOn hxe
    obtain ⟨z₀, hz₀, z₁, hz₁, rfl⟩ :=
      CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_mem_etaPiece_add_eq p _ _ L hL _ hze
    have hz₀p := hpc 0 z₀ (AddSubgroup.mem_inf.mp hz₀).2
    have hz₁p := hpc 1 z₁ (AddSubgroup.mem_inf.mp hz₁).2
    have h10 : t.etaRed ι ψ g hc hcb z₁ = x - t.etaRed ι ψ g hc hcb z₀ := by
      rw [← hzx, map_add, add_sub_cancel_left]
    have h01 : t.etaRed ι ψ g hc hcb z₀ = x - t.etaRed ι ψ g hc hcb z₁ := by
      rw [← hzx, map_add, add_sub_cancel_right]
    have hi : i = 0 ∨ i = 1 := by
      rcases i with ⟨_ | _ | n, hn⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega
    rcases hi with rfl | rfl
    · have hz1 : z₁ = 0 := by
        refine hbij.injOn (AddSubgroup.mem_inf.mp hz₁).1 (zero_mem _) ?_
        rw [map_zero]
        exact hdisj _ (by rw [h10]; exact AddSubgroup.sub_mem _ hxp hz₀p) hz₁p
      refine ⟨z₀, hz₀, ?_⟩
      rw [← hzx, hz1, add_zero]
    · have hz0 : z₀ = 0 := by
        refine hbij.injOn (AddSubgroup.mem_inf.mp hz₀).1 (zero_mem _) ?_
        rw [map_zero]
        exact hdisj _ hz₀p (by rw [h01]; exact AddSubgroup.sub_mem _ hxp hz₁p)
      refine ⟨z₁, hz₁, ?_⟩
      rw [← hzx, hz0, zero_add]

theorem lieZero_map_le_ker_lieVarpi {R R' : Type} [CommRing R] [CommRing R'] (j : Zp2 p →+* R)
    (X : FormalODModule p R) (hLie : IsCompl (X.lieZero j) (X.lieOne j))
    (h0 : X.lieZero j ≤ LinearMap.ker X.lieVarpi) (f : R →+* R') :
    (X.map f).lieZero (f.comp j) ≤ LinearMap.ker (X.map f).lieVarpi := by
  rw [(CerednikDrinfeld.FormalODModule.isCompl_lieZero_lieOne_map_and_eq_span_image p j X hLie f).2.1,
    Submodule.span_le]
  rintro _ ⟨m, hm, rfl⟩
  show (X.map f).lieVarpi (⇑f ∘ m) = 0
  have hlin : MvFormalGroup.linearPart (X.map f).varpi = (MvFormalGroup.linearPart X.varpi).map f := by
    ext a b
    show ((X.map f).varpi a).coeff (Finsupp.single b 1) = f ((X.varpi a).coeff (Finsupp.single b 1))
    rw [FormalODModule.map_varpi]
    exact MvPowerSeries.coeff_map _ _ _
  have h0m : X.lieVarpi m = 0 := h0 hm
  funext a
  show (Matrix.mulVec (MvFormalGroup.linearPart (X.map f).varpi) (⇑f ∘ m)) a = 0
  rw [hlin, ← RingHom.map_mulVec]
  show f (X.lieVarpi m a) = 0
  rw [h0m, Pi.zero_apply, map_zero]

theorem exists_eq_sum_smul_of_mem_invariants (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (j : Zp2 p →+* K)
    (Y : FormalODModule p K) (hY : Y.IsSpecial j) (hY4 : Y.HasHeight 4)
    (hc : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1))
    (L : (Y.toGradedCartierModuleData j hc).M →+ (Y.toGradedCartierModuleData j hc).NMod)
    (hL : (Y.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (i : Fin 2) (hi : FormalODModule.CritChart.IsCritical Y j (i : ℕ))
    (c : ℤ_[p] →+* WittVector p K) (e : Fin 2 → MvFormalGroup.CartierModule p Y.F)
    (hep : ∀ r, e r ∈ Y.gradedPiece j (i : ℕ))
    (he : ∀ z, z ∈ (Y.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i ↔
        ∃ a : Fin 2 → ℤ_[p], z = (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a r) • e r, 0))
    (m : MvFormalGroup.CartierModule p Y.F) (hm : m ∈ FormalODModule.CritChart.invariants Y j (i : ℕ)) :
    ∃ a : Fin 2 → ℤ_[p], m = ∑ r, c (a r) • e r := by
  have hV : ∀ f : MvFormalGroup.CartierModule p Y.F,
      MvFormalGroup.CartierModule.verschiebungInt f = MvFormalGroup.CartierModule.verschiebung f :=
    fun f => MvFormalGroup.CartierModule.verschiebungInt_apply_eq_verschiebung f
  have htors : ∀ m : MvFormalGroup.CartierModule p Y.F,
      MvFormalGroup.CartierModule.endAct Y.varpiEnd m = 0 → m = 0 :=
    CerednikDrinfeld.FormalODModule.eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced p j Y hY hY4
  have hi' : ∀ m ∈ Y.gradedPiece j (i : ℕ), ∃ g : MvFormalGroup.CartierModule p Y.F,
      MvFormalGroup.CartierModule.verschiebungInt g = MvFormalGroup.CartierModule.endAct Y.varpiEnd m := by
    intro m hm
    obtain ⟨g, hg⟩ := hi m hm
    exact ⟨g, by rw [hV]; exact hg⟩
  have hLi : ∀ x y : MvFormalGroup.CartierModule p Y.F, x ∈ Y.gradedPiece j (i : ℕ) →
      MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct Y.varpiEnd x →
        L x = (Y.toGradedCartierModuleData j hc).nMk (y, 0) := fun x y hx hy =>
    CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p j Y hc L hL (i : ℕ) hi' x y hx hy
  obtain ⟨hmem, hinj0⟩ :=
    CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
      p j Y hc L hL htors i hi' hLi
  obtain ⟨hm1, hm2⟩ := (FormalODModule.CritChart.mem_invariants_iff Y j _ m).1 hm
  have hz : (Y.toGradedCartierModuleData j hc).nMk (m, 0) ∈
      (Y.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i :=
    (hmem _).2 ⟨m, hm1, by rw [hV]; exact hm2, rfl⟩
  obtain ⟨a, ha⟩ := (he _).1 hz
  have hpiece : (∑ r, c (a r) • e r) ∈ Y.gradedPiece j (i : ℕ) :=
    AddSubgroup.sum_mem _ fun r _ => smul_mem_gradedPiece Y j _ _ _ (hep r)
  exact ⟨a, hinj0 _ _ hm1 hpiece ha⟩

end RCBlocks
namespace RC1Odd

variable {p : ℕ} [Fact p.Prime]

theorem nVarpi_nMk {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (D : GradedCartierModuleData p B j) (m m' : D.M) :
    D.nVarpi (D.nMk (m, m')) = D.nMk (D.varpi m, D.varpi m') := by
  simp only [GradedCartierModuleData.nMk_apply, GradedCartierModuleData.nVarpi, Submodule.mkQ_apply,
    Submodule.mapQ_apply]
  rfl

theorem nMap_nVarpi {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (z : D.NMod) :
    D.nMap D' f hV hPi (D.nVarpi z) = D'.nVarpi (D.nMap D' f hV hPi z) := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [nVarpi_nMk, GradedCartierModuleData.nMap_nMk, GradedCartierModuleData.nMap_nMk, nVarpi_nMk, hPi, hPi]

theorem varpi_mem_invariants_one_of_mem_invariants_zero {B : Type} [CommRing B] [CharP B p]
    (Y : FormalODModule p B) (j : Zp2 p →+* B) (m : CartierModule p Y.F)
    (hm : m ∈ FormalODModule.CritChart.invariants Y j 0) :
    endAct Y.varpiEnd m ∈ FormalODModule.CritChart.invariants Y j 1 ∧
      (p : ℕ) • m = endAct Y.varpiEnd (endAct Y.varpiEnd m) := by
  obtain ⟨hm0, hmPi⟩ := (FormalODModule.CritChart.mem_invariants_iff Y j 0 m).1 hm
  refine ⟨(FormalODModule.CritChart.mem_invariants_iff Y j 1 _).2 ⟨?_, ?_⟩, ?_⟩
  · exact FormalODModule.endAct_varpiEnd_mem_gradedPiece_succ Y j 0 m hm0
  · conv_lhs => rw [hmPi]
    rw [← verschiebungInt_eq_verschiebung]
    exact endAct_verschiebungInt Y.varpiEnd m
  · exact (FormalODModule.endAct_varpiEnd_endAct_varpiEnd Y m).symm

end RC1Odd

namespace RC1Odd

variable {p : ℕ} [Fact p.Prime]

theorem exists_nVarpi_eq_iff {S' : Type} [CommRing S'] (j : Zp2 p →+* S') (Y : FormalODModule p S')
    (hc : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1))
    (η : Set (Y.toGradedCartierModuleData j hc).NMod)
    (c : ℤ_[p] →+* WittVector p S') (e : Fin 2 → CartierModule p Y.F)
    (hη : ∀ z, z ∈ η ↔ ∃ a : Fin 2 → ℤ_[p], z = (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a r) • e r, 0)) :
    ∀ x, (∃ z ∈ η, (Y.toGradedCartierModuleData j hc).nVarpi z = x) ↔
      ∃ a : Fin 2 → ℤ_[p], x = (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a r) • Y.varpiLinear (e r), 0) := by
  intro x
  have hPi : ∀ a : Fin 2 → ℤ_[p],
      (Y.toGradedCartierModuleData j hc).nVarpi ((Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a r) • e r, 0)) =
        (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a r) • Y.varpiLinear (e r), 0) := by
    intro a
    rw [nVarpi_nMk, map_zero]
    congr 1
    refine Prod.ext ?_ rfl
    show Y.varpiLinear (∑ r, c (a r) • e r) = ∑ r, c (a r) • Y.varpiLinear (e r)
    rw [map_sum]
    exact Finset.sum_congr rfl fun r _ => Y.varpiLinear.map_smul (c (a r)) (e r)
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨a, rfl⟩ := (hη z).1 hz
    exact ⟨a, hPi a⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, (hη _).2 ⟨a, rfl⟩, hPi a⟩

theorem eq_of_nMk_sum_varpi_eq {S' : Type} [CommRing S'] (j : Zp2 p →+* S') (Y : FormalODModule p S')
    (hc : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1))
    (c : ℤ_[p] →+* WittVector p S') (e : Fin 2 → CartierModule p Y.F)
    (he : ∀ r, e r ∈ Y.gradedPiece j 1)
    (hinj0 : ∀ m m' : CartierModule p Y.F, m ∈ Y.gradedPiece j 0 → m' ∈ Y.gradedPiece j 0 →
      (Y.toGradedCartierModuleData j hc).nMk (m, 0) = (Y.toGradedCartierModuleData j hc).nMk (m', 0) → m = m')
    (htors : ∀ m : CartierModule p Y.F, endAct Y.varpiEnd m = 0 → m = 0)
    (hinje : ∀ a a' : Fin 2 → ℤ_[p], (∑ r, c (a r) • e r) = ∑ r, c (a' r) • e r → a = a') :
    ∀ a a' : Fin 2 → ℤ_[p],
      (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a r) • Y.varpiLinear (e r), 0) =
        (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a' r) • Y.varpiLinear (e r), 0) → a = a' := by
  intro a a' h
  have hmem : ∀ b : Fin 2 → ℤ_[p], (∑ r, c (b r) • Y.varpiLinear (e r)) ∈ Y.gradedPiece j 0 := by
    intro b
    refine (Y.gradedSubmodule j 0).sum_mem fun r _ => (Y.gradedSubmodule j 0).smul_mem _ ?_
    have h' : endAct Y.varpiEnd (e r) ∈ Y.gradedPiece j 2 :=
      FormalODModule.endAct_varpiEnd_mem_gradedPiece_succ Y j 1 (e r) (he r)
    have h2 : Y.gradedPiece j 2 = Y.gradedPiece j 0 := FormalODModule.gradedPiece_add_two Y j 0
    rw [h2] at h'
    exact h'
  have h1 := hinj0 _ _ (hmem a) (hmem a') h
  have h2 : Y.varpiLinear (∑ r, c (a r) • e r) = Y.varpiLinear (∑ r, c (a' r) • e r) := by
    simpa only [map_sum, map_smul] using h1
  refine hinje a a' (?_)
  have h3 : Y.varpiLinear ((∑ r, c (a r) • e r) - ∑ r, c (a' r) • e r) = 0 := by rw [map_sub, h2, sub_self]
  exact sub_eq_zero.1 (htors _ h3)

theorem exists_smul_eq_nMk_sum_varpi {S' : Type} [CommRing S'] [CharP S' p] (j : Zp2 p →+* S')
    (Y : FormalODModule p S') (hc : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1))
    (c : ℤ_[p] →+* WittVector p S') (e : Fin 2 → CartierModule p Y.F)
    (hQ : ∀ m ∈ FormalODModule.CritChart.invariants Y j 1, ∃ a : Fin 2 → ℤ_[p], m = ∑ r, c (a r) • e r)
    (r : (Fin 2 → ℤ_[p]) →+ (Y.toGradedCartierModuleData j hc).NMod)
    (hr : ∀ w, ∃ y ∈ FormalODModule.CritChart.invariants Y j 0, r w = (Y.toGradedCartierModuleData j hc).nMk (y, 0)) :
    ∀ w, ∃ a : Fin 2 → ℤ_[p],
      p • r w = (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a r) • Y.varpiLinear (e r), 0) := by
  intro w
  obtain ⟨y, hy, hyw⟩ := hr w
  obtain ⟨hPiy, hpy⟩ := varpi_mem_invariants_one_of_mem_invariants_zero Y j y hy
  obtain ⟨a, ha⟩ := hQ _ hPiy
  refine ⟨a, ?_⟩
  rw [hyw, ← map_nsmul, Prod.smul_mk, smul_zero]
  congr 1
  refine Prod.ext ?_ rfl
  show (p : ℕ) • y = ∑ r, c (a r) • Y.varpiLinear (e r)
  rw [hpy, ha, ← FormalODModule.varpiLinear_apply, map_sum]
  exact Finset.sum_congr rfl fun r _ => Y.varpiLinear.map_smul (c (a r)) (e r)

end RC1Odd

namespace RC1Aux

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

theorem nMk_fst_injective {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (E : GradedCartierModuleData p B j) (htors : ∀ m : E.M, E.varpi m = 0 → m = 0)
    (m m' : E.M) (h : E.nMk (m, 0) = E.nMk (m', 0)) : m = m' := by
  rw [nMk_apply, nMk_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨x, hx⟩ : ∃ x, E.nRelMap x = (m, E.toSigma 0) - (m', E.toSigma 0) := LinearMap.mem_range.mp h
  rw [nRelMap_apply, Prod.mk_sub_mk, Prod.mk.injEq] at hx
  obtain ⟨h1, h2⟩ := hx
  have hneg : -E.varpi (E.ofSigma x) = 0 := by
    have h3 : E.toSigma (-E.varpi (E.ofSigma x)) = 0 := by rw [h2, sub_self]
    exact h3
  have hx0 : E.ofSigma x = 0 := htors _ (neg_eq_zero.mp hneg)
  rw [hx0, map_zero] at h1
  exact (sub_eq_zero.mp h1.symm)

end RC1Aux

open RFFrame RCBlocks CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule in

set_option maxHeartbeats 3200000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (ι : Zp2 p →+* WittVector p k)
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
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (hc : t.IsGradedS ι ψ (Rigidified.awayHom (1 : B))) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : B)))
    (hcΦ1 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : B)))
    (L : ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).M →+ ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).NMod)
    (hL : ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).IsCanonicalLMap L)
    (h1X : t.X.lieOne (structureMap ι ψ) ≤ LinearMap.ker t.X.lieVarpi) :
    ∃ (c : ℤ_[p] →+* WittVector p (Rigidified.Baway (1 : B) ⧸ pIdeal p (Rigidified.Baway (1 : B))))
      (e : Fin 2 → MvFormalGroup.CartierModule p (t.XbarS (Rigidified.awayHom (1 : B))).F)
      (γ : Matrix (Fin 2) (Fin 2) ℤ_[p]),
      (∀ r, e r ∈ (t.XbarS (Rigidified.awayHom (1 : B))).gradedPiece (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) 1) ∧
      (∀ m ∈ (t.XbarS (Rigidified.awayHom (1 : B))).gradedPiece (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) 1,
        ∃! w : Fin 2 → WittVector p (Rigidified.Baway (1 : B) ⧸ pIdeal p (Rigidified.Baway (1 : B))), m = ∑ r, w r • e r) ∧
      (∀ x : ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).NMod,
        (∃ z ∈ ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).etaPiece L hL.isCartierLMap.map_verschiebung 1,
            t.etaRed ι ψ (Rigidified.awayHom (1 : B)) hc hcb (((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).nVarpi z) = x) ↔
          ∃ a : Fin 2 → ℤ_[p], x = ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).nMk (∑ r, c (a r) • (t.XbarS (Rigidified.awayHom (1 : B))).varpiLinear (e r), 0)) ∧
      (∀ a a' : Fin 2 → ℤ_[p],
        ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).nMk (∑ r, c (a r) • (t.XbarS (Rigidified.awayHom (1 : B))).varpiLinear (e r), 0) = ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).nMk (∑ r, c (a' r) • (t.XbarS (Rigidified.awayHom (1 : B))).varpiLinear (e r), 0) → a = a') ∧
      (∀ w : Fin 2 → ℤ_[p],
        p • t.rigidNum ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom (1 : B)) hcb hcΦ1 w =
          ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).nMk (∑ r, c ((γ.mulVec w) r) • (t.XbarS (Rigidified.awayHom (1 : B))).varpiLinear (e r), 0)) := by
  classical
  letI instF : Field (Sb p B) := RFFrame.fieldSb p hB
  haveI : CharP (Sb p B) p := RFFrame.charP_Sb p hB
  haveI : IsAlgClosed (Sb p B) := RFFrame.isAlgClosed_Sb p hB
  haveI : CharP B p := RFFrame.charP_B p hB
  set g₁ : B →+* S B := Rigidified.awayHom (1 : B) with hg₁

  set Db := (t.XbarS g₁).toGradedCartierModuleData (Rigidified.jSbar ι ψ g₁) hcb with hDb
  obtain ⟨Lb, hLb⟩ := RFFrame.exists_isCanonicalLMap_XbarS ι ψ t g₁ hc hcb L hL

  have hXbar_eq : t.X.map ((reduceMap (p := p) g₁).comp (Ideal.Quotient.mk (pIdeal p B))) = t.XbarS g₁ := by
    show _ = (t.X.map _).map _
    rw [FormalODModule.map_map]
  have h1bar : FormalODModule.CritChart.IsCritical (t.XbarS g₁) (Rigidified.jSbar ι ψ g₁) 1 := by
    have := CerednikDrinfeld.FormalODModule.CritChart.isCritical_map_one_of_lieOne_le_ker_lieVarpi p
      (structureMap ι ψ) t.X ht.1.1 h1X ((reduceMap (p := p) g₁).comp (Ideal.Quotient.mk (pIdeal p B)))
    rw [hXbar_eq] at this
    exact this
  have hΦbar_eq : Φ.map ((reduceMap (p := p) g₁).comp (residueMap ψ)) = Rigidified.PhibarS (Φ := Φ) ψ g₁ := by
    show _ = (Φ.map _).map _
    rw [FormalODModule.map_map]
  have h0Φbar : FormalODModule.CritChart.IsCritical (Rigidified.PhibarS (Φ := Φ) ψ g₁) (Rigidified.jPhiS ι ψ g₁) 0 := by
    have := CerednikDrinfeld.FormalODModule.CritChart.isCritical_map_zero_of_lieZero_le_ker_lieVarpi p
      (Rigidified.jbar ι) Φ hΦ.1 h0Φ ((reduceMap (p := p) g₁).comp (residueMap ψ))
    rw [hΦbar_eq] at this
    exact this
  obtain ⟨c, -, -⟩ := WittVector.exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range p (Sb p B)

  obtain ⟨e, he_inv, he_basis, he_eta, he_inj⟩ :=
    CerednikDrinfeld.FormalODModule.exists_forall_mem_etaPiece_one_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed
      p (Sb p B) (Rigidified.jSbar ι ψ g₁) (t.XbarS g₁) (isSpecial_XbarS ι ψ t g₁ ht) (hasHeight_XbarS ι ψ t g₁ ht)
      hcb Lb hLb h1bar c
  have hep : ∀ r, e r ∈ (t.XbarS g₁).gradedPiece (Rigidified.jSbar ι ψ g₁) 1 := fun r =>
    ((FormalODModule.CritChart.mem_invariants_iff _ _ _ _).1 (he_inv r)).1
  have htorsX : ∀ m : CartierModule p (t.XbarS g₁).F, endAct (t.XbarS g₁).varpiEnd m = 0 → m = 0 :=
    CerednikDrinfeld.FormalODModule.eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced p (Rigidified.jSbar ι ψ g₁) _
      (isSpecial_XbarS ι ψ t g₁ ht) (hasHeight_XbarS ι ψ t g₁ ht)

  obtain ⟨LΦ, hLΦ⟩ := RFFrame.exists_isCanonicalLMap_PhibarS p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ ψ hB t ht hc hcb hcΦ1 L hL
  have hVΦ : ∀ f : CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ g₁).F, verschiebungInt f = verschiebung f :=
    fun f => verschiebungInt_apply_eq_verschiebung f
  have htorsΦ : ∀ m : CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ g₁).F,
      endAct (Rigidified.PhibarS (Φ := Φ) ψ g₁).varpiEnd m = 0 → m = 0 :=
    CerednikDrinfeld.FormalODModule.eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced p (Rigidified.jPhiS ι ψ g₁) _
      (isSpecial_PhibarS ι ψ g₁ hΦ) (hasHeight_PhibarS ψ g₁ hΦ4)
  have hiΦ : ∀ m ∈ (Rigidified.PhibarS (Φ := Φ) ψ g₁).gradedPiece (Rigidified.jPhiS ι ψ g₁) ((0 : Fin 2) : ℕ),
      ∃ g : CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ g₁).F,
        verschiebungInt g = endAct (Rigidified.PhibarS (Φ := Φ) ψ g₁).varpiEnd m := by
    intro m hm
    obtain ⟨g, hg⟩ := h0Φbar m hm
    exact ⟨g, by rw [hVΦ]; exact hg⟩
  have hLiΦ := fun x y hx hy =>
    CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p (Rigidified.jPhiS ι ψ g₁) _ hcΦ1 LΦ hLΦ
      ((0 : Fin 2) : ℕ) hiΦ x y hx hy
  obtain ⟨hmemΦ, -⟩ :=
    CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
      p (Rigidified.jPhiS ι ψ g₁) _ hcΦ1 LΦ hLΦ htorsΦ 0 hiΦ hLiΦ

  have hr : ∀ w : Fin 2 → ℤ_[p], ∃ y ∈ FormalODModule.CritChart.invariants (t.XbarS g₁) (Rigidified.jSbar ι ψ g₁) 0,
      t.rigidNum ι hcΦ rΦ ψ ht.2.2.1 g₁ hcb hcΦ1 w = Db.nMk (y, 0) := by
    intro w
    have hmemw := CerednikDrinfeld.SpecialFormal.Rigidified.nMap_bcPhi_apply_mem_etaPiece_zero_of_isAlgClosed p k ι Φ
      hΦ hΦ4 h0Φ hcΦ rΦ hrΦ B ψ hB t ht hc hcb hcΦ1 L hL LΦ hLΦ w
    obtain ⟨m', hm'0, hm'inv, hm'eq⟩ := (hmemΦ _).1 hmemw
    have hrig : t.rigidNum ι hcΦ rΦ ψ ht.2.2.1 g₁ hcb hcΦ1 w = Db.nMk (Rigidified.rhoC ψ t ht.2.2.1.1 g₁ m', 0) := by
      show ((Rigidified.PhibarS (Φ := Φ) ψ g₁).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g₁) hcΦ1).nMap Db
          (Rigidified.rhoC ψ t ht.2.2.1.1 g₁) (Rigidified.rhoC_verschiebungInt ψ t ht.2.2.1.1 g₁)
          (Rigidified.rhoC_endAct_varpiEnd ψ t ht.2.2.1 g₁)
          (((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nMap
            ((Rigidified.PhibarS (Φ := Φ) ψ g₁).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g₁) hcΦ1)
            (Rigidified.bcPhi (Φ := Φ) ψ g₁) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ g₁)
            (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ g₁)) (rΦ w)) = _
      rw [hm'eq, nMap_nMk, map_zero]
      rfl
    have hρOD : FormalODModule.IsODHom (Rigidified.PhibarS (Φ := Φ) ψ g₁) (t.XbarS g₁) (t.ρ.map (reduceMap g₁)) :=
      ht.2.2.1.map (reduceMap g₁)
    have hm'0' : m' ∈ (Rigidified.PhibarS (Φ := Φ) ψ g₁).gradedPiece (Rigidified.jSbar ι ψ g₁) 0 := by
      rw [← jPhiS_eq_jSbar]; exact hm'0
    have hρm0 : Rigidified.rhoC ψ t ht.2.2.1.1 g₁ m' ∈ (t.XbarS g₁).gradedPiece (Rigidified.jSbar ι ψ g₁) 0 :=
      CerednikDrinfeld.FormalODModule.IsODHom.map_mem_gradedPiece p (Rigidified.jSbar ι ψ g₁) _ _ _ hρOD 0 m' hm'0'
    have hρinv : endAct (t.XbarS g₁).varpiEnd (Rigidified.rhoC ψ t ht.2.2.1.1 g₁ m') =
        verschiebungInt (Rigidified.rhoC ψ t ht.2.2.1.1 g₁ m') := by
      rw [← Rigidified.rhoC_endAct_varpiEnd ψ t ht.2.2.1 g₁ m', hm'inv, Rigidified.rhoC_verschiebungInt]
    exact ⟨_, (FormalODModule.CritChart.mem_invariants_iff _ _ _ _).2
      ⟨hρm0, by rw [hρinv]; exact verschiebungInt_apply_eq_verschiebung _⟩, hrig⟩

  have hQ : ∀ m ∈ FormalODModule.CritChart.invariants (t.XbarS g₁) (Rigidified.jSbar ι ψ g₁) 1,
      ∃ a : Fin 2 → ℤ_[p], m = ∑ r, c (a r) • e r := fun m hm =>
    exists_eq_sum_smul_of_mem_invariants (Sb p B) (Rigidified.jSbar ι ψ g₁) (t.XbarS g₁)
      (isSpecial_XbarS ι ψ t g₁ ht) (hasHeight_XbarS ι ψ t g₁ ht) hcb Lb hLb 1 h1bar c e hep he_eta m hm
  have key := RC1Odd.exists_smul_eq_nMk_sum_varpi (Rigidified.jSbar ι ψ g₁) (t.XbarS g₁) hcb c e hQ
    (t.rigidNum ι hcΦ rΦ ψ ht.2.2.1 g₁ hcb hcΦ1) hr
  choose α hα using key

  have hinj : ∀ a a' : Fin 2 → ℤ_[p],
      Db.nMk (∑ r, c (a r) • (t.XbarS g₁).varpiLinear (e r), 0) =
        Db.nMk (∑ r, c (a' r) • (t.XbarS g₁).varpiLinear (e r), 0) → a = a' :=
    RC1Odd.eq_of_nMk_sum_varpi_eq (Rigidified.jSbar ι ψ g₁) (t.XbarS g₁) hcb c e hep
      (fun m m' _ _ h => RC1Aux.nMk_fst_injective Db htorsX m m' h) htorsX
      (fun a a' h => he_inj a a' (congrArg (fun v => Db.nMk (v, 0)) h))

  have hsum : ∀ a a' : Fin 2 → ℤ_[p],
      Db.nMk (∑ r, c ((a + a') r) • (t.XbarS g₁).varpiLinear (e r), 0) =
        Db.nMk (∑ r, c (a r) • (t.XbarS g₁).varpiLinear (e r), 0) +
          Db.nMk (∑ r, c (a' r) • (t.XbarS g₁).varpiLinear (e r), 0) := by
    intro a a'
    rw [← map_add, Prod.mk_add_mk, add_zero, ← Finset.sum_add_distrib]
    refine congrArg (fun v => Db.nMk (v, 0)) ?_
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Pi.add_apply, map_add, add_smul]
    rfl
  have hαadd : ∀ w w', α (w + w') = α w + α w' := fun w w' =>
    hinj _ _ (by rw [hsum, ← hα, ← hα, ← hα, map_add, nsmul_add])
  let αh : (Fin 2 → ℤ_[p]) →+ (Fin 2 → ℤ_[p]) := AddMonoidHom.mk' α hαadd
  have hαsmul : ∀ (s : ℤ_[p]) (x : Fin 2 → ℤ_[p]), α (s • x) = s • α x := fun s x =>
    PadicInt.addMonoidHom_map_smul_of_free p αh s x
  let αl : (Fin 2 → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 2 → ℤ_[p]) :=
    { toFun := α, map_add' := hαadd, map_smul' := hαsmul }
  have hγ : ∀ w, (LinearMap.toMatrix' αl).mulVec w = α w := fun w => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl

  have hNV : ∀ z : ((t.XS g₁).toGradedCartierModuleData (Rigidified.jS ι ψ g₁) hc).NMod,
      t.etaRed ι ψ g₁ hc hcb (((t.XS g₁).toGradedCartierModuleData (Rigidified.jS ι ψ g₁) hc).nVarpi z) =
        Db.nVarpi (t.etaRed ι ψ g₁ hc hcb z) := fun z => by
    unfold Rigidified.etaRed
    exact RC1Odd.nMap_nVarpi ((t.XS g₁).toGradedCartierModuleData (Rigidified.jS ι ψ g₁) hc) Db
      (t.redC g₁) (t.redC_verschiebungInt g₁) (t.redC_endAct_varpiEnd g₁) z
  refine ⟨c, e, LinearMap.toMatrix' αl, hep, he_basis, ?_, hinj, fun w => ?_⟩
  · intro x
    rw [← RC1Odd.exists_nVarpi_eq_iff (Rigidified.jSbar ι ψ g₁) (t.XbarS g₁) hcb
      (Db.etaPiece Lb hLb.isCartierLMap.map_verschiebung 1 : Set _) c e he_eta x]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨t.etaRed ι ψ g₁ hc hcb z, ?_, (hNV z).symm⟩
      exact (exists_etaRed_eq_iff_mem_etaPiece ι ψ t g₁ (isNilpotent_S p hB) hc hcb L hL Lb hLb 1 _).1 ⟨z, hz, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := (exists_etaRed_eq_iff_mem_etaPiece ι ψ t g₁ (isNilpotent_S p hB) hc hcb L hL Lb hLb 1 y).2 hy
      exact ⟨z, hz, hNV z⟩
  · rw [hγ]; exact hα w

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_ringHom_basis_forall_etaRed_nVarpi_iff_and_smul_rigidNum_eq_nMk_mulVec_of_lieOne_le_ker_of_isAlgClosed_wittVector
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_ringHom_basis_forall_etaRed_nVarpi_iff_and_smul_rigidNum_eq_nMk_mulVec_of_lieOne_le_ker_of_isAlgClosed_wittVector (solution)
