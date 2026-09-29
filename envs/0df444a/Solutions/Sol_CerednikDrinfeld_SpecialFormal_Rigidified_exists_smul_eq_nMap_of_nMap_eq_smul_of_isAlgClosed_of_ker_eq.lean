-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isAlgClosed_of_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/99cc50de-7696-56d7-b707-dfcdf2d1f8de

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

import Theorems.Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_exists_smul_eq_nMap_nMap_of_surjective_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isAlgClosed_of_ker_eq
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace DivDescentAsmKit

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

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

omit [Fact p.Prime] in
theorem isHausdorff_of_isNilpotent {S : Type} [CommRing S] (hS : IsNilpotent ((p : ℕ) : S)) :
    IsHausdorff (Ideal.span {((p : ℕ) : S)}) S := by
  obtain ⟨N, hN⟩ := hS
  refine ⟨fun x hx => ?_⟩
  have := hx N
  rwa [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_smul, SModEq.bot] at this

theorem isHomogeneousVBasis_push {B S : Type} [CommRing B] [CommRing S] {j : Zp2 p →+* B} {j' : Zp2 p →+* S}
    (g : B →+* S) (X : FormalODModule p B) (X' : FormalODModule p S)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) (hc' : IsCompl (X'.gradedPiece j' 0) (X'.gradedPiece j' 1))
    (hF : X.F.map g = X'.F) (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hbca : IsBaseChangeAlong' g (X.toGradedCartierModuleData j hc) (X'.toGradedCartierModuleData j' hc') (CartierModule.baseChangeEq g hF)) :
    X'.IsHomogeneousVBasis j' (fun i => CartierModule.baseChangeEq g hF (γ i)) := by
  refine ⟨fun i => ?_, ?_⟩
  · exact (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hc' i _).mp
      (hbca.2.2.2.2.1 i _ ((FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hc i _).mpr (hγ.1 i)))
  · exact isUnit_det_tangent_baseChangeEq _ hF _ hγ.2

theorem nMap_mem_eta {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ m, f (D.verschiebung m) = D'.verschiebung (f m))
    (hP : ∀ m, f (D.varpi m) = D'.varpi (f m))
    (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (L' : D'.M →+ D'.NMod) (hL' : ∀ x : D'.M, L' (D'.verschiebung x) = D'.nMk (D'.varpi x, 0))
    (hLL' : ∀ m, L' (f m) = D.nMap D' f hV hP (L m)) (z : D.NMod) (hz : z ∈ D.eta L hL) :
    D.nMap D' f hV hP z ∈ D'.eta L' hL' := by
  rw [mem_eta_iff] at hz ⊢
  obtain ⟨⟨x, x'⟩, rfl⟩ := D.nMk_surjective z
  conv_rhs => rw [← hz]
  rw [phi_nMk, map_add, nMap_nMk, nMap_nMk, phi_nMk, hLL', map_zero]

theorem nMap_mem_nPiece {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ m, f (D.verschiebung m) = D'.verschiebung (f m))
    (hP : ∀ m, f (D.varpi m) = D'.varpi (f m))
    (hf : ∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i)
    (i : Fin 2) (z : D.NMod) (hz : z ∈ D.nPiece i) : D.nMap D' f hV hP z ∈ D'.nPiece i := by
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := hz
  refine ⟨(f a, f b), ⟨hf i a hab.1, hf i b hab.2⟩, ?_⟩
  show D'.nMk (f a, f b) = D.nMap D' f hV hP (D.nMk (a, b))
  rw [nMap_nMk]

theorem nMap_mem_etaPiece {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ m, f (D.verschiebung m) = D'.verschiebung (f m))
    (hP : ∀ m, f (D.varpi m) = D'.varpi (f m))
    (hf : ∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i)
    (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (L' : D'.M →+ D'.NMod) (hL' : ∀ x : D'.M, L' (D'.verschiebung x) = D'.nMk (D'.varpi x, 0))
    (hLL' : ∀ m, L' (f m) = D.nMap D' f hV hP (L m)) (i : Fin 2) (z : D.NMod) (hz : z ∈ D.etaPiece L hL i) :
    D.nMap D' f hV hP z ∈ D'.etaPiece L' hL' i :=
  AddSubgroup.mem_inf.mpr ⟨nMap_mem_eta D D' f hV hP L hL L' hL' hLL' z (AddSubgroup.mem_inf.mp hz).1,
    nMap_mem_nPiece D D' f hV hP hf i z (AddSubgroup.mem_inf.mp hz).2⟩

theorem nMap_nMap_eq {B1 B2 B3 : Type} [CommRing B1] [CommRing B2] [CommRing B3]
    {j1 : Zp2 p →+* B1} {j2 : Zp2 p →+* B2} {j3 : Zp2 p →+* B3}
    (D1 : GradedCartierModuleData p B1 j1) (D2 : GradedCartierModuleData p B2 j2)
    (D3 : GradedCartierModuleData p B3 j3)
    (f : D1.M →+ D2.M) (hfV : ∀ x, f (D1.verschiebung x) = D2.verschiebung (f x))
    (hfPi : ∀ x, f (D1.varpi x) = D2.varpi (f x))
    (g : D2.M →+ D3.M) (hgV : ∀ x, g (D2.verschiebung x) = D3.verschiebung (g x))
    (hgPi : ∀ x, g (D2.varpi x) = D3.varpi (g x))
    (k : D1.M →+ D3.M) (hkV : ∀ x, k (D1.verschiebung x) = D3.verschiebung (k x))
    (hkPi : ∀ x, k (D1.varpi x) = D3.varpi (k x))
    (hc : ∀ x, g (f x) = k x) (z : D1.NMod) :
    D2.nMap D3 g hgV hgPi (D1.nMap D2 f hfV hfPi z) = D1.nMap D3 k hkV hkPi z := by
  obtain ⟨⟨a, b⟩, rfl⟩ := D1.nMk_surjective z
  rw [nMap_nMk, nMap_nMk, nMap_nMk, hc, hc]

end DivDescentAsmKit

open DivDescentAsmKit CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (i : Fin 2) (f : B) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
    (L : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M →+ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (z : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung i)
    {K : Type} [Field K] [IsAlgClosed K] [Algebra ℤ_[p] K] (g : B →+* K)
    (hg : g.comp (algebraMap ℤ_[p] B) = algebraMap ℤ_[p] K)
    (x : PrimeSpectrum B) (hx : RingHom.ker g = x.asIdeal) (hgf : IsUnit (g f))
    (ht' : (t.map g).IsAdmissible ι (g.comp ψ))
    (hc' : (t.map g).IsGradedS ι (g.comp ψ) (Rigidified.awayHom (1 : K)))
    (L' : (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').M →+ (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').NMod) (hL' : (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').IsCanonicalLMap L')
    (hXh : (t.XS (Rigidified.awayHom f)).F.map ((algebraMap K (Rigidified.Baway (1 : K))).comp (IsLocalization.Away.lift f (g := g) hgf : Rigidified.Baway f →+* K)) = ((t.map g).XS (Rigidified.awayHom (1 : K))).F)
    (hbcV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).verschiebung m) =
      (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXh m))
    (hbcPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).varpi m) =
      (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXh m))
    (hdiv : ∃ y ∈ (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i,
      ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).nMap (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc') (MvFormalGroup.CartierModule.baseChangeEq _ hXh) hbcV hbcPi z = p • y) :
    ∃ (f₀ : B) (_ : f₀ ∉ x.asIdeal) (hc₀ : t.IsGradedS ι ψ (Rigidified.awayHom (f * f₀)))
      (L₀ : ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).M →+ ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).NMod) (hL₀ : ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀)
      (hXr : (t.XS (Rigidified.awayHom f)).F.map (IsLocalization.Away.awayToAwayRight f f₀ : Rigidified.Baway f →+* Rigidified.Baway (f * f₀)) = (t.XS (Rigidified.awayHom (f * f₀))).F)
      (hrV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).verschiebung m) =
        ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (hrPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).varpi m) =
        ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (z₀ : ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).NMod),
      z₀ ∈ ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung i ∧
        p • z₀ = ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).nMap ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXr) hrV hrPi z := by
  classical

  have hpBf : IsNilpotent ((p : ℕ) : Rigidified.Baway f) := by
    simpa only [map_natCast] using hB.map (Rigidified.awayHom f)
  have hpK : IsNilpotent ((p : ℕ) : K) := by
    simpa only [map_natCast] using hB.map g
  have hpK1 : IsNilpotent ((p : ℕ) : Rigidified.Baway (1 : K)) := by
    simpa only [map_natCast] using hpK.map (Rigidified.awayHom (1 : K))

  haveI hNoethBf : IsNoetherianRing (Rigidified.Baway f) := inferInstance
  obtain ⟨q, hqdef⟩ : ∃ q : Rigidified.Baway f →+* Rigidified.Baway f ⧸ nilradical (Rigidified.Baway f),
      q = Ideal.Quotient.mk (nilradical (Rigidified.Baway f)) := ⟨_, rfl⟩
  have hq : Function.Surjective q := by rw [hqdef]; exact Ideal.Quotient.mk_surjective
  have hqker : RingHom.ker q = nilradical (Rigidified.Baway f) := by rw [hqdef]; exact Ideal.mk_ker
  have hqI : IsNilpotent (RingHom.ker q) := by
    rw [hqker]; exact IsNoetherianRing.isNilpotent_nilradical _
  haveI hRedS : IsReduced (Rigidified.Baway f ⧸ nilradical (Rigidified.Baway f)) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  have hpS0 : ((p : ℕ) : Rigidified.Baway f ⧸ nilradical (Rigidified.Baway f)) = 0 := by
    rw [← map_natCast q, ← RingHom.mem_ker, hqker]
    exact mem_nilradical.mpr hpBf
  have hpS : IsNilpotent ((p : ℕ) : Rigidified.Baway f ⧸ nilradical (Rigidified.Baway f)) := ⟨1, by rw [pow_one, hpS0]⟩

  have hcS : t.IsGradedS ι ψ (q.comp (Rigidified.awayHom f)) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpS _
  have hXS : (t.XS (Rigidified.awayHom f)).F.map q = (t.XS (q.comp (Rigidified.awayHom f))).F := by
    show (t.X.F.map (Rigidified.awayHom f)).map q = t.X.F.map (q.comp (Rigidified.awayHom f))
    rw [MvFormalGroup.map_map_ringHom]
  have hXm_q : (t.XS (Rigidified.awayHom f)).map q = t.XS (q.comp (Rigidified.awayHom f)) := by
    rw [Rigidified.XS, Rigidified.XS, FormalODModule.map_map]
  have hj_q : q.comp (Rigidified.jS ι ψ (Rigidified.awayHom f)) = Rigidified.jS ι ψ (q.comp (Rigidified.awayHom f)) := rfl

  obtain ⟨Sl, _, jl, φl, _, _, Dl, _, fl, hfl, Ll, _, _⟩ := hL.exists_lift
  obtain ⟨γl, _, hγf⟩ := hfl.2.2.2.2.2
  have hγ : (t.XS (Rigidified.awayHom f)).IsHomogeneousVBasis (Rigidified.jS ι ψ (Rigidified.awayHom f)) (fun k => fl (γl k)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData p _ _ hc _ hγf
  have hD := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ hc).2
  have hbca_q : IsBaseChangeAlong' q ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc)
      ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData (Rigidified.jS ι ψ (q.comp (Rigidified.awayHom f))) hcS)
      (MvFormalGroup.CartierModule.baseChangeEq _ hXS) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc _ hXm_q _ hj_q hcS hXS
  have hγS := isHomogeneousVBasis_push q (t.XS (Rigidified.awayHom f)) (t.XS (q.comp (Rigidified.awayHom f))) hc hcS hXS _ hγ hbca_q
  have hDS := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγS hcS).2
  obtain ⟨LS, hLS⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
    (Rigidified.jS ι ψ (q.comp (Rigidified.awayHom f))) (isHausdorff_of_isNilpotent hpS) _ _ hγS hcS
  have hLL_q := natL_of_eq _ _ hpBf hpS _ hD _ hj_q _ hDS _ hbca_q L hL LS hLS

  have hzS := nMap_mem_etaPiece _ _ _ hbca_q.2.2.1 hbca_q.2.2.2.1 hbca_q.2.2.2.2.1 L hL.isCartierLMap.map_verschiebung
    LS hLS.isCartierLMap.map_verschiebung hLL_q i z hz

  have hglift : (IsLocalization.Away.lift f (g := g) hgf : Rigidified.Baway f →+* K).comp (Rigidified.awayHom f) = g :=
    IsLocalization.Away.lift_comp _ _
  have hle : nilradical (Rigidified.Baway f) ≤ RingHom.ker (IsLocalization.Away.lift f (g := g) hgf : Rigidified.Baway f →+* K) := by
    haveI := RingHom.ker_isPrime (IsLocalization.Away.lift f (g := g) hgf : Rigidified.Baway f →+* K)
    exact nilradical_le_prime _
  obtain ⟨k, hkq⟩ : ∃ k : Rigidified.Baway f ⧸ nilradical (Rigidified.Baway f) →+* K,
      k.comp q = (IsLocalization.Away.lift f (g := g) hgf : Rigidified.Baway f →+* K) := by
    refine ⟨Ideal.Quotient.lift _ (IsLocalization.Away.lift f (g := g) hgf) (fun a ha => hle ha), ?_⟩
    rw [hqdef]; exact Ideal.Quotient.lift_comp_mk _ _ _
  have hkqa : k.comp (q.comp (Rigidified.awayHom f)) = g := by
    rw [← RingHom.comp_assoc, hkq, hglift]

  obtain ⟨xS, hxSdef⟩ : ∃ xS : PrimeSpectrum (Rigidified.Baway f ⧸ nilradical (Rigidified.Baway f)), xS.asIdeal = RingHom.ker k :=
    ⟨⟨RingHom.ker k, RingHom.ker_isPrime k⟩, rfl⟩
  have hk : RingHom.ker k = xS.asIdeal := hxSdef.symm
  have hxS : Ideal.comap (q.comp (Rigidified.awayHom f)) xS.asIdeal = x.asIdeal := by
    rw [hxSdef, RingHom.comap_ker, hkqa, hx]

  have hc'' : t.IsGradedS ι ψ (k.comp (q.comp (Rigidified.awayHom f))) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpK _
  have hXk : (t.XS (q.comp (Rigidified.awayHom f))).F.map k = (t.XS (k.comp (q.comp (Rigidified.awayHom f)))).F := by
    show (t.X.F.map (q.comp (Rigidified.awayHom f))).map k = t.X.F.map (k.comp (q.comp (Rigidified.awayHom f)))
    rw [MvFormalGroup.map_map_ringHom]
  have hXm_k : (t.XS (q.comp (Rigidified.awayHom f))).map k = t.XS (k.comp (q.comp (Rigidified.awayHom f))) := by
    rw [Rigidified.XS, Rigidified.XS, FormalODModule.map_map]
  have hj_k : k.comp (Rigidified.jS ι ψ (q.comp (Rigidified.awayHom f))) = Rigidified.jS ι ψ (k.comp (q.comp (Rigidified.awayHom f))) := rfl
  have hbca_k : IsBaseChangeAlong' k ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData (Rigidified.jS ι ψ (q.comp (Rigidified.awayHom f))) hcS)
      ((t.XS (k.comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ (k.comp (q.comp (Rigidified.awayHom f)))) hc'')
      (MvFormalGroup.CartierModule.baseChangeEq _ hXk) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγS hcS _ hXm_k _ hj_k hc'' hXk
  have hγK := isHomogeneousVBasis_push k (t.XS (q.comp (Rigidified.awayHom f))) (t.XS (k.comp (q.comp (Rigidified.awayHom f)))) hcS hc'' hXk _ hγS hbca_k
  have hDK := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγK hc'').2
  obtain ⟨L'', hL''⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
    (Rigidified.jS ι ψ (k.comp (q.comp (Rigidified.awayHom f)))) (isHausdorff_of_isNilpotent hpK) _ _ hγK hc''
  have hLL_k := natL_of_eq _ _ hpS hpK _ hDS _ hj_k _ hDK _ hbca_k LS hLS L'' hL''

  obtain ⟨e, he⟩ : ∃ e : Rigidified.Baway (1 : K) →+* K, e.comp (Rigidified.awayHom (1 : K)) = RingHom.id K :=
    ⟨IsLocalization.Away.lift (1 : K) (g := RingHom.id K) isUnit_one, IsLocalization.Away.lift_comp _ _⟩
  have he_apply : ∀ y : K, e (Rigidified.awayHom (1 : K) y) = y := fun y => RingHom.congr_fun he y

  have hcompK : e.comp ((algebraMap K (Rigidified.Baway (1 : K))).comp (IsLocalization.Away.lift f (g := g) hgf : Rigidified.Baway f →+* K)) = k.comp q := by
    rw [← RingHom.comp_assoc, show (algebraMap K (Rigidified.Baway (1 : K))) = Rigidified.awayHom (1 : K) from rfl, he,
      RingHom.id_comp, hkq]
  have hge : (e.comp (Rigidified.awayHom (1 : K))).comp g = k.comp (q.comp (Rigidified.awayHom f)) := by
    rw [he, RingHom.id_comp, hkqa]
  have hXe : ((t.map g).XS (Rigidified.awayHom (1 : K))).F.map e = (t.XS (k.comp (q.comp (Rigidified.awayHom f)))).F := by
    show ((t.X.F.map g).map (Rigidified.awayHom (1 : K))).map e = t.X.F.map (k.comp (q.comp (Rigidified.awayHom f)))
    rw [MvFormalGroup.map_map_ringHom, MvFormalGroup.map_map_ringHom, hge]
  have hXm_e : ((t.map g).XS (Rigidified.awayHom (1 : K))).map e = t.XS (k.comp (q.comp (Rigidified.awayHom f))) := by
    rw [Rigidified.XS, Rigidified.XS, Rigidified.map_X, FormalODModule.map_map, FormalODModule.map_map, hge]
  have hj_e : e.comp (Rigidified.jS ι (g.comp ψ) (Rigidified.awayHom (1 : K))) = Rigidified.jS ι ψ (k.comp (q.comp (Rigidified.awayHom f))) := by
    show e.comp ((Rigidified.awayHom (1 : K)).comp ((g.comp ψ).comp ι)) = (k.comp (q.comp (Rigidified.awayHom f))).comp (ψ.comp ι)
    rw [← hge]; rfl

  obtain ⟨Sl', _, jl', φl', _, _, Dl', _, fl', hfl', Ll', _, _⟩ := hL'.exists_lift
  obtain ⟨γl', _, hγf'⟩ := hfl'.2.2.2.2.2
  have hγ' : ((t.map g).XS (Rigidified.awayHom (1 : K))).IsHomogeneousVBasis (Rigidified.jS ι (g.comp ψ) (Rigidified.awayHom (1 : K))) (fun k => fl' (γl' k)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData p _ _ hc' _ hγf'
  have hD' := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ' hc').2
  have hbca_e : IsBaseChangeAlong' e (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι (g.comp ψ) (Rigidified.awayHom (1 : K))) hc')
      ((t.XS (k.comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ (k.comp (q.comp (Rigidified.awayHom f)))) hc'')
      (MvFormalGroup.CartierModule.baseChangeEq e hXe) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ' hc' _ hXm_e _ hj_e hc'' hXe
  have hLL_e := natL_of_eq _ _ hpK1 hpK _ hD' _ hj_e _ hDK _ hbca_e L' hL' L'' hL''

  obtain ⟨y, hy, hNz⟩ := hdiv
  have hy'' := nMap_mem_etaPiece _ _ _ hbca_e.2.2.1 hbca_e.2.2.2.1 hbca_e.2.2.2.2.1 L' hL'.isCartierLMap.map_verschiebung
    L'' hL''.isCartierLMap.map_verschiebung hLL_e i y hy

  have hsq : ∀ m : MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom f)).F,
      MvFormalGroup.CartierModule.baseChangeEq e hXe (MvFormalGroup.CartierModule.baseChangeEq _ hXh m) =
      MvFormalGroup.CartierModule.baseChangeEq k hXk (MvFormalGroup.CartierModule.baseChangeEq q hXS m) := by
    intro m
    apply MvFormalGroup.CartierModule.ext
    funext n
    show MvPowerSeries.map e (MvPowerSeries.map _ (m.toPowerSeries n)) = MvPowerSeries.map k (MvPowerSeries.map q (m.toPowerSeries n))
    rw [MvPowerSeries.map_map, MvPowerSeries.map_map, hcompK]
  have hkV : ∀ m, ((MvFormalGroup.CartierModule.baseChangeEq k hXk).comp (MvFormalGroup.CartierModule.baseChangeEq q hXS))
      (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).verschiebung m) =
      ((t.XS (k.comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ (k.comp (q.comp (Rigidified.awayHom f)))) hc'').verschiebung
      (((MvFormalGroup.CartierModule.baseChangeEq k hXk).comp (MvFormalGroup.CartierModule.baseChangeEq q hXS)) m) := fun m =>
    (congrArg (MvFormalGroup.CartierModule.baseChangeEq k hXk) (hbca_q.2.2.1 m)).trans (hbca_k.2.2.1 _)
  have hkP : ∀ m, ((MvFormalGroup.CartierModule.baseChangeEq k hXk).comp (MvFormalGroup.CartierModule.baseChangeEq q hXS))
      (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).varpi m) =
      ((t.XS (k.comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ (k.comp (q.comp (Rigidified.awayHom f)))) hc'').varpi
      (((MvFormalGroup.CartierModule.baseChangeEq k hXk).comp (MvFormalGroup.CartierModule.baseChangeEq q hXS)) m) := fun m =>
    (congrArg (MvFormalGroup.CartierModule.baseChangeEq k hXk) (hbca_q.2.2.2.1 m)).trans (hbca_k.2.2.2.1 _)
  have hNz' : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).nMap
      (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι (g.comp ψ) (Rigidified.awayHom (1 : K))) hc')
      (MvFormalGroup.CartierModule.baseChangeEq _ hXh) hbcV hbcPi z = p • y := hNz
  have e1 := nMap_nMap_eq ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc)
      (((t.map g).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι (g.comp ψ) (Rigidified.awayHom (1 : K))) hc')
      ((t.XS (k.comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ (k.comp (q.comp (Rigidified.awayHom f)))) hc'')
      (MvFormalGroup.CartierModule.baseChangeEq _ hXh) hbcV hbcPi
      (MvFormalGroup.CartierModule.baseChangeEq e hXe) hbca_e.2.2.1 hbca_e.2.2.2.1
      ((MvFormalGroup.CartierModule.baseChangeEq k hXk).comp (MvFormalGroup.CartierModule.baseChangeEq q hXS)) hkV hkP hsq z
  have e2 := nMap_nMap_eq ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc)
      ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData (Rigidified.jS ι ψ (q.comp (Rigidified.awayHom f))) hcS)
      ((t.XS (k.comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData (Rigidified.jS ι ψ (k.comp (q.comp (Rigidified.awayHom f)))) hc'')
      (MvFormalGroup.CartierModule.baseChangeEq q hXS) hbca_q.2.2.1 hbca_q.2.2.2.1
      (MvFormalGroup.CartierModule.baseChangeEq k hXk) hbca_k.2.2.1 hbca_k.2.2.2.1
      ((MvFormalGroup.CartierModule.baseChangeEq k hXk).comp (MvFormalGroup.CartierModule.baseChangeEq q hXS)) hkV hkP (fun _ => rfl) z
  have hdiv'' : ∃ y'' ∈ ((t.XS (k.comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc'').etaPiece L'' hL''.isCartierLMap.map_verschiebung i,
      ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).nMap ((t.XS (k.comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc'')
        (MvFormalGroup.CartierModule.baseChangeEq _ hXk) hbca_k.2.2.1 hbca_k.2.2.2.1
        (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).nMap ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS)
          (MvFormalGroup.CartierModule.baseChangeEq _ hXS) hbca_q.2.2.1 hbca_q.2.2.2.1 z) = p • y'' := by
    refine ⟨_, hy'', ?_⟩
    rw [e2, ← e1, hNz', map_nsmul]

  obtain ⟨f₀', hf₀', hc₀', L₀', hL₀', hXr', hrV', hrPi', z₀', hz₀', hdiv₀'⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced p ι Φ ψ hB t ht
      (q.comp (Rigidified.awayHom f)) hpS0 hcS LS hLS i _ hzS xS k hk hc'' L'' hL'' hXk hbca_k.2.2.1 hbca_k.2.2.2.1 hdiv''

  exact CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_exists_smul_eq_nMap_nMap_of_surjective_of_isNilpotent_ker
    p ι Φ ψ hB t i f hc L hL z hz x q hq hqI hcS LS hLS hXS hbca_q.2.2.1 hbca_q.2.2.2.1 xS hxS
    ⟨f₀', hf₀', hc₀', L₀', hL₀', hXr', hrV', hrPi', z₀', hz₀', hdiv₀'⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isAlgClosed_of_ker_eq
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isAlgClosed_of_ker_eq (solution)
