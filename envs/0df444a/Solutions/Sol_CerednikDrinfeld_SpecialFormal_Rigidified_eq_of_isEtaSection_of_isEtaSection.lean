-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.eq_of_isEtaSection_of_isEtaSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/a3768f50-1474-53c4-94cd-3a74c82152e6

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
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_map_varpi
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_nMap_bijOn_eta_of_eq_baseChangeEq_mk
import Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_nsmul_eq_zero_of_mem_eta
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_eq_of_latticeRel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_eq_of_isEtaSection_of_isEtaSection
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

namespace B4Asm

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

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

omit [Fact (Nat.Prime p)] in
theorem isHausdorff_of_isNilpotent {S : Type} [CommRing S] (hS : IsNilpotent ((p : ℕ) : S)) :
    IsHausdorff (Ideal.span {((p : ℕ) : S)}) S := by
  obtain ⟨N, hN⟩ := hS
  refine ⟨fun x hx => ?_⟩
  have := hx N
  rwa [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_smul, SModEq.bot] at this

section Datum

variable {B : Type} [CommRing B] {j : Zp2 p →+* B}

theorem nVarpi_nMk (D : GradedCartierModuleData p B j) (m m' : D.M) :
    D.nVarpi (D.nMk (m, m')) = D.nMk (D.varpi m, D.varpi m') := rfl

theorem nsmul_nMk (D : GradedCartierModuleData p B j) (k : ℕ) (m m' : D.M) :
    k • D.nMk (m, m') = D.nMk (k • m, k • m') := by
  rw [← map_nsmul]; rfl

theorem nVarpi_nVarpi (D : GradedCartierModuleData p B j) (z : D.NMod) :
    D.nVarpi (D.nVarpi z) = (p : ℕ) • z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [nVarpi_nMk, nVarpi_nMk, D.varpi_varpi, D.varpi_varpi, nsmul_nMk]

theorem nVarpi_mem_eta (D : GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L) (z : D.NMod)
    (hz : z ∈ D.eta L hL.isCartierLMap.map_verschiebung) :
    D.nVarpi z ∈ D.eta L hL.isCartierLMap.map_verschiebung := by
  obtain ⟨⟨a, b⟩, rfl⟩ := D.nMk_surjective z
  rw [mem_eta_iff] at hz ⊢
  rw [nVarpi_nMk, phi_nMk,
    CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.map_varpi p j D hD L hL a]
  have h0 : D.nMk (D.varpi b, 0) = D.nVarpi (D.nMk (b, 0)) := by rw [nVarpi_nMk, map_zero]
  rw [h0, ← map_add, ← phi_nMk D L hL.isCartierLMap.map_verschiebung a b, hz, nVarpi_nMk]

theorem nVarpi_pow_mem_eta (D : GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L) (n : ℕ) (z : D.NMod)
    (hz : z ∈ D.eta L hL.isCartierLMap.map_verschiebung) :
    ((D.nVarpi : D.NMod →ₗ[WittVector p B] D.NMod) ^ n) z ∈ D.eta L hL.isCartierLMap.map_verschiebung := by
  induction n with
  | zero => simpa using hz
  | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact nVarpi_mem_eta D hD L hL _ ih

end Datum

end B4Asm

set_option maxHeartbeats 3200000 in
set_option linter.unusedSectionVars false in
open B4Asm CerednikDrinfeld.GradedCartierModuleData in
theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
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
    {B : Type} [CommRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    {S : Type} [CommRing S] [IsNoetherianRing S] (g : B →+* S) (hS : IsNilpotent (p : S))
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (L : _) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (i : Fin 2) (v : Fin 2 → ℚ_[p])
    (z z' : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod)
    (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 g hc hcb hcΦg L hL i z v)
    (hz' : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 g hc hcb hcΦg L hL i z' v) :
    z = z' := by
  classical
  letI : Algebra ℤ_[p] S := (g.comp (algebraMap ℤ_[p] B)).toAlgebra

  have hq : (reduceMap (p := p) g).comp (Ideal.Quotient.mk (pIdeal p B)) =
      (Ideal.Quotient.mk (pIdeal p S)).comp g := RingHom.ext fun _ => rfl
  have hpq : IsNilpotent ((p : ℕ) : S ⧸ pIdeal p S) :=
    ⟨1, by rw [pow_one]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))⟩

  obtain ⟨Sl, _, jl, φl, _, _, Dl, _, fl, hfl, Ll, _, _⟩ := hL.exists_lift
  obtain ⟨γl, _, hγf⟩ := hfl.2.2.2.2.2
  have hγ : (t.XS g).IsHomogeneousVBasis (Rigidified.jS ι ψ g) (fun i => fl (γl i)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData p _ _ hc _ hγf
  have hD : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsSpecialCartierModule :=
    (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ hc).2

  have hXb : (t.XS g).map (Ideal.Quotient.mk (pIdeal p S)) = t.XbarS g := by
    show (t.X.map g).map _ = (t.X.map _).map _
    rw [FormalODModule.map_map, FormalODModule.map_map, hq]
  have hjb : (Ideal.Quotient.mk (pIdeal p S)).comp (Rigidified.jS ι ψ g) = Rigidified.jSbar ι ψ g := by
    show (Ideal.Quotient.mk (pIdeal p S)).comp (g.comp _) = (reduceMap g).comp ((Ideal.Quotient.mk (pIdeal p B)).comp _)
    rw [← RingHom.comp_assoc, ← hq, RingHom.comp_assoc]
  have hbca : IsBaseChangeAlong' (Ideal.Quotient.mk (pIdeal p S))
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc)
      ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc _ hXb _ hjb hcb (t.XS_F_map_mk g)
  have hγb : (t.XbarS g).IsHomogeneousVBasis (Rigidified.jSbar ι ψ g) (fun i => t.redC g (fl (γl i))) := by
    refine ⟨fun i => ?_, isUnit_det_tangent_baseChangeEq _ (t.XS_F_map_mk g) _ hγ.2⟩
    exact (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hcb i _).mp
      (hbca.2.2.2.2.1 i _ ((FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hc i _).mpr (hγ.1 i)))
  have hDb : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).IsSpecialCartierModule :=
    (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγb hcb).2
  obtain ⟨Lb, hLb⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
      (Rigidified.jSbar ι ψ g) (isHausdorff_of_isNilpotent hpq) _ _ hγb hcb
  have hLL : ∀ y, Lb (t.redC g y) =
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap
        ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g)
        (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) (L y) :=
    natL_of_eq _ _ hS hpq _ hD _ hjb _ hDb (t.redC g) hbca L hL Lb hLb
  have hinj := (CerednikDrinfeld.FormalODModule.nMap_bijOn_eta_of_eq_baseChangeEq_mk p hS (Rigidified.jS ι ψ g)
    (t.XS g) _ hγ hc (t.XbarS g) hXb (Rigidified.jSbar ι ψ g) hjb hcb (t.XS_F_map_mk g) (t.redC g) rfl
    (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) L hL Lb hLb hLL).injOn

  unfold Rigidified.IsEtaSection at hz hz'
  obtain ⟨hzeta, hrel⟩ := hz
  obtain ⟨hzeta', hrel'⟩ := hz'
  obtain ⟨N, hN⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_of_latticeRel p _ _ _ _ _ _ hrel hrel'

  have hzη : z ∈ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).eta L hL.isCartierLMap.map_verschiebung :=
    (AddSubgroup.mem_inf.mp hzeta).1
  have hzη' : z' ∈ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).eta L hL.isCartierLMap.map_verschiebung :=
    (AddSubgroup.mem_inf.mp hzeta').1
  set Pz := ((((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nVarpi :
      _ →ₗ[WittVector p S] _) ^ (i : ℕ)) z with hPz
  set Pz' := ((((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nVarpi :
      _ →ₗ[WittVector p S] _) ^ (i : ℕ)) z' with hPz'
  have hPzη : Pz ∈ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).eta L hL.isCartierLMap.map_verschiebung :=
    nVarpi_pow_mem_eta _ hD L hL _ z hzη
  have hPzη' : Pz' ∈ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).eta L hL.isCartierLMap.map_verschiebung :=
    nVarpi_pow_mem_eta _ hD L hL _ z' hzη'
  have hPN : p ^ N • Pz = p ^ N • Pz' := by
    apply hinj (AddSubgroup.nsmul_mem _ hPzη _) (AddSubgroup.nsmul_mem _ hPzη' _)
    simp only [Rigidified.etaRed] at hN
    rw [map_nsmul, map_nsmul]
    exact hN

  have hkill : ∀ (k : ℕ) (ζ : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod),
      ζ ∈ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).eta L hL.isCartierLMap.map_verschiebung →
      p ^ k • ζ = 0 → ζ = 0 := by
    intro k
    induction k with
    | zero => intro ζ _ h; simpa using h
    | succ k ih =>
      intro ζ hζ h
      refine ih ζ hζ (CerednikDrinfeld.FormalODModule.eq_zero_of_nsmul_eq_zero_of_mem_eta p hS
        (Rigidified.jS ι ψ g) (t.XS g) _ hγ hc L hL _ (AddSubgroup.nsmul_mem _ hζ _) ?_)
      rw [smul_smul, ← pow_succ', h]
  have hP : Pz = Pz' := by
    have h0 : p ^ N • (Pz - Pz') = 0 := by rw [nsmul_sub, hPN, sub_self]
    exact sub_eq_zero.mp (hkill N _ (AddSubgroup.sub_mem _ hPzη hPzη') h0)
  rw [hPz, hPz'] at hP
  fin_cases i
  · simpa using hP
  · have h2 : (p : ℕ) • z = (p : ℕ) • z' := by
      rw [← nVarpi_nVarpi, ← nVarpi_nVarpi]
      simp only [pow_one] at hP
      rw [hP]
    have h3 : (p : ℕ) ^ 1 • (z - z') = 0 := by rw [pow_one, nsmul_sub, h2, sub_self]
    exact sub_eq_zero.mp (hkill 1 _ (AddSubgroup.sub_mem _ hzη hzη') h3)

end S_CerednikDrinfeld_SpecialFormal_Rigidified_eq_of_isEtaSection_of_isEtaSection
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_eq_of_isEtaSection_of_isEtaSection (solution)
