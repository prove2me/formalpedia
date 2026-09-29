-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_mem_etaPiece_tangent_eq_of_line_transport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/2d078b68-4d20-540f-833d-af99dc15ea8d

import Theorems.Thm_CerednikDrinfeld_FormalODModule_nMap_bijOn_etaPiece_of_eq_baseChangeEq_of_surjective_of_mul_eq_zero
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_coordinates_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_eq_of_isEtaSection_of_isEtaSection
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_mem_iff_exists_isEtaSection_zero_awayHom_one_of_isAlgClosed_wittVector
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_eq_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_of_free_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_tangent_eq_of_mkQ_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isCartierQuadruple_of_isAdmissible_of_lieVarpi_eq_zero_wittVector
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isBaseChangeAlong
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_mem_etaPiece_tangent_eq_of_line_transport
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open scoped TensorProduct

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData

namespace LineTransport

section NMod
variable {p : ℕ} [Fact p.Prime]

theorem mkQ_map_eq_u_nMap {B B' : Type} [CommRing B] [CommRing B'] {j : CerednikDrinfeld.Zp2 p →+* B} {j' : CerednikDrinfeld.Zp2 p →+* B'}
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (D' : CerednikDrinfeld.GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L) (L' : D'.M →+ D'.NMod) (hL' : D'.IsCanonicalLMap L')
    (i : Fin 2) (z : D.NMod) (hz : z ∈ D.etaPiece L hL.isCartierLMap.map_verschiebung i)
    (hz' : D.nMap D' f hV hPi z ∈ D'.etaPiece L' hL'.isCartierLMap.map_verschiebung i)
    (m : D.M) (hm : D.vRange.mkQ m = D.u L hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz).1⟩) :
    D'.vRange.mkQ (f m) = D'.u L' hL'.isCartierLMap.map_verschiebung ⟨D.nMap D' f hV hPi z, (AddSubgroup.mem_inf.mp hz').1⟩ := by
  obtain ⟨⟨a, b⟩, hab⟩ := D.nMk_surjective z
  subst hab
  change D.vRange.mkQ m = D.vRange.mkQ a at hm
  change D'.vRange.mkQ (f m) = D'.vRange.mkQ (f a)
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hm ⊢
  obtain ⟨y, hy⟩ := (D.mem_vRange_iff _).mp hm
  exact (D'.mem_vRange_iff _).mpr ⟨f y, by rw [← hV, hy, map_sub]⟩

theorem nMap_nMap {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    {j : CerednikDrinfeld.Zp2 p →+* B} {j' : CerednikDrinfeld.Zp2 p →+* B'} {j'' : CerednikDrinfeld.Zp2 p →+* B''}
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (D' : CerednikDrinfeld.GradedCartierModuleData p B' j')
    (D'' : CerednikDrinfeld.GradedCartierModuleData p B'' j'')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x)) (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    (g : D'.M →+ D''.M) (hV' : ∀ x, g (D'.verschiebung x) = D''.verschiebung (g x)) (hPi' : ∀ x, g (D'.varpi x) = D''.varpi (g x))
    (h : D.M →+ D''.M) (hV'' : ∀ x, h (D.verschiebung x) = D''.verschiebung (h x)) (hPi'' : ∀ x, h (D.varpi x) = D''.varpi (h x))
    (hgf : ∀ x, g (f x) = h x) (z : D.NMod) :
    D'.nMap D'' g hV' hPi' (D.nMap D' f hV hPi z) = D.nMap D'' h hV'' hPi'' z := by
  obtain ⟨⟨a, b⟩, rfl⟩ := D.nMk_surjective z
  rw [nMap_nMk, nMap_nMk, nMap_nMk, hgf, hgf]

end NMod

section Local

theorem isUnit_of_fst_ne_zero {κ : Type} [Field κ] (s : DualNumber κ) (hs : TrivSqZeroExt.fst s ≠ 0) : IsUnit s :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hs)

theorem linearMap_pi_apply_eq_sum (R : Type*) [CommSemiring R] {n : ℕ} (Λ : (Fin n → R) →ₗ[R] (Fin n → R))
    (w : Fin n → R) (j : Fin n) : Λ w j = ∑ l : Fin n, Λ (Pi.single l 1) j * w l := by
  classical
  have hs : ∀ l : Fin n, (fun j' : Fin n => if l = j' then (1 : R) else 0) = Pi.single l 1 := by
    intro l; funext j'
    by_cases h : l = j'
    · subst h; simp
    · simp [Pi.single_apply, h, Ne.symm h]
  rw [LinearMap.pi_apply_eq_sum_univ Λ w, Finset.sum_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [Pi.smul_apply, smul_eq_mul, mul_comm, hs l]

theorem bijective_algebraMap_of_le_isUnit (R : Type*) [CommRing R] (S : Submonoid R) (hS : S ≤ IsUnit.submonoid R)
    (L : Type*) [CommRing L] [Algebra R L] [IsLocalization S L] : Function.Bijective (algebraMap R L) := by
  let e : R ≃ₐ[R] L := IsLocalization.atUnits R S hS
  have he : (algebraMap R L : R → L) = e := funext fun x => by simpa using (e.commutes x).symm
  rw [he]; exact e.bijective

theorem bijective_algebraMap_away_of_isUnit (R : Type*) [CommRing R] (f : R) (hf : IsUnit f) :
    Function.Bijective (algebraMap R (Localization.Away f)) :=
  bijective_algebraMap_of_le_isUnit R (Submonoid.powers f)
    (by rintro x ⟨n, rfl⟩; exact hf.pow n) (Localization.Away f)

theorem bijective_algebraMap_atPrime_of_forall_isUnit (R : Type*) [CommRing R] (x : PrimeSpectrum R)
    (h : ∀ s : R, s ∉ x.asIdeal → IsUnit s) :
    Function.Bijective (algebraMap R (Localization.AtPrime x.asIdeal)) :=
  bijective_algebraMap_of_le_isUnit R x.asIdeal.primeCompl (fun s hs => h s hs) (Localization.AtPrime x.asIdeal)

theorem injective_algebraMap_atPrime_of_forall_isUnit (R : Type*) [CommRing R] (x : PrimeSpectrum R)
    (h : ∀ s : R, s ∉ x.asIdeal → IsUnit s) :
    Function.Injective (algebraMap R (Localization.AtPrime x.asIdeal)) :=
  (bijective_algebraMap_atPrime_of_forall_isUnit R x h).1

theorem free_of_invertible_of_isLocalRing (R : Type*) [CommRing R] [IsLocalRing R] (M : Type*) [AddCommGroup M]
    [Module R M] [Module.Invertible R M] : Module.Free R M :=
  Module.free_of_flat_of_isLocalRing

end Local

end LineTransport

open LineTransport in
set_option maxHeartbeats 12800000 in
theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0 : ∀ m ∈ Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι), Φ.lieVarpi m = 0)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    (κ : Type) [Field κ] [IsAlgClosed κ] [Algebra ℤ_[p] κ]
    (ψR : WittVector p k →+* DualNumber κ) (hR : IsNilpotent (p : DualNumber κ))
    (t t' : Rigidified p Φ (DualNumber κ)) (ht : t.IsAdmissible ι ψR) (ht' : t'.IsAdmissible ι ψR)
    (Q Q' : FormalOmega.DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) (DualNumber κ))
    (σ₀ : Q.T₀ ≃ₗ[DualNumber κ] ↥(t.X.lieZero (structureMap ι ψR)))
    (σ₁ : Q.T₁ ≃ₗ[DualNumber κ] ↥(t.X.lieOne (structureMap ι ψR)))
    (hQ : t.IsCartierQuadrupleVia ι hcΦ rΦ ψR Q σ₀ σ₁)
    (σ₀' : Q'.T₀ ≃ₗ[DualNumber κ] ↥(t'.X.lieZero (structureMap ι ψR)))
    (σ₁' : Q'.T₁ ≃ₗ[DualNumber κ] ↥(t'.X.lieOne (structureMap ι ψR)))
    (hQ' : t'.IsCartierQuadrupleVia ι hcΦ rΦ ψR Q' σ₀' σ₁')
    (Λ : t.X.Lie ≃ₗ[DualNumber κ] t'.X.Lie)
    (ψκ : WittVector p k →+* κ) (hresψ : (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).comp ψR = ψκ)

    (hsmooth : ¬ ((∀ w ∈ (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X.lieZero (structureMap ι ψκ), (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X.lieVarpi w = 0) ∧
        (∀ w ∈ (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X.lieOne (structureMap ι ψκ), (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X.lieVarpi w = 0)))

    (u₀ v₀ : Series κ) (m : ℕ)
    (hu₀ : FormalODModule.IsODHom (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X u₀) (hv₀ : FormalODModule.IsODHom (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X v₀)
    (hvu : v₀.comp u₀ = Series.id κ) (huv : u₀.comp v₀ = Series.id κ)
    (hρ : ((t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).Xbar.act ((p : Zp2 p) ^ (m + (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).n))).comp ((u₀.map (Ideal.Quotient.mk (pIdeal p κ))).comp (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).ρ)
      = ((t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).Xbar.act ((p : Zp2 p) ^ (m + (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).n))).comp (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).ρ)

    (hΛ0 : Submodule.map Λ.toLinearMap (t.X.lieZero (structureMap ι ψR)) = t'.X.lieZero (structureMap ι ψR))
    (hΛ1 : Submodule.map Λ.toLinearMap (t.X.lieOne (structureMap ι ψR)) = t'.X.lieOne (structureMap ι ψR))
    (hΛPi : ∀ w : t.X.Lie, Λ (t.X.lieVarpi w) = t'.X.lieVarpi (Λ w))
    (hΛred : ∀ (w : t.X.Lie) (i : Fin 2), TrivSqZeroExt.fst (Λ w i) =
      (Matrix.mulVecLin (MvFormalGroup.linearPart u₀) (fun j => TrivSqZeroExt.fst (w j))) i)

    (hN : ∀ x, Q.N₀ x = Q'.N₀ x ∧ Q.N₁ x = Q'.N₁ x)
    (hline : ∀ (x : PrimeSpectrum (DualNumber κ)) (i : Fin 2) (v : Fin 2 → ℚ_[p])
        (f : DualNumber κ) (hf : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψR (Rigidified.awayHom f))
        (hcb : t.IsGradedSbar ι ψR (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψR (Rigidified.awayHom f))
        (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hc).IsCanonicalLMap L)
        (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψR ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL i z v)
        (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hc).M)
        (hm : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hc).vRange.mkQ m =
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hc).u L hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩)
        (f' : DualNumber κ) (hf' : f' ∉ x.asIdeal) (hc' : t'.IsGradedS ι ψR (Rigidified.awayHom f'))
        (hcb' : t'.IsGradedSbar ι ψR (Rigidified.awayHom f')) (hcΦf' : Rigidified.IsGradedPhiS (Φ := Φ) ι ψR (Rigidified.awayHom f'))
        (L' : _) (hL' : ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hc').IsCanonicalLMap L')
        (z' : _) (hz' : t'.IsEtaSection ι hcΦ rΦ ψR ht'.2.2.1 (Rigidified.awayHom f') hc' hcb' hcΦf' L' hL' i z' v)
        (m' : ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hc').M)
        (hm' : ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hc').vRange.mkQ m' =
          ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hc').u L' hL'.isCartierLMap.map_verschiebung ⟨z', (AddSubgroup.mem_inf.mp hz'.1).1⟩),
        ∀ j : Fin 2, Rigidified.awayToLoc x f' hf' (MvFormalGroup.CartierModule.tangent m' j) =
        ∑ l : Fin 2, Rigidified.locHom x (Λ (Pi.single l 1) j) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m l))
    (hc : IsCompl (t.X.gradedPiece (structureMap ι ψR) 0) (t.X.gradedPiece (structureMap ι ψR) 1))
    (hc' : IsCompl (t'.X.gradedPiece (structureMap ι ψR) 0) (t'.X.gradedPiece (structureMap ι ψR) 1))
    (γ : Fin 2 → MvFormalGroup.CartierModule p t.X.F) (hγ : t.X.IsHomogeneousVBasis (structureMap ι ψR) γ)
    (L : (t.X.toGradedCartierModuleData (structureMap ι ψR) hc).M →+ (t.X.toGradedCartierModuleData (structureMap ι ψR) hc).NMod) (hL : (t.X.toGradedCartierModuleData (structureMap ι ψR) hc).IsCanonicalLMap L)
    (L' : (t'.X.toGradedCartierModuleData (structureMap ι ψR) hc').M →+ (t'.X.toGradedCartierModuleData (structureMap ι ψR) hc').NMod) (hL' : (t'.X.toGradedCartierModuleData (structureMap ι ψR) hc').IsCanonicalLMap L')
    (i : Fin 2) :
    ∀ (z : (t.X.toGradedCartierModuleData (structureMap ι ψR) hc).NMod) (hz : z ∈ (t.X.toGradedCartierModuleData (structureMap ι ψR) hc).etaPiece L hL.isCartierLMap.map_verschiebung i)
      (m : MvFormalGroup.CartierModule p t.X.F),
      (t.X.toGradedCartierModuleData (structureMap ι ψR) hc).vRange.mkQ m = (t.X.toGradedCartierModuleData (structureMap ι ψR) hc).u L hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz).1⟩ →
      ∃ (z' : (t'.X.toGradedCartierModuleData (structureMap ι ψR) hc').NMod) (hz' : z' ∈ (t'.X.toGradedCartierModuleData (structureMap ι ψR) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i)
        (m' : MvFormalGroup.CartierModule p t'.X.F),
        (t'.X.toGradedCartierModuleData (structureMap ι ψR) hc').vRange.mkQ m' = (t'.X.toGradedCartierModuleData (structureMap ι ψR) hc').u L' hL'.isCartierLMap.map_verschiebung ⟨z', (AddSubgroup.mem_inf.mp hz').1⟩ ∧
        MvFormalGroup.CartierModule.tangent m' = Λ (MvFormalGroup.CartierModule.tangent m) := by
  classical
  intro z hz m hm

  have hκ : IsNilpotent (p : κ) := by
    obtain ⟨n, hn⟩ := hR
    refine ⟨n, ?_⟩
    have := congrArg (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ) hn
    rwa [map_pow, map_natCast, map_zero] at this
  haveI : CharP κ p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hκ.eq_zero
  have htb : (t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)).IsAdmissible ι ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι ψR (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ) t ht
  have h0' : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi :=
    fun m hm => LinearMap.mem_ker.mpr (h0 m hm)
  obtain ⟨LΦ, hLΦ⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
      p k ι Φ hΦ hcΦ
  obtain ⟨Qb, hQb⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_isCartierQuadruple_of_isAdmissible_of_lieVarpi_eq_zero_wittVector
      p k ι Φ hΦ hΦ4 h0' hcΦ rΦ ⟨LΦ, hLΦ⟩ hrΦ ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) hκ (t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) htb
  obtain ⟨hODb, τb₀, τb₁, hTb0, hTb1, Hb⟩ := hQb

  obtain ⟨hc₁, hcb₁, hcΦ1, L₁, hL₁, -⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_mem_iff_exists_isEtaSection_zero_awayHom_one_of_isAlgClosed_wittVector
      p k ι Φ hΦ hΦ4 h0' hcΦ rΦ ⟨LΦ, hLΦ⟩ hrΦ ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) hκ (t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) htb Qb.N₀ (fun x v => (Hb htb.2.2.1 x).1 v)

  let xb : PrimeSpectrum κ := ⟨⊥, Ideal.bot_prime⟩
  let x : PrimeSpectrum (DualNumber κ) := DrinfeldDatum.pointUnder ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) xb
  have hxunit : ∀ s : DualNumber κ, s ∉ x.asIdeal → IsUnit s := fun s hs =>
    isUnit_of_fst_ne_zero s (fun h => hs (show ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) s ∈ (⊥ : Ideal κ) from (Submodule.mem_bot κ).mpr h))
  have hfunit : ∀ s : DualNumber κ, s ∉ x.asIdeal → IsUnit ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ) s) := fun s hs =>
    isUnit_iff_ne_zero.mpr (fun h => hs (show ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) s ∈ (⊥ : Ideal κ) from (Submodule.mem_bot κ).mpr h))

  have hX' : t.X.map ((Rigidified.awayHom (1 : κ)).comp (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) = (t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)).XS (Rigidified.awayHom (1 : κ)) :=
    (FormalODModule.map_map _ _ t.X).symm
  have hF' : t.X.F.map ((Rigidified.awayHom (1 : κ)).comp (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) = ((t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)).XS (Rigidified.awayHom (1 : κ))).F :=
    (map_map_ringHom t.X.F _ _).symm

  have hsurj₁ : Function.Surjective ((Rigidified.awayHom (1 : κ)).comp (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) :=
    (bijective_algebraMap_away_of_isUnit κ 1 isUnit_one).2.comp (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)
  have hker₁ : ∀ a b : DualNumber κ, ((Rigidified.awayHom (1 : κ)).comp (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) a = 0 → ((Rigidified.awayHom (1 : κ)).comp (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) b = 0 → a * b = 0 := by
    intro a b ha hb
    have hinj := (bijective_algebraMap_away_of_isUnit κ 1 isUnit_one).1
    have ha' : TrivSqZeroExt.fst a = 0 := hinj (by simpa using ha)
    have hb' : TrivSqZeroExt.fst b = 0 := hinj (by simpa using hb)
    ext
    · rw [TrivSqZeroExt.fst_mul, ha', zero_mul, TrivSqZeroExt.fst_zero]
    · rw [TrivSqZeroExt.snd_mul, ha', hb', TrivSqZeroExt.snd_zero]; simp
  obtain ⟨hLL₁, -, hbij₁⟩ :=
    CerednikDrinfeld.FormalODModule.nMap_bijOn_etaPiece_of_eq_baseChangeEq_of_surjective_of_mul_eq_zero
      p hR ((Rigidified.awayHom (1 : κ)).comp (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) hsurj₁ hker₁ (structureMap ι ψR) t.X γ hγ hc
      ((t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)).XS (Rigidified.awayHom (1 : κ))) hX'
      (Rigidified.jS ι ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) (Rigidified.awayHom (1 : κ))) rfl hc₁ hF'
      (baseChangeEq ((Rigidified.awayHom (1 : κ)).comp (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) hF') rfl
      (fun x => baseChangeEq_verschiebungInt _ _ x) (fun x => baseChangeEq_endAct _ _ (fun _ => rfl) x)
      L hL L₁ hL₁
  have hbij := hbij₁ i

  obtain ⟨v, hv⟩ :=
    (CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_coordinates_of_isAlgClosed p k ι Φ hΦ hΦ4 h0' hcΦ rΦ hrΦ
      κ ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) hκ (t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) htb hc₁ hcb₁ hcΦ1 L₁ hL₁ i).1 _ (hbij.1 hz)

  obtain ⟨bcQ⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isBaseChangeAlong
      p ι Φ hΦ hΦ4 hcΦ rΦ hrΦ ψR hR ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) hκ ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) rfl t ht Q
      ((CerednikDrinfeld.SpecialFormal.Rigidified.isCartierQuadruple_iff_exists_via ι hcΦ rΦ ψR t Q).mpr ⟨hQ.1, σ₀, σ₁, hQ⟩)
      Qb ⟨hODb, τb₀, τb₁, hTb0, hTb1, Hb⟩
  have h1xb : (1 : κ) ∉ xb.asIdeal := fun h => one_ne_zero ((Submodule.mem_bot κ).mp h)

  have pres : (∃ (f : DualNumber κ) (_ : f ∉ x.asIdeal) (hcf : t.IsGradedS ι ψR (Rigidified.awayHom f))
        (hcbf : t.IsGradedSbar ι ψR (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψR (Rigidified.awayHom f))
        (Lf : _) (hLf : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hcf).IsCanonicalLMap Lf),
        ∃ zf, t.IsEtaSection ι hcΦ rΦ ψR ht.2.2.1 (Rigidified.awayHom f) hcf hcbf hcΦf Lf hLf i zf v) ∧ (∃ (f : DualNumber κ) (_ : f ∉ x.asIdeal) (hcf : t'.IsGradedS ι ψR (Rigidified.awayHom f))
        (hcbf : t'.IsGradedSbar ι ψR (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψR (Rigidified.awayHom f))
        (Lf : _) (hLf : ((t'.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hcf).IsCanonicalLMap Lf),
        ∃ zf, t'.IsEtaSection ι hcΦ rΦ ψR ht'.2.2.1 (Rigidified.awayHom f) hcf hcbf hcΦf Lf hLf i zf v) := by
    revert hv; revert v; revert hbij; revert hz m; revert z; revert i
    intro i
    fin_cases i <;> intro z hz m hm hbij v hv
    · have h1 : v ∈ Qb.N₀ xb := ((Hb htb.2.2.1 xb).1 v).mpr ⟨1, h1xb, hc₁, hcb₁, hcΦ1, L₁, hL₁, _, hv⟩
      have h2 : v ∈ Q.N₀ x := by rw [← bcQ.N₀_eq xb]; exact h1
      have h3 : v ∈ Q'.N₀ x := by rw [← (hN x).1]; exact h2
      exact ⟨((hQ.2.2.2 ht.2.2.1 x).1 v).mp h2, ((hQ'.2.2.2 ht'.2.2.1 x).1 v).mp h3⟩
    · have h1 : v ∈ Qb.N₁ xb := ((Hb htb.2.2.1 xb).2.1 v).mpr ⟨1, h1xb, hc₁, hcb₁, hcΦ1, L₁, hL₁, _, hv⟩
      have h2 : v ∈ Q.N₁ x := by rw [← bcQ.N₁_eq xb]; exact h1
      have h3 : v ∈ Q'.N₁ x := by rw [← (hN x).2]; exact h2
      exact ⟨((hQ.2.2.2 ht.2.2.1 x).2.1 v).mp h2, ((hQ'.2.2.2 ht'.2.2.1 x).2.1 v).mp h3⟩
  obtain ⟨⟨f, hf, hcf, hcbf, hcΦf, Lf, hLf, zf, hzf⟩, ⟨f', hf', hcf', hcbf', hcΦf', Lf', hLf', zf', hzf'⟩⟩ := pres

  obtain ⟨γ', hγ'⟩ : ∃ γ' : Fin 2 → MvFormalGroup.CartierModule p t'.X.F, t'.X.IsHomogeneousVBasis (structureMap ι ψR) γ' := by
    haveI := ht'.1.2.1
    haveI := ht'.1.2.2
    exact CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_of_isSpecial_of_free_of_isNilpotent p
      (structureMap ι ψR) hR t'.X ht'.1 (free_of_invertible_of_isLocalRing _ _) (free_of_invertible_of_isLocalRing _ _)

  have hbjf := bijective_algebraMap_away_of_isUnit (DualNumber κ) f (hxunit f hf)
  obtain ⟨hLLf, -, hbijEf⟩ :=
    CerednikDrinfeld.FormalODModule.nMap_bijOn_etaPiece_of_eq_baseChangeEq_of_surjective_of_mul_eq_zero
      p hR (Rigidified.awayHom f) hbjf.2
      (fun a b ha _ => by rw [show a = 0 from hbjf.1 (by rw [ha, map_zero]), zero_mul])
      (structureMap ι ψR) t.X γ hγ hc (t.XS (Rigidified.awayHom f)) rfl
      (Rigidified.jS ι ψR (Rigidified.awayHom f)) rfl hcf rfl
      (baseChangeEq (Rigidified.awayHom f) rfl) rfl
      (fun x => baseChangeEq_verschiebungInt _ _ x) (fun x => baseChangeEq_endAct _ _ (fun _ => rfl) x)
      L hL Lf hLf
  obtain ⟨zv, hzv, hzvf⟩ := (hbijEf i).2.2 hzf.1
  subst hzvf
  obtain ⟨mv, hmv⟩ := (t.X.toGradedCartierModuleData (structureMap ι ψR) hc).vRange.mkQ_surjective
    ((t.X.toGradedCartierModuleData (structureMap ι ψR) hc).u L hL.isCartierLMap.map_verschiebung ⟨zv, (AddSubgroup.mem_inf.mp hzv).1⟩)
  have hmf := mkQ_map_eq_u_nMap (t.X.toGradedCartierModuleData (structureMap ι ψR) hc) ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hcf) (baseChangeEq (Rigidified.awayHom f) rfl)
    (fun x => baseChangeEq_verschiebungInt _ _ x) (fun x => baseChangeEq_endAct _ _ (fun _ => rfl) x)
    L hL Lf hLf i zv hzv hzf.1 mv hmv

  have hbjf' := bijective_algebraMap_away_of_isUnit (DualNumber κ) f' (hxunit f' hf')
  obtain ⟨hLLf', -, hbijEf'⟩ :=
    CerednikDrinfeld.FormalODModule.nMap_bijOn_etaPiece_of_eq_baseChangeEq_of_surjective_of_mul_eq_zero
      p hR (Rigidified.awayHom f') hbjf'.2
      (fun a b ha _ => by rw [show a = 0 from hbjf'.1 (by rw [ha, map_zero]), zero_mul])
      (structureMap ι ψR) t'.X γ' hγ' hc' (t'.XS (Rigidified.awayHom f')) rfl
      (Rigidified.jS ι ψR (Rigidified.awayHom f')) rfl hcf' rfl
      (baseChangeEq (Rigidified.awayHom f') rfl) rfl
      (fun x => baseChangeEq_verschiebungInt _ _ x) (fun x => baseChangeEq_endAct _ _ (fun _ => rfl) x)
      L' hL' Lf' hLf'
  obtain ⟨zv', hzv', hzvf'⟩ := (hbijEf' i).2.2 hzf'.1
  subst hzvf'
  obtain ⟨mv', hmv'⟩ := (t'.X.toGradedCartierModuleData (structureMap ι ψR) hc').vRange.mkQ_surjective
    ((t'.X.toGradedCartierModuleData (structureMap ι ψR) hc').u L' hL'.isCartierLMap.map_verschiebung ⟨zv', (AddSubgroup.mem_inf.mp hzv').1⟩)
  have hmf' := mkQ_map_eq_u_nMap (t'.X.toGradedCartierModuleData (structureMap ι ψR) hc') ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hcf') (baseChangeEq (Rigidified.awayHom f') rfl)
    (fun x => baseChangeEq_verschiebungInt _ _ x) (fun x => baseChangeEq_endAct _ _ (fun _ => rfl) x)
    L' hL' Lf' hLf' i zv' hzv' hzf'.1 mv' hmv'

  have hl := hline x i v f hf hcf hcbf hcΦf Lf hLf ((t.X.toGradedCartierModuleData (structureMap ι ψR) hc).nMap ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hcf) (baseChangeEq (Rigidified.awayHom f) rfl) (fun x => baseChangeEq_verschiebungInt _ _ x) (fun x => baseChangeEq_endAct _ _ (fun _ => rfl) x) zv) hzf ((baseChangeEq (Rigidified.awayHom f) rfl : MvFormalGroup.CartierModule p t.X.F →+ MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom f)).F) mv) hmf
    f' hf' hcf' hcbf' hcΦf' Lf' hLf' ((t'.X.toGradedCartierModuleData (structureMap ι ψR) hc').nMap ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hcf') (baseChangeEq (Rigidified.awayHom f') rfl) (fun x => baseChangeEq_verschiebungInt _ _ x) (fun x => baseChangeEq_endAct _ _ (fun _ => rfl) x) zv') hzf' ((baseChangeEq (Rigidified.awayHom f') rfl : MvFormalGroup.CartierModule p t'.X.F →+ MvFormalGroup.CartierModule p (t'.XS (Rigidified.awayHom f')).F) mv') hmf'
  have hawf : ∀ (g : DualNumber κ) (hg : g ∉ x.asIdeal) (b : DualNumber κ),
      Rigidified.awayToLoc x g hg (Rigidified.awayHom g b) = Rigidified.locHom x b := by
    intro g hg b
    unfold Rigidified.awayToLoc
    exact IsLocalization.Away.lift_eq g _ b
  have hA : ∀ l, Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent ((baseChangeEq (Rigidified.awayHom f) rfl : MvFormalGroup.CartierModule p t.X.F →+ MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom f)).F) mv) l) =
      Rigidified.locHom x (MvFormalGroup.CartierModule.tangent mv l) := fun l => by
    rw [show MvFormalGroup.CartierModule.tangent ((baseChangeEq (Rigidified.awayHom f) rfl : MvFormalGroup.CartierModule p t.X.F →+ MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom f)).F) mv) l = Rigidified.awayHom f (MvFormalGroup.CartierModule.tangent mv l)
      from congrFun (tangent_baseChangeEq _ _ _) l, hawf]
  have hA' : ∀ l, Rigidified.awayToLoc x f' hf' (MvFormalGroup.CartierModule.tangent ((baseChangeEq (Rigidified.awayHom f') rfl : MvFormalGroup.CartierModule p t'.X.F →+ MvFormalGroup.CartierModule p (t'.XS (Rigidified.awayHom f')).F) mv') l) =
      Rigidified.locHom x (MvFormalGroup.CartierModule.tangent mv' l) := fun l => by
    rw [show MvFormalGroup.CartierModule.tangent ((baseChangeEq (Rigidified.awayHom f') rfl : MvFormalGroup.CartierModule p t'.X.F →+ MvFormalGroup.CartierModule p (t'.XS (Rigidified.awayHom f')).F) mv') l = Rigidified.awayHom f' (MvFormalGroup.CartierModule.tangent mv' l)
      from congrFun (tangent_baseChangeEq _ _ _) l, hawf]
  have htan : MvFormalGroup.CartierModule.tangent mv' = Λ (MvFormalGroup.CartierModule.tangent mv) := by
    funext j
    apply injective_algebraMap_atPrime_of_forall_isUnit (DualNumber κ) x hxunit
    have hj : Rigidified.locHom x (MvFormalGroup.CartierModule.tangent mv' j) =
        ∑ l : Fin 2, Rigidified.locHom x (Λ (Pi.single l 1) j) * Rigidified.locHom x (MvFormalGroup.CartierModule.tangent mv l) :=
      (hA' j).symm.trans ((hl j).trans (Finset.sum_congr rfl fun l _ => congrArg (fun c => Rigidified.locHom x (Λ (Pi.single l 1) j) * c) (hA l)))
    simp only [← map_mul, ← map_sum] at hj
    refine hj.trans ?_
    congr 1
    rw [show Λ (MvFormalGroup.CartierModule.tangent mv) = Λ.toLinearMap (MvFormalGroup.CartierModule.tangent mv) from rfl,
      linearMap_pi_apply_eq_sum (DualNumber κ) Λ.toLinearMap]
    rfl

  obtain ⟨hc₂, hcb₂, hcΦ2, L₂, hL₂, z₂, hz₂, ⟨hXh, hbcV, hbcPi, hz₂eq⟩, -⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
      p ι Φ hcΦ rΦ ψR hR t ht f hcf hcbf hcΦf Lf hLf i ((t.X.toGradedCartierModuleData (structureMap ι ψR) hc).nMap ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hcf) (baseChangeEq (Rigidified.awayHom f) rfl) (fun x => baseChangeEq_verschiebungInt _ _ x) (fun x => baseChangeEq_endAct _ _ (fun _ => rfl) x) zv) v hzf (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ) (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p])).comp_algebraMap hκ (hfunit f hf) htb

  have hnil₁ : IsNilpotent (p : Rigidified.Baway (1 : κ)) := by
    have := hκ.map (algebraMap κ (Rigidified.Baway (1 : κ))); rwa [map_natCast] at this
  have hγ₁ := (hγ.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)).map (Rigidified.awayHom (1 : κ))
  have hD₁ := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p
    (Rigidified.jS ι ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) (Rigidified.awayHom (1 : κ))) ((t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)).XS (Rigidified.awayHom (1 : κ))) _ hγ₁ hc₁).2
  have hL₁₂ : L₁ = L₂ :=
    CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.eq_of_isNilpotent p _ hnil₁ _ hD₁ L₁ L₂ hL₁ hL₂
  subst hL₁₂

  have hcompf : ∀ mm : MvFormalGroup.CartierModule p t.X.F,
      baseChangeEq _ hXh ((baseChangeEq (Rigidified.awayHom f) rfl : MvFormalGroup.CartierModule p t.X.F →+ MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom f)).F) mm) = (baseChangeEq ((Rigidified.awayHom (1 : κ)).comp (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) hF') mm := by
    intro mm
    refine MvFormalGroup.CartierModule.ext (funext fun jj => ?_)
    show MvPowerSeries.map _ (MvPowerSeries.map _ (mm.toPowerSeries jj)) = MvPowerSeries.map _ (mm.toPowerSeries jj)
    rw [← RingHom.comp_apply (MvPowerSeries.map _) (MvPowerSeries.map _), ← MvPowerSeries.map_comp]
    congr 2
    exact RingHom.ext fun a => by simp [IsLocalization.Away.lift_eq]
  have hz₂' : z₂ = (t.X.toGradedCartierModuleData (structureMap ι ψR) hc).nMap (((t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)).XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) (Rigidified.awayHom (1 : κ))) hc₁) (baseChangeEq ((Rigidified.awayHom (1 : κ)).comp (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) hF') (fun x => baseChangeEq_verschiebungInt _ _ x) (fun x => baseChangeEq_endAct _ _ (fun _ => rfl) x) zv := by
    rw [hz₂eq]
    exact nMap_nMap _ _ _ _ _ _ _ _ _ _ _ _ hcompf zv

  have hz₂'' : (t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)).IsEtaSection ι hcΦ rΦ ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) htb.2.2.1 (Rigidified.awayHom (1 : κ)) hc₁ hcb₁ hcΦ1 L₁ hL₁ i
      ((t.X.toGradedCartierModuleData (structureMap ι ψR) hc).nMap (((t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)).XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) (Rigidified.awayHom (1 : κ))) hc₁) (baseChangeEq ((Rigidified.awayHom (1 : κ)).comp (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) hF') (fun x => baseChangeEq_verschiebungInt _ _ x) (fun x => baseChangeEq_endAct _ _ (fun _ => rfl) x) zv) v := by
    rw [← hz₂']; exact hz₂
  haveI : IsNoetherianRing (Rigidified.Baway (1 : κ)) := IsLocalization.isNoetherianRing (Submonoid.powers (1 : κ)) _ inferInstance
  have heq := CerednikDrinfeld.SpecialFormal.Rigidified.eq_of_isEtaSection_of_isEtaSection p ι Φ hΦ hΦ4 hcΦ rΦ ⟨LΦ, hLΦ⟩ hrΦ
    ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) (t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) htb (Rigidified.awayHom (1 : κ)) hnil₁ hc₁ hcb₁ hcΦ1 L₁ hL₁ i v _ _ hv hz₂''
  have hzz : z = zv := hbij.2.1 hz hzv heq
  subst hzz
  have htm : MvFormalGroup.CartierModule.tangent m = MvFormalGroup.CartierModule.tangent mv :=
    CerednikDrinfeld.FormalODModule.tangent_eq_of_mkQ_eq p (structureMap ι ψR) t.X hc m mv (hm.trans hmv.symm)
  exact ⟨zv', hzv', mv', hmv', by rw [htan, htm]⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_mem_etaPiece_tangent_eq_of_line_transport
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_mem_etaPiece_tangent_eq_of_line_transport (solution)
