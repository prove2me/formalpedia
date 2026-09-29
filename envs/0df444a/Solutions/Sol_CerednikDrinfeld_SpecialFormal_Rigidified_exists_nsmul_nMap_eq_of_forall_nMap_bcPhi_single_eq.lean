-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_nMap_eq_of_forall_nMap_bcPhi_single_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/8168ee53-92f3-590a-ac01-40f97abd827b

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_pow_smul_eq_sum_smul_add_sum_smul_nVarpi_of_bijOn_etaPiece_zero_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq_of_isVAdicallyComplete
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isHomogeneousVBasis_bcPhi_apply
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_nMap_eq_of_forall_nMap_bcPhi_single_eq
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace NRigid

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime]

theorem map_frobenius_witt {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (w : WittVector p R) :
    WittVector.map f (WittVector.frobenius w) = WittVector.frobenius (WittVector.map f w) := by
  have := (WittVector.frobeniusFun_isPoly p).map f w
  exact this

theorem map_id_witt {R : Type} [CommRing R] (w : WittVector p R) : WittVector.map (RingHom.id R) w = w := by
  ext n; simp

theorem smul3 {M : Type} [AddCommMonoid M] (q a e : ℕ) (x : M) :
    q • (e • (q ^ a • x)) = (q ^ (a + 1) * e) • x := by
  rw [← mul_smul, ← mul_smul]
  congr 1
  ring

theorem nsmul_nMk {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (k : ℕ) (m m' : D.M) : k • D.nMk (m, m') = D.nMk (k • m, k • m') := by
  rw [← map_nsmul]; rfl

theorem nVarpi_nMk {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (m m' : D.M) : D.nVarpi (D.nMk (m, m')) = D.nMk (D.varpi m, D.varpi m') := rfl

theorem nMap_nVarpi {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (z : D.NMod) :
    D.nMap D' f hV hPi (D.nVarpi z) = D'.nVarpi (D.nMap D' f hV hPi z) := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [nVarpi_nMk, nMap_nMk, nMap_nMk, nVarpi_nMk, hPi, hPi]

theorem nMap_smul_map {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}
    (φ : B →+* B')
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    (hf : ∀ (w : WittVector p B) (x : D.M), f (w • x) = WittVector.map φ w • f x)
    (w : WittVector p B) (z : D.NMod) :
    D.nMap D' f hV hPi (w • z) = WittVector.map φ w • D.nMap D' f hV hPi z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [smul_nMk, nMap_nMk, nMap_nMk, smul_nMk, hf, hf, map_frobenius_witt]

theorem nMap_smul {B : Type} [CommRing B] {j j' : Zp2 p →+* B}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    (hf : ∀ (w : WittVector p B) (x : D.M), f (w • x) = w • f x)
    (w : WittVector p B) (z : D.NMod) :
    D.nMap D' f hV hPi (w • z) = w • D.nMap D' f hV hPi z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [smul_nMk, nMap_nMk, nMap_nMk, smul_nMk, hf, hf]

theorem nsmul_eq_zero_of_nMk_eq_zero {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (D : GradedCartierModuleData p B j) (x : D.M) (hx : D.nMk (x, 0) = 0) : (p : ℕ) • x = 0 := by
  rw [nMk_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨y, hy⟩ := hx
  rw [nRelMap_apply, Prod.mk.injEq] at hy
  obtain ⟨hy1, hy2⟩ := hy
  have hPi : D.varpi (D.ofSigma y) = 0 := by
    have h2 : -D.varpi (D.ofSigma y) = 0 := D.toSigma.injective hy2
    exact neg_eq_zero.mp h2
  have hpy : (p : ℕ) • D.ofSigma y = 0 := by
    rw [← D.varpi_varpi, hPi, map_zero]
  rw [← hy1, ← map_nsmul, hpy, map_zero]

theorem nMk_sub_zero {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (x y : D.M) : D.nMk (x - y, 0) = D.nMk (x, 0) - D.nMk (y, 0) := by
  rw [← map_sub, Prod.mk_sub_mk, sub_zero]

theorem main {R B' : Type} [CommRing R] [CommRing B'] {j₀ : Zp2 p →+* R} {jS jX : Zp2 p →+* B'}
    (φ : R →+* B')
    (D₀ : GradedCartierModuleData p R j₀) (DS : GradedCartierModuleData p B' jS)
    (DX : GradedCartierModuleData p B' jX) (hDX : DX.IsVAdicallyComplete)
    (bc : D₀.M →+ DS.M) (hbcW : ∀ (w : WittVector p R) (x : D₀.M), bc (w • x) = WittVector.map φ w • bc x)
    (hbcV : ∀ x, bc (D₀.verschiebung x) = DS.verschiebung (bc x))
    (hbcPi : ∀ x, bc (D₀.varpi x) = DS.varpi (bc x))
    (γ : Fin 2 → D₀.M) (hγS : DS.IsHomogeneousVBasis (fun i => bc (γ i)))
    (f₁ f₂ : DS.M →+ DX.M)
    (hW₁ : ∀ (w : WittVector p B') (x : DS.M), f₁ (w • x) = w • f₁ x)
    (hW₂ : ∀ (w : WittVector p B') (x : DS.M), f₂ (w • x) = w • f₂ x)
    (hV₁ : ∀ x, f₁ (DS.verschiebung x) = DX.verschiebung (f₁ x))
    (hPi₁ : ∀ x, f₁ (DS.varpi x) = DX.varpi (f₁ x))
    (hV₂ : ∀ x, f₂ (DS.verschiebung x) = DX.verschiebung (f₂ x))
    (hPi₂ : ∀ x, f₂ (DS.varpi x) = DX.varpi (f₂ x))
    (e₁ e₂ : ℕ) (gen : Fin 2 → D₀.NMod)
    (hgen : ∀ i : Fin 2, e₁ • DS.nMap DX f₁ hV₁ hPi₁ (D₀.nMap DS bc hbcV hbcPi (gen i)) =
      e₂ • DS.nMap DX f₂ hV₂ hPi₂ (D₀.nMap DS bc hbcV hbcPi (gen i)))
    (hspan : ∃ a : ℕ, ∀ x : D₀.NMod, ∃ c d : Fin 2 → WittVector p R,
      p ^ a • x = (∑ i : Fin 2, c i • gen i) + ∑ i : Fin 2, d i • D₀.nVarpi (gen i)) :
    ∃ a : ℕ, ∀ z : DS.NMod,
      p ^ a • (e₁ • DS.nMap DX f₁ hV₁ hPi₁ z) = p ^ a • (e₂ • DS.nMap DX f₂ hV₂ hPi₂ z) := by
  obtain ⟨a, ha⟩ := hspan
  set F₁ : D₀.NMod →+ DX.NMod := (DS.nMap DX f₁ hV₁ hPi₁).comp (D₀.nMap DS bc hbcV hbcPi) with hF₁
  set F₂ : D₀.NMod →+ DX.NMod := (DS.nMap DX f₂ hV₂ hPi₂).comp (D₀.nMap DS bc hbcV hbcPi) with hF₂
  have hF₁app : ∀ y, F₁ y = DS.nMap DX f₁ hV₁ hPi₁ (D₀.nMap DS bc hbcV hbcPi y) := fun y => rfl
  have hF₂app : ∀ y, F₂ y = DS.nMap DX f₂ hV₂ hPi₂ (D₀.nMap DS bc hbcV hbcPi y) := fun y => rfl
  have hF₁Pi : ∀ y, F₁ (D₀.nVarpi y) = DX.nVarpi (F₁ y) := fun y => by
    rw [hF₁app, hF₁app, nMap_nVarpi, nMap_nVarpi]
  have hF₂Pi : ∀ y, F₂ (D₀.nVarpi y) = DX.nVarpi (F₂ y) := fun y => by
    rw [hF₂app, hF₂app, nMap_nVarpi, nMap_nVarpi]
  have hF₁W : ∀ (w : WittVector p R) y, F₁ (w • y) = WittVector.map φ w • F₁ y := fun w y => by
    rw [hF₁app, hF₁app, nMap_smul_map φ D₀ DS bc hbcV hbcPi hbcW, nMap_smul DS DX f₁ hV₁ hPi₁ hW₁]
  have hF₂W : ∀ (w : WittVector p R) y, F₂ (w • y) = WittVector.map φ w • F₂ y := fun w y => by
    rw [hF₂app, hF₂app, nMap_smul_map φ D₀ DS bc hbcV hbcPi hbcW, nMap_smul DS DX f₂ hV₂ hPi₂ hW₂]
  set G : D₀.NMod →+ DX.NMod := e₁ • F₁ - e₂ • F₂ with hG
  have hGapp : ∀ y, G y = e₁ • F₁ y - e₂ • F₂ y := fun y => by
    simp only [hG, AddMonoidHom.sub_apply, AddMonoidHom.nsmul_apply]
  have hGgen : ∀ i, G (gen i) = 0 := fun i => by
    rw [hGapp, sub_eq_zero, hF₁app, hF₂app]; exact hgen i
  have hGPi : ∀ y, G (D₀.nVarpi y) = DX.nVarpi (G y) := fun y => by
    rw [hGapp, hGapp, hF₁Pi, hF₂Pi, map_sub, map_nsmul, map_nsmul]
  have hGW : ∀ (w : WittVector p R) y, G (w • y) = WittVector.map φ w • G y := fun w y => by
    rw [hGapp, hGapp, hF₁W, hF₂W, smul_sub, smul_comm e₁ (WittVector.map φ w), smul_comm e₂ (WittVector.map φ w)]
  have hGzero : ∀ x, G (p ^ a • x) = 0 := fun x => by
    obtain ⟨c, d, hx⟩ := ha x
    rw [hx, map_add, map_sum, map_sum]
    have h1 : ∀ i, G (c i • gen i) = 0 := fun i => by rw [hGW, hGgen, smul_zero]
    have h2 : ∀ i, G (d i • D₀.nVarpi (gen i)) = 0 := fun i => by rw [hGW, hGPi, hGgen, map_zero, smul_zero]
    simp only [h1, h2, Finset.sum_const_zero, add_zero]

  have step3 : ∀ m : D₀.M, (p ^ (a + 1) * e₁) • f₁ (bc m) = (p ^ (a + 1) * e₂) • f₂ (bc m) := fun m => by
    have h := hGzero (D₀.nMk (m, 0))
    rw [hGapp, sub_eq_zero, nsmul_nMk, smul_zero, hF₁app, hF₂app] at h
    simp only [nMap_nMk, map_zero, nsmul_nMk, smul_zero] at h
    have h2 : DX.nMk (e₁ • f₁ (bc (p ^ a • m)) - e₂ • f₂ (bc (p ^ a • m)), 0) = 0 := by
      rw [nMk_sub_zero, h, sub_self]
    have h3 := nsmul_eq_zero_of_nMk_eq_zero DX _ h2
    rw [map_nsmul, map_nsmul, map_nsmul, smul_sub, sub_eq_zero, smul3, smul3] at h3
    exact h3

  set δ₁ : DS.M →+ DX.M := (p ^ (a + 1) * e₁) • f₁ with hδ₁
  set δ₂ : DS.M →+ DX.M := (p ^ (a + 1) * e₂) • f₂ with hδ₂
  have hδ₁app : ∀ x, δ₁ x = (p ^ (a + 1) * e₁) • f₁ x := fun x => AddMonoidHom.nsmul_apply _ _ _
  have hδ₂app : ∀ x, δ₂ x = (p ^ (a + 1) * e₂) • f₂ x := fun x => AddMonoidHom.nsmul_apply _ _ _
  have key : δ₁ = δ₂ :=
    CerednikDrinfeld.GradedCartierModuleData.eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq_of_isVAdicallyComplete
      p (RingHom.id B') DS DX hDX (fun i => bc (γ i)) hγS δ₁ δ₂
      (fun w x => by rw [hδ₁app, hδ₁app, hW₁, smul_comm, map_id_witt])
      (fun x => by rw [hδ₁app, hδ₁app, hV₁, map_nsmul])
      (fun w x => by rw [hδ₂app, hδ₂app, hW₂, smul_comm, map_id_witt])
      (fun x => by rw [hδ₂app, hδ₂app, hV₂, map_nsmul])
      (fun i => by rw [hδ₁app, hδ₂app]; exact step3 (γ i))
  have k1 : ∀ u : DS.M, p ^ (a + 1) • (e₁ • f₁ u) = p ^ (a + 1) • (e₂ • f₂ u) := fun u => by
    have := congrArg (fun δ : DS.M →+ DX.M => δ u) key
    simp only [hδ₁app, hδ₂app] at this
    rw [← mul_smul, ← mul_smul]
    exact this
  refine ⟨a + 1, fun z => ?_⟩
  obtain ⟨⟨m, m'⟩, rfl⟩ := DS.nMk_surjective z
  rw [nMap_nMk, nMap_nMk, nsmul_nMk, nsmul_nMk, nsmul_nMk, nsmul_nMk, k1, k1]

end NRigid

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] (ψ : WittVector p k →+* B)
    (t' : Rigidified p Φ B) (ht' : t'.IsAdmissible ι ψ)
    {S : Type} [CommRing S] (g : B →+* S)
    (hcb' : t'.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (f₁ f₂ : MvFormalGroup.CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ g).F →+
      MvFormalGroup.CartierModule p (t'.XbarS g).F)
    (hW₁ : ∀ (w : WittVector p (S ⧸ pIdeal p S)) (x : MvFormalGroup.CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ g).F),
      f₁ (w • x) = w • f₁ x)
    (hW₂ : ∀ (w : WittVector p (S ⧸ pIdeal p S)) (x : MvFormalGroup.CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ g).F),
      f₂ (w • x) = w • f₂ x)
    (hV₁ : ∀ x, f₁ (((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).verschiebung x) = ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb').verschiebung (f₁ x))
    (hPi₁ : ∀ x, f₁ (((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).varpi x) = ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb').varpi (f₁ x))
    (hV₂ : ∀ x, f₂ (((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).verschiebung x) = ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb').verschiebung (f₂ x))
    (hPi₂ : ∀ x, f₂ (((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).varpi x) = ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb').varpi (f₂ x))
    (e₁ e₂ : ℕ)
    (hgen : ∀ i : Fin 2,
      e₁ • ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMap ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb') f₁ hV₁ hPi₁
          ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg)
            (Rigidified.bcPhi (Φ := Φ) ψ g) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ g)
            (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ g) (rΦ (Pi.single i 1))) =
        e₂ • ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMap ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb') f₂ hV₂ hPi₂
          ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg)
            (Rigidified.bcPhi (Φ := Φ) ψ g) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ g)
            (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ g) (rΦ (Pi.single i 1)))) :
    ∃ a : ℕ, ∀ z : ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).NMod,
      p ^ a • (e₁ • ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMap ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb') f₁ hV₁ hPi₁ z) =
        p ^ a • (e₂ • ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMap ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb') f₂ hV₂ hPi₂ z) := by
  obtain ⟨a, ha⟩ :=
    CerednikDrinfeld.FormalODModule.exists_pow_smul_eq_sum_smul_add_sum_smul_nVarpi_of_bijOn_etaPiece_zero_of_isAlgClosed
      p k ι Φ hΦ hΦ4 hcΦ rΦ hrΦ
  obtain ⟨γ, -, hγS⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_isHomogeneousVBasis_bcPhi_apply p k ι Φ hΦ hcΦ ψ g hcΦg
  have hDX : ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb').IsVAdicallyComplete :=
    fun x => MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add p
      (t'.XbarS g).F x
  have hcomp : (Φ.F.map ((reduceMap g).comp (residueMap ψ))) = (Rigidified.PhibarS (Φ := Φ) ψ g).F := by
    show (Φ.F.map ((reduceMap g).comp (residueMap ψ))) = (Φ.F.map (residueMap ψ)).map (reduceMap g)
    rw [MvFormalGroup.map_map_ringHom]
  have hbc1 : ∀ x : MvFormalGroup.CartierModule p Φ.F, Rigidified.bcPhi (Φ := Φ) ψ g x =
      MvFormalGroup.CartierModule.baseChangeEq ((reduceMap g).comp (residueMap ψ)) hcomp x := by
    intro x
    exact MvFormalGroup.CartierModule.baseChangeEq_baseChangeEq (residueMap ψ) (reduceMap g) rfl rfl hcomp x
  have hbcW : ∀ (w : WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k)))
      (x : MvFormalGroup.CartierModule p Φ.F),
      Rigidified.bcPhi (Φ := Φ) ψ g (w • x) =
        WittVector.map ((reduceMap g).comp (residueMap ψ)) w • Rigidified.bcPhi (Φ := Φ) ψ g x := by
    intro w x
    rw [hbc1, hbc1, MvFormalGroup.CartierModule.baseChangeEq_smul_witt]
  exact NRigid.main ((reduceMap g).comp (residueMap ψ))
    (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ)
    ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg)
    ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb') hDX
    (Rigidified.bcPhi (Φ := Φ) ψ g) hbcW (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ g)
    (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ g) γ hγS f₁ f₂ hW₁ hW₂ hV₁ hPi₁ hV₂ hPi₂ e₁ e₂
    (fun i => rΦ (Pi.single i 1)) hgen ⟨a, ha⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_nMap_eq_of_forall_nMap_bcPhi_single_eq
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_nMap_eq_of_forall_nMap_bcPhi_single_eq (solution)
