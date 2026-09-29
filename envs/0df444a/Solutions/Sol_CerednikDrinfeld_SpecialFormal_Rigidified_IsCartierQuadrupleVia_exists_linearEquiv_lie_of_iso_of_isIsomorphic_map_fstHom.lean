-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_linearEquiv_lie_of_iso_of_isIsomorphic_map_fstHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/ec0a3adc-54ae-56f8-875e-d6b46fdef9e8

import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_via_linearPart_of_isODHom_of_comp_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isCartierQuadruple_of_isAdmissible_of_lieVarpi_eq_zero_wittVector
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_semilinear_tangent
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_u_baseChange
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_linearEquiv_lie_of_iso_of_isIsomorphic_map_fstHom
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj"

set_option autoImplicit false

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_linearEquiv_lie_of_iso_of_isIsomorphic_map_fstHom.CerednikDrinfeld CerednikDrinfeld.SpecialFormal P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_linearEquiv_lie_of_iso_of_isIsomorphic_map_fstHom.CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega"

open scoped PadicInt Padic

open scoped TensorProduct

namespace LieTransport

theorem exists_glue {R : Type*} [CommRing R] {E E' : Type*} [AddCommGroup E] [Module R E]
    [AddCommGroup E'] [Module R E']
    (P Q : Submodule R E) (h : IsCompl P Q) (P' Q' : Submodule R E') (h' : IsCompl P' Q')
    (Λ₀ : ↥P ≃ₗ[R] ↥P') (Λ₁ : ↥Q ≃ₗ[R] ↥Q') :
    ∃ Λ : E ≃ₗ[R] E', (∀ x : ↥P, Λ (x : E) = (Λ₀ x : E')) ∧ (∀ x : ↥Q, Λ (x : E) = (Λ₁ x : E')) := by
  refine ⟨((Submodule.prodEquivOfIsCompl P Q h).symm.trans (Λ₀.prodCongr Λ₁)).trans
    (Submodule.prodEquivOfIsCompl P' Q' h'), fun x => ?_, fun x => ?_⟩
  · simp [LinearEquiv.trans_apply, Submodule.prodEquivOfIsCompl_symm_apply_left, LinearEquiv.prodCongr_apply,
      Submodule.coe_prodEquivOfIsCompl']
  · simp [LinearEquiv.trans_apply, Submodule.prodEquivOfIsCompl_symm_apply_right, LinearEquiv.prodCongr_apply,
      Submodule.coe_prodEquivOfIsCompl']

theorem map_eq_of_glue {R : Type*} [CommRing R] {E E' : Type*} [AddCommGroup E] [Module R E]
    [AddCommGroup E'] [Module R E']
    (P : Submodule R E) (P' : Submodule R E') (Λ₀ : ↥P ≃ₗ[R] ↥P') (Λ : E ≃ₗ[R] E')
    (hΛ : ∀ x : ↥P, Λ (x : E) = (Λ₀ x : E')) :
    Submodule.map Λ.toLinearMap P = P' := by
  ext y
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [show x = ((⟨x, hx⟩ : ↥P) : E) from rfl, hΛ]
    exact (Λ₀ ⟨x, hx⟩).2
  · intro hy
    refine ⟨((Λ₀.symm ⟨y, hy⟩ : ↥P) : E), (Λ₀.symm ⟨y, hy⟩).2, ?_⟩
    rw [hΛ, LinearEquiv.apply_symm_apply]

end LieTransport

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_via_linearPart_of_isODHom_of_comp_eq Zp2 FormalODModule FormalODModule.IsODHom SpecialFormal.Rigidified SpecialFormal.Rigidified.IsAdmissible FormalOmega.DrinfeldDatum SpecialFormal.Rigidified.IsCartierQuadruple SpecialFormal.Rigidified.IsCartierQuadrupleVia SpecialFormal.Rigidified.isCartierQuadruple_iff_exists_via SpecialFormal.Rigidified.exists_isCartierQuadruple_of_isAdmissible_of_lieVarpi_eq_zero_wittVector SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_semilinear_tangent SpecialFormal.Rigidified.IsCartierQuadrupleVia.u_baseChange SpecialFormal.Rigidified.IsCartierQuadruple.isBaseChangeAlong FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed SpecialFormal.Rigidified.IsAdmissible.map_ringHom" namespace SpecialFormal p2m_export "CerednikDrinfeld.SpecialFormal" "Rigidified.IsCartierQuadrupleVia.exists_via_linearPart_of_isODHom_of_comp_eq Series Series.id pIdeal structureMap Rigidified Rigidified.IsAdmissible Rigidified.jbar Rigidified.IsCartierQuadruple Rigidified.IsCartierQuadrupleVia Rigidified.isCartierQuadruple_iff_exists_via Rigidified.exists_isCartierQuadruple_of_isAdmissible_of_lieVarpi_eq_zero_wittVector Rigidified.IsCartierQuadrupleVia.exists_semilinear_tangent Rigidified.IsCartierQuadrupleVia.u_baseChange Rigidified.IsCartierQuadruple.isBaseChangeAlong Rigidified.IsAdmissible.map_ringHom" namespace Rigidified p2m_export "CerednikDrinfeld.SpecialFormal.Rigidified" "IsCartierQuadrupleVia.exists_via_linearPart_of_isODHom_of_comp_eq Xbar IsAdmissible IsIsomorphic map mk n ρ X jbar IsCartierQuadruple IsCartierQuadrupleVia isCartierQuadruple_iff_exists_via exists_isCartierQuadruple_of_isAdmissible_of_lieVarpi_eq_zero_wittVector IsCartierQuadrupleVia.exists_semilinear_tangent IsCartierQuadrupleVia.u_baseChange IsCartierQuadruple.isBaseChangeAlong IsAdmissible.map_ringHom" namespace IsCartierQuadrupleVia p2m_export "CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia" "exists_via_linearPart_of_isODHom_of_comp_eq exists_semilinear_tangent u_baseChange" end CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia
p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.Rigidified CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia" in
open LieTransport in

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_lie_transport
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B : Type} [CommRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι ψ)
    (Q Q' : FormalOmega.DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (σ₀ : Q.T₀ ≃ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
    (σ₁ : Q.T₁ ≃ₗ[B] ↥(t.X.lieOne (structureMap ι ψ)))
    (hQ : t.IsCartierQuadrupleVia ι hcΦ rΦ ψ Q σ₀ σ₁)
    (σ₀' : Q'.T₀ ≃ₗ[B] ↥(t'.X.lieZero (structureMap ι ψ)))
    (σ₁' : Q'.T₁ ≃ₗ[B] ↥(t'.X.lieOne (structureMap ι ψ)))
    (hQ' : t'.IsCartierQuadrupleVia ι hcΦ rΦ ψ Q' σ₀' σ₁')
    (I : Q.Iso Q') :
    ∃ Λ : t.X.Lie ≃ₗ[B] t'.X.Lie,
      (∀ s : Q.T₀, Λ ((σ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) =
        ((σ₀' (I.τ₀ s) : ↥(t'.X.lieZero (structureMap ι ψ))) : t'.X.Lie)) ∧
      (∀ s : Q.T₁, Λ ((σ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) =
        ((σ₁' (I.τ₁ s) : ↥(t'.X.lieOne (structureMap ι ψ))) : t'.X.Lie)) ∧
      Submodule.map Λ.toLinearMap (t.X.lieZero (structureMap ι ψ)) = t'.X.lieZero (structureMap ι ψ) ∧
      Submodule.map Λ.toLinearMap (t.X.lieOne (structureMap ι ψ)) = t'.X.lieOne (structureMap ι ψ) ∧
      (∀ w : t.X.Lie, Λ (t.X.lieVarpi w) = t'.X.lieVarpi (Λ w)) := by
  obtain ⟨-, hT0, hT1, -⟩ := hQ
  obtain ⟨-, hT0', hT1', -⟩ := hQ'

  let Λ₀ : ↥(t.X.lieZero (structureMap ι ψ)) ≃ₗ[B] ↥(t'.X.lieZero (structureMap ι ψ)) :=
    (σ₀.symm.trans I.τ₀).trans σ₀'
  let Λ₁ : ↥(t.X.lieOne (structureMap ι ψ)) ≃ₗ[B] ↥(t'.X.lieOne (structureMap ι ψ)) :=
    (σ₁.symm.trans I.τ₁).trans σ₁'
  obtain ⟨Λ, hΛ0, hΛ1⟩ := exists_glue _ _ ht.1.1 _ _ ht'.1.1 Λ₀ Λ₁
  have hΛσ₀ : ∀ s : Q.T₀, Λ ((σ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) =
      ((σ₀' (I.τ₀ s) : ↥(t'.X.lieZero (structureMap ι ψ))) : t'.X.Lie) := by
    intro s; rw [hΛ0]; simp [Λ₀]
  have hΛσ₁ : ∀ s : Q.T₁, Λ ((σ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) =
      ((σ₁' (I.τ₁ s) : ↥(t'.X.lieOne (structureMap ι ψ))) : t'.X.Lie) := by
    intro s; rw [hΛ1]; simp [Λ₁]
  refine ⟨Λ, hΛσ₀, hΛσ₁, map_eq_of_glue _ _ Λ₀ Λ hΛ0, map_eq_of_glue _ _ Λ₁ Λ hΛ1, ?_⟩

  have key0 : ∀ x : ↥(t.X.lieZero (structureMap ι ψ)), Λ (t.X.lieVarpi (x : t.X.Lie)) = t'.X.lieVarpi (Λ (x : t.X.Lie)) := by
    intro x
    obtain ⟨s, rfl⟩ : ∃ s, σ₀ s = x := σ₀.surjective x
    rw [← hT0 s, hΛσ₁, hΛσ₀, I.τ₁_Pi₀, hT0']
  have key1 : ∀ x : ↥(t.X.lieOne (structureMap ι ψ)), Λ (t.X.lieVarpi (x : t.X.Lie)) = t'.X.lieVarpi (Λ (x : t.X.Lie)) := by
    intro x
    obtain ⟨s, rfl⟩ : ∃ s, σ₁ s = x := σ₁.surjective x
    rw [← hT1 s, hΛσ₀, hΛσ₁, I.τ₀_Pi₁, hT1']
  intro w
  obtain ⟨⟨x0, x1⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl _ _ ht.1.1).surjective w
  rw [Submodule.coe_prodEquivOfIsCompl']
  simp only [map_add, key0, key1]

namespace LieTransportKey

theorem forall_of_forall_numerator {R : Type*} [CommRing R] (S : Submonoid R) (hS : ∀ s ∈ S, IsUnit s)
    {T : Type*} [AddCommGroup T] [Module R T]
    {D : Type*} [AddCommGroup D] [Module (Localization S) D]
    {ι' : Type*} (g : ι' → D) (hspan : Submodule.span (Localization S) (Set.range g) = ⊤)
    (u : D →ₗ[Localization S] LocalizedModule S T) (hu : Function.Surjective u)
    (P : T → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b)) (hsmul : ∀ (r : R) (a : T), P a → P (r • a))
    (hgen : ∀ (i : ι') (tt : T) (s : S), u (g i) = LocalizedModule.mk tt s → P tt) :
    ∀ tt : T, P tt := by
  classical

  have hsmulS : ∀ (s : S) (a : T), P a → P (s • a) := fun s a ha => by
    rw [Submonoid.smul_def]; exact hsmul _ _ ha

  have hmk : ∀ x : LocalizedModule S T, ∃ (tt : T) (s : S), x = LocalizedModule.mk tt s :=
    LocalizedModule.induction_on (β := fun x => ∃ (tt : T) (s : S), x = LocalizedModule.mk tt s)
      (fun m s => ⟨m, s, rfl⟩)

  let W : Submodule (Localization S) D :=
    { carrier := {d | ∃ (tt : T) (s : S), u d = LocalizedModule.mk tt s ∧ P tt}
      add_mem' := by
        rintro a b ⟨ta, sa, ha, hPa⟩ ⟨tb, sb, hb, hPb⟩
        refine ⟨sb • ta + sa • tb, sa * sb, ?_, hadd _ _ (hsmulS _ _ hPa) (hsmulS _ _ hPb)⟩
        rw [map_add, ha, hb, LocalizedModule.mk_add_mk]
      zero_mem' := ⟨0, 1, by rw [map_zero, LocalizedModule.zero_mk], h0⟩
      smul_mem' := by
        rintro c d ⟨td, sd, hd, hPd⟩
        induction c using Localization.induction_on with
        | H y =>
          obtain ⟨r, s0⟩ := y
          refine ⟨r • td, s0 * sd, ?_, hsmul _ _ hPd⟩
          rw [map_smul, hd, LocalizedModule.mk_smul_mk] }

  have hW : ∀ d, d ∈ W := by
    have hle : Submodule.span (Localization S) (Set.range g) ≤ W := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨tt, s, hs⟩ := hmk (u (g i))
      exact ⟨tt, s, hs, hgen i tt s hs⟩
    rw [hspan] at hle
    exact fun d => hle Submodule.mem_top

  intro tt
  obtain ⟨d, hd⟩ := hu (LocalizedModule.mk tt 1)
  obtain ⟨tt', s', hd', hP'⟩ := hW d
  rw [hd, LocalizedModule.mk_eq] at hd'
  obtain ⟨c, hc⟩ := hd'
  have hP1 : P (c • s' • tt) := by rw [hc]; exact hsmulS _ _ (hsmulS _ _ hP')
  obtain ⟨v, hv⟩ := hS _ (S.mul_mem c.2 s'.2)
  have htt : tt = ((v⁻¹ : Rˣ) : R) • (((c : R) * (s' : R)) • tt) := by
    rw [← hv, smul_smul, Units.inv_mul, one_smul]
  rw [htt]
  refine hsmul _ _ ?_
  rw [mul_smul]
  simpa only [Submonoid.smul_def] using hP1

theorem span_one_tmul_eq_top {𝒪 : Type*} [CommRing 𝒪] (A : Type*) [CommRing A] [Algebra 𝒪 A]
    (N : Type*) [AddCommGroup N] [Module 𝒪 N] :
    Submodule.span A (Set.range fun n : N => (1 : A) ⊗ₜ[𝒪] n) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a n =>
    have h : a ⊗ₜ[𝒪] n = a • ((1 : A) ⊗ₜ[𝒪] n) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨n, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem semilinear_eq_of_u_compat₀
    {p : ℕ} [Fact p.Prime]
    {B : Type} [CommRing B] [Algebra ℤ_[p] B] {B' : Type} [CommRing B'] [Algebra ℤ_[p] B']
    (f : B →ₐ[ℤ_[p]] B')
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (Qb : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B')
    (I : Q.Iso Q') (x' : PrimeSpectrum B')
    (hunit : ∀ s : B, f s ∉ x'.asIdeal → IsUnit s)
    (hreg : ∀ (c : B'), c ∉ x'.asIdeal → ∀ (a b : Qb.T₀), c • a = c • b → a = b)
    (hN : Qb.N₀ x' = Q.N₀ (DrinfeldDatum.pointUnder f x'))
    (τb₀ : Q.T₀ →ₛₗ[(f : B →+* B')] Qb.T₀) (τt₀ : Q'.T₀ →ₛₗ[(f : B →+* B')] Qb.T₀)
    (hub : ∀ (x' : PrimeSpectrum B') (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₀ (DrinfeldDatum.pointUnder f x')) (hv' : v ∈ Qb.N₀ x')
    (tt : Q.T₀) (s : B) (hs : f s ∉ x'.asIdeal),
    Q.u₀ (DrinfeldDatum.pointUnder f x') ((1 : locRing B (DrinfeldDatum.pointUnder f x')) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₀ (DrinfeldDatum.pointUnder f x')))) =
      LocalizedModule.mk tt (⟨s, hs⟩ : (DrinfeldDatum.pointUnder f x').asIdeal.primeCompl) →
    Qb.u₀ x' ((1 : locRing B' x') ⊗ₜ[ℤ_[p]] (⟨v, hv'⟩ : ↥(Qb.N₀ x'))) =
      LocalizedModule.mk (τb₀ tt) (⟨f s, hs⟩ : x'.asIdeal.primeCompl))
    (hut : ∀ (x' : PrimeSpectrum B') (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q'.N₀ (DrinfeldDatum.pointUnder f x')) (hv' : v ∈ Qb.N₀ x')
    (tt : Q'.T₀) (s : B) (hs : f s ∉ x'.asIdeal),
    Q'.u₀ (DrinfeldDatum.pointUnder f x') ((1 : locRing B (DrinfeldDatum.pointUnder f x')) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q'.N₀ (DrinfeldDatum.pointUnder f x')))) =
      LocalizedModule.mk tt (⟨s, hs⟩ : (DrinfeldDatum.pointUnder f x').asIdeal.primeCompl) →
    Qb.u₀ x' ((1 : locRing B' x') ⊗ₜ[ℤ_[p]] (⟨v, hv'⟩ : ↥(Qb.N₀ x'))) =
      LocalizedModule.mk (τt₀ tt) (⟨f s, hs⟩ : x'.asIdeal.primeCompl)) :
    ∀ s : Q.T₀, τb₀ s = τt₀ (I.τ₀ s) := by
  have hS : ∀ c ∈ (DrinfeldDatum.pointUnder f x').asIdeal.primeCompl, IsUnit c := fun c hc => hunit c hc
  refine forall_of_forall_numerator (DrinfeldDatum.pointUnder f x').asIdeal.primeCompl hS
    (fun v : ↥(Q.N₀ (DrinfeldDatum.pointUnder f x')) =>
      (1 : locRing B (DrinfeldDatum.pointUnder f x')) ⊗ₜ[ℤ_[p]] (v : ↥(Q.N₀ (DrinfeldDatum.pointUnder f x'))))
    (span_one_tmul_eq_top (𝒪 := ℤ_[p]) (locRing B (DrinfeldDatum.pointUnder f x')) ↥(Q.N₀ (DrinfeldDatum.pointUnder f x')))
    (Q.u₀ (DrinfeldDatum.pointUnder f x')) (Q.u₀_surjective _) (fun tt => τb₀ tt = τt₀ (I.τ₀ tt)) ?_ ?_ ?_ ?_
  · simp only [map_zero]
  · intro a b ha hb; rw [LinearMap.map_add τb₀, LinearEquiv.map_add I.τ₀, LinearMap.map_add τt₀, ha, hb]
  · intro r a ha; rw [LinearMap.map_smulₛₗ τb₀, LinearEquiv.map_smul I.τ₀, LinearMap.map_smulₛₗ τt₀, ha]
  · intro v tt s h
    have hvb : (v : Fin 2 → ℚ_[p]) ∈ Qb.N₀ x' := by rw [hN]; exact v.2
    have hv' : (v : Fin 2 → ℚ_[p]) ∈ Q'.N₀ (DrinfeldDatum.pointUnder f x') := by rw [← I.N₀_eq]; exact v.2
    have h1 := hub x' v v.2 hvb tt s s.2 h
    have h2 : Q'.u₀ (DrinfeldDatum.pointUnder f x') ((1 : locRing B (DrinfeldDatum.pointUnder f x')) ⊗ₜ[ℤ_[p]]
        (⟨(v : Fin 2 → ℚ_[p]), hv'⟩ : ↥(Q'.N₀ (DrinfeldDatum.pointUnder f x')))) = LocalizedModule.mk (I.τ₀ tt) s := by
      rw [I.τ₀_u₀ _ v v.2 hv', h, LocalizedModule.map_mk]; rfl
    have h3 := hut x' v hv' hvb (I.τ₀ tt) s s.2 h2
    have h13 := h1.symm.trans h3
    rw [LocalizedModule.mk_eq] at h13
    obtain ⟨c, hc⟩ := h13
    simp only [Submonoid.smul_def] at hc
    rw [smul_smul, smul_smul] at hc
    refine hreg ((c : B') * f s) ?_ _ _ hc
    exact fun hm => (Ideal.IsPrime.mem_or_mem x'.isPrime hm).elim c.2 s.2

theorem semilinear_eq_of_u_compat₁
    {p : ℕ} [Fact p.Prime]
    {B : Type} [CommRing B] [Algebra ℤ_[p] B] {B' : Type} [CommRing B'] [Algebra ℤ_[p] B']
    (f : B →ₐ[ℤ_[p]] B')
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (Qb : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B')
    (I : Q.Iso Q') (x' : PrimeSpectrum B')
    (hunit : ∀ s : B, f s ∉ x'.asIdeal → IsUnit s)
    (hreg : ∀ (c : B'), c ∉ x'.asIdeal → ∀ (a b : Qb.T₁), c • a = c • b → a = b)
    (hN : Qb.N₁ x' = Q.N₁ (DrinfeldDatum.pointUnder f x'))
    (τb₁ : Q.T₁ →ₛₗ[(f : B →+* B')] Qb.T₁) (τt₁ : Q'.T₁ →ₛₗ[(f : B →+* B')] Qb.T₁)
    (hub : ∀ (x' : PrimeSpectrum B') (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₁ (DrinfeldDatum.pointUnder f x')) (hv' : v ∈ Qb.N₁ x')
    (tt : Q.T₁) (s : B) (hs : f s ∉ x'.asIdeal),
    Q.u₁ (DrinfeldDatum.pointUnder f x') ((1 : locRing B (DrinfeldDatum.pointUnder f x')) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₁ (DrinfeldDatum.pointUnder f x')))) =
      LocalizedModule.mk tt (⟨s, hs⟩ : (DrinfeldDatum.pointUnder f x').asIdeal.primeCompl) →
    Qb.u₁ x' ((1 : locRing B' x') ⊗ₜ[ℤ_[p]] (⟨v, hv'⟩ : ↥(Qb.N₁ x'))) =
      LocalizedModule.mk (τb₁ tt) (⟨f s, hs⟩ : x'.asIdeal.primeCompl))
    (hut : ∀ (x' : PrimeSpectrum B') (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q'.N₁ (DrinfeldDatum.pointUnder f x')) (hv' : v ∈ Qb.N₁ x')
    (tt : Q'.T₁) (s : B) (hs : f s ∉ x'.asIdeal),
    Q'.u₁ (DrinfeldDatum.pointUnder f x') ((1 : locRing B (DrinfeldDatum.pointUnder f x')) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q'.N₁ (DrinfeldDatum.pointUnder f x')))) =
      LocalizedModule.mk tt (⟨s, hs⟩ : (DrinfeldDatum.pointUnder f x').asIdeal.primeCompl) →
    Qb.u₁ x' ((1 : locRing B' x') ⊗ₜ[ℤ_[p]] (⟨v, hv'⟩ : ↥(Qb.N₁ x'))) =
      LocalizedModule.mk (τt₁ tt) (⟨f s, hs⟩ : x'.asIdeal.primeCompl)) :
    ∀ s : Q.T₁, τb₁ s = τt₁ (I.τ₁ s) := by
  have hS : ∀ c ∈ (DrinfeldDatum.pointUnder f x').asIdeal.primeCompl, IsUnit c := fun c hc => hunit c hc
  refine forall_of_forall_numerator (DrinfeldDatum.pointUnder f x').asIdeal.primeCompl hS
    (fun v : ↥(Q.N₁ (DrinfeldDatum.pointUnder f x')) =>
      (1 : locRing B (DrinfeldDatum.pointUnder f x')) ⊗ₜ[ℤ_[p]] (v : ↥(Q.N₁ (DrinfeldDatum.pointUnder f x'))))
    (span_one_tmul_eq_top (𝒪 := ℤ_[p]) (locRing B (DrinfeldDatum.pointUnder f x')) ↥(Q.N₁ (DrinfeldDatum.pointUnder f x')))
    (Q.u₁ (DrinfeldDatum.pointUnder f x')) (Q.u₁_surjective _) (fun tt => τb₁ tt = τt₁ (I.τ₁ tt)) ?_ ?_ ?_ ?_
  · simp only [map_zero]
  · intro a b ha hb; rw [LinearMap.map_add τb₁, LinearEquiv.map_add I.τ₁, LinearMap.map_add τt₁, ha, hb]
  · intro r a ha; rw [LinearMap.map_smulₛₗ τb₁, LinearEquiv.map_smul I.τ₁, LinearMap.map_smulₛₗ τt₁, ha]
  · intro v tt s h
    have hvb : (v : Fin 2 → ℚ_[p]) ∈ Qb.N₁ x' := by rw [hN]; exact v.2
    have hv' : (v : Fin 2 → ℚ_[p]) ∈ Q'.N₁ (DrinfeldDatum.pointUnder f x') := by rw [← I.N₁_eq]; exact v.2
    have h1 := hub x' v v.2 hvb tt s s.2 h
    have h2 : Q'.u₁ (DrinfeldDatum.pointUnder f x') ((1 : locRing B (DrinfeldDatum.pointUnder f x')) ⊗ₜ[ℤ_[p]]
        (⟨(v : Fin 2 → ℚ_[p]), hv'⟩ : ↥(Q'.N₁ (DrinfeldDatum.pointUnder f x')))) = LocalizedModule.mk (I.τ₁ tt) s := by
      rw [I.τ₁_u₁ _ v v.2 hv', h, LocalizedModule.map_mk]; rfl
    have h3 := hut x' v hv' hvb (I.τ₁ tt) s s.2 h2
    have h13 := h1.symm.trans h3
    rw [LocalizedModule.mk_eq] at h13
    obtain ⟨c, hc⟩ := h13
    simp only [Submonoid.smul_def] at hc
    rw [smul_smul, smul_smul] at hc
    refine hreg ((c : B') * f s) ?_ _ _ hc
    exact fun hm => (Ideal.IsPrime.mem_or_mem x'.isPrime hm).elim c.2 s.2

end LieTransportKey

open LieTransport LieTransportKey in
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
    (I : Q.Iso Q')
    (hred : (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).IsIsomorphic
      (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ))) :
    ∃ (u₀ v₀ : Series κ) (m : ℕ),

      FormalODModule.IsODHom (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X u₀ ∧
      FormalODModule.IsODHom (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X v₀ ∧
      v₀.comp u₀ = Series.id κ ∧ u₀.comp v₀ = Series.id κ ∧
      ((t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).Xbar.act ((p : Zp2 p) ^ (m + (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).n))).comp ((u₀.map (Ideal.Quotient.mk (pIdeal p κ))).comp (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).ρ)
        = ((t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).Xbar.act ((p : Zp2 p) ^ (m + (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).n))).comp (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).ρ ∧
      ∃ Λ : t.X.Lie ≃ₗ[DualNumber κ] t'.X.Lie,

        (∀ s : Q.T₀, Λ ((σ₀ s : ↥(t.X.lieZero (structureMap ι ψR))) : t.X.Lie) =
          ((σ₀' (I.τ₀ s) : ↥(t'.X.lieZero (structureMap ι ψR))) : t'.X.Lie)) ∧
        (∀ s : Q.T₁, Λ ((σ₁ s : ↥(t.X.lieOne (structureMap ι ψR))) : t.X.Lie) =
          ((σ₁' (I.τ₁ s) : ↥(t'.X.lieOne (structureMap ι ψR))) : t'.X.Lie)) ∧

        Submodule.map Λ.toLinearMap (t.X.lieZero (structureMap ι ψR)) = t'.X.lieZero (structureMap ι ψR) ∧
        Submodule.map Λ.toLinearMap (t.X.lieOne (structureMap ι ψR)) = t'.X.lieOne (structureMap ι ψR) ∧
        (∀ w : t.X.Lie, Λ (t.X.lieVarpi w) = t'.X.lieVarpi (Λ w)) ∧

        (∀ (w : t.X.Lie) (i : Fin 2), TrivSqZeroExt.fst (Λ w i) =
          (Matrix.mulVecLin (MvFormalGroup.linearPart u₀) (fun j => TrivSqZeroExt.fst (w j))) i) := by
  classical

  obtain ⟨u₀, v₀, m, hu₀, hv₀, hvu, huv, hρ⟩ := hred

  obtain ⟨Λ, hΛ₀, hΛ₁, hΛ0, hΛ1, hΛPi⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_lie_transport p ι hcΦ rΦ ψR t t' ht ht'
      Q Q' σ₀ σ₁ hQ σ₀' σ₁' hQ' I
  refine ⟨u₀, v₀, m, hu₀, hv₀, hvu, huv, hρ, Λ, hΛ₀, hΛ₁, hΛ0, hΛ1, hΛPi, ?_⟩

  have hκ : IsNilpotent (p : κ) := by
    obtain ⟨n, hn⟩ := hR
    refine ⟨n, ?_⟩
    have := congrArg (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ) hn
    rwa [map_pow, map_natCast, map_zero] at this
  have hF : (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR = (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR := rfl
  have htb : (t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)).IsAdmissible ι ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι ψR (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ) t ht
  have htb' : (t'.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)).IsAdmissible ι ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι ψR (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ) t' ht'
  have h0' : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi :=
    fun m hm => LinearMap.mem_ker.mpr (h0 m hm)
  obtain ⟨LΦ, hLΦ⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
      p k ι Φ hΦ hcΦ

  obtain ⟨Qb, hQb⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_isCartierQuadruple_of_isAdmissible_of_lieVarpi_eq_zero_wittVector
      p k ι Φ hΦ hΦ4 h0' hcΦ rΦ ⟨LΦ, hLΦ⟩ hrΦ ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) hκ (t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) htb
  obtain ⟨hODb, σb₀, σb₁, hQbv⟩ :=
    (CerednikDrinfeld.SpecialFormal.Rigidified.isCartierQuadruple_iff_exists_via ι hcΦ rΦ ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR)
      (t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) Qb).mp hQb

  obtain ⟨ρ₀, ρ₁, hQbv', hρ₀, hρ₁⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_via_linearPart_of_isODHom_of_comp_eq
      p ι Φ hΦ hΦ4 hcΦ rΦ hrΦ ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) hκ (t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) (t'.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)) htb htb'
      u₀ v₀ m hu₀ hv₀ hvu huv hρ Qb σb₀ σb₁ hQbv

  obtain ⟨τb₀, τb₁, hsp₀, hsp₁, hτPi₀, hτPi₁, hτσ₀, hτσ₁⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_semilinear_tangent
      p ι Φ hΦ hΦ4 hcΦ rΦ hrΦ ψR hR ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) hκ ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) hF t ht Q σ₀ σ₁ hQ Qb σb₀ σb₁ hQbv
  obtain ⟨τt₀, τt₁, hsp₀', hsp₁', hτPi₀', hτPi₁', hτσ₀', hτσ₁'⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_semilinear_tangent
      p ι Φ hΦ hΦ4 hcΦ rΦ hrΦ ψR hR ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) hκ ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) hF t' ht' Q' σ₀' σ₁' hQ' Qb ρ₀ ρ₁ hQbv'
  obtain ⟨hub₀, hub₁⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.u_baseChange
      p ι Φ hΦ hΦ4 hcΦ rΦ hrΦ ψR hR ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) hκ ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) hF t ht Q σ₀ σ₁ hQ Qb σb₀ σb₁ hQbv
      τb₀ τb₁ ⟨hsp₀, hsp₁, hτPi₀, hτPi₁⟩ ⟨hτσ₀, hτσ₁⟩
  obtain ⟨hut₀, hut₁⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.u_baseChange
      p ι Φ hΦ hΦ4 hcΦ rΦ hrΦ ψR hR ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) hκ ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) hF t' ht' Q' σ₀' σ₁' hQ' Qb ρ₀ ρ₁ hQbv'
      τt₀ τt₁ ⟨hsp₀', hsp₁', hτPi₀', hτPi₁'⟩ ⟨hτσ₀', hτσ₁'⟩

  obtain ⟨bc⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isBaseChangeAlong
      p ι Φ hΦ hΦ4 hcΦ rΦ hrΦ ψR hR ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR) hκ ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) hF t ht Q
      ((CerednikDrinfeld.SpecialFormal.Rigidified.isCartierQuadruple_iff_exists_via ι hcΦ rΦ ψR t Q).mpr
        ⟨hQ.1, σ₀, σ₁, hQ⟩) Qb hQb

  let xb : PrimeSpectrum κ := ⟨⊥, Ideal.bot_prime⟩
  have hunit : ∀ s : DualNumber κ, ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) s ∉ xb.asIdeal → IsUnit s := by
    intro s hs
    have h0 : TrivSqZeroExt.fst s ≠ 0 := fun h => hs (show ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) s ∈ (⊥ : Ideal κ) from (Submodule.mem_bot κ).mpr h)
    exact TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr h0)
  have hne : ∀ c : κ, c ∉ xb.asIdeal → c ≠ 0 := fun c hc h0 => hc ((Submodule.mem_bot κ).mpr h0)
  have key₀ : ∀ s : Q.T₀, τb₀ s = τt₀ (I.τ₀ s) :=
    semilinear_eq_of_u_compat₀ ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) Q Q' Qb I xb hunit
      (fun c hc a b h => smul_right_injective Qb.T₀ (hne c hc) h) (bc.N₀_eq xb) τb₀ τt₀ hub₀ hut₀
  have key₁ : ∀ s : Q.T₁, τb₁ s = τt₁ (I.τ₁ s) :=
    semilinear_eq_of_u_compat₁ ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) Q Q' Qb I xb hunit
      (fun c hc a b h => smul_right_injective Qb.T₁ (hne c hc) h) (bc.N₁_eq xb) τb₁ τt₁ hub₁ hut₁

  have hF_apply : ∀ a : DualNumber κ, (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ) a = TrivSqZeroExt.fst a := fun a => rfl
  have piece₀ : ∀ (s : Q.T₀) (i : Fin 2),
      TrivSqZeroExt.fst (Λ ((σ₀ s : ↥(t.X.lieZero (structureMap ι ψR))) : t.X.Lie) i) =
        (Matrix.mulVecLin (MvFormalGroup.linearPart u₀)
          (fun j => TrivSqZeroExt.fst (((σ₀ s : ↥(t.X.lieZero (structureMap ι ψR))) : t.X.Lie) j))) i := by
    intro s i
    have e1 : (fun j => TrivSqZeroExt.fst (((σ₀ s : ↥(t.X.lieZero (structureMap ι ψR))) : t.X.Lie) j)) =
        ((σb₀ (τb₀ s) : ↥((t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)).X.lieZero (structureMap ι ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR)))) : (t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)).X.Lie) := by
      funext j; rw [hτσ₀ s j]; rfl
    rw [hΛ₀ s, e1, ← hρ₀ (τb₀ s) i, key₀ s, hτσ₀' (I.τ₀ s) i]; rfl
  have piece₁ : ∀ (s : Q.T₁) (i : Fin 2),
      TrivSqZeroExt.fst (Λ ((σ₁ s : ↥(t.X.lieOne (structureMap ι ψR))) : t.X.Lie) i) =
        (Matrix.mulVecLin (MvFormalGroup.linearPart u₀)
          (fun j => TrivSqZeroExt.fst (((σ₁ s : ↥(t.X.lieOne (structureMap ι ψR))) : t.X.Lie) j))) i := by
    intro s i
    have e1 : (fun j => TrivSqZeroExt.fst (((σ₁ s : ↥(t.X.lieOne (structureMap ι ψR))) : t.X.Lie) j)) =
        ((σb₁ (τb₁ s) : ↥((t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)).X.lieOne (structureMap ι ((((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ).comp ψR)))) : (t.map (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p]) : DualNumber κ →+* κ)).X.Lie) := by
      funext j; rw [hτσ₁ s j]; rfl
    rw [hΛ₁ s, e1, ← hρ₁ (τb₁ s) i, key₁ s, hτσ₁' (I.τ₁ s) i]; rfl

  intro w i
  obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl _ _ ht.1.1).surjective w
  obtain ⟨sa, hsa⟩ : ∃ s, σ₀ s = a := σ₀.surjective a
  obtain ⟨sb, hsb⟩ : ∃ s, σ₁ s = b := σ₁.surjective b
  subst hsa hsb
  rw [Submodule.coe_prodEquivOfIsCompl', map_add, Pi.add_apply, TrivSqZeroExt.fst_add, piece₀, piece₁,
    ← Pi.add_apply, ← map_add]
  congr 2

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_linearEquiv_lie_of_iso_of_isIsomorphic_map_fstHom
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_linearEquiv_lie_of_iso_of_isIsomorphic_map_fstHom (solution)
