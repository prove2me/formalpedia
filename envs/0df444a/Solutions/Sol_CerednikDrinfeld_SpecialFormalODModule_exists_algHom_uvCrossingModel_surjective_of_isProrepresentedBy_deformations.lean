-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_algHom_uvCrossingModel_surjective_of_isProrepresentedBy_deformations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/25b1b5e5-072d-57d0-afe8-4b033b075788

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_of_free
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_and_isIso_map_of_forall_apply_eq
import Theorems.Thm_ModularCurve_UVCrossingModel_existsUnique_algHom_apply_U_eq_apply_V_eq_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit
import Theorems.Thm_ModularCurve_UVCrossingModel_maximalIdeal_eq_span_pair
import Theorems.Thm_ModularCurve_UVCrossingModel_isAdicComplete_maximalIdeal
import Theorems.Thm_IsRegularLocalRing_mvPowerSeries_fin
import Theorems.Thm_IsRegularLocalRing_quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
import Theorems.Thm_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_algHom_forall_exists_isIso_of_isAdicComplete_of_isProrepresentedBy_deformations
import Theorems.Thm_CerednikDrinfeld_FormalODModule_linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants
import Theorems.Thm_IsLocalRing_surjective_of_isAdicComplete_of_maximalIdeal_le_map_sup_sq
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_lieCoordinates_mul_eq_of_isProrepresentedBy_deformations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_algHom_uvCrossingModel_surjective_of_isProrepresentedBy_deformations
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open IsLocalRing

namespace DDF5

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped Matrix

section Generic
variable {q : ℕ} [Fact q.Prime]
variable {B : Type} [CommRing B] {B' : Type} [CommRing B']

open MvPowerSeries in
theorem linearPart_comp (ψ φ : Series B) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    MvFormalGroup.linearPart (ψ.comp φ) = MvFormalGroup.linearPart ψ * MvFormalGroup.linearPart φ :=
  MvFormalGroup.linearPart_subst hφ ψ

theorem linearPart_map (f : B →+* B') (φ : Series B) :
    MvFormalGroup.linearPart (φ.map f) = (MvFormalGroup.linearPart φ).map f := by
  ext i j
  simp [MvFormalGroup.linearPart, Series.map, MvPowerSeries.coeff_map]

theorem linearPart_id : MvFormalGroup.linearPart (Series.id B) = 1 := by
  unfold Series.id
  exact MvFormalGroup.linearPart_X

theorem mem_lieZero_iff (j : Zp2 q →+* B) (X : FormalODModule q B) (m : X.Lie) :
    m ∈ X.lieZero j ↔ ∀ a, MvFormalGroup.linearPart (X.act a) *ᵥ m = j a • m := by
  simp only [FormalODModule.lieZero, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, FormalODModule.lieAct, Matrix.mulVecLin_apply]

theorem mem_lieOne_iff (j : Zp2 q →+* B) (X : FormalODModule q B) (m : X.Lie) :
    m ∈ X.lieOne j ↔
      ∀ a, MvFormalGroup.linearPart (X.act a) *ᵥ m = j (WittVector.frobenius a) • m := by
  simp only [FormalODModule.lieOne, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, FormalODModule.lieAct, Matrix.mulVecLin_apply]

theorem frob_frob (a : Zp2 q) : WittVector.frobenius (WittVector.frobenius a) = a := by
  letI : Fintype (GaloisField q 2) := Fintype.ofFinite _
  ext n
  simp only [WittVector.coeff_frobenius_charP]
  rw [← pow_mul, ← pow_two, ← GaloisField.card q 2 two_ne_zero, Nat.card_eq_fintype_card,
    FiniteField.pow_card]

theorem linearPart_varpi_mul_self (X : FormalODModule q B) :
    MvFormalGroup.linearPart X.varpi * MvFormalGroup.linearPart X.varpi =
      ((q : ℕ) : B) • (1 : Matrix (Fin 2) (Fin 2) B) := by
  have h := congrArg MvFormalGroup.linearPart X.varpi_comp_varpi
  rw [linearPart_comp _ _ X.isLawHom_varpi.1, FormalODModule.act_natCast, MvFormalGroup.linearPart_nthSeries] at h
  rw [h]
  ext i i'
  simp [Matrix.smul_apply, nsmul_eq_mul]

theorem linearPart_varpi_mul_act (X : FormalODModule q B) (a : Zp2 q) :
    MvFormalGroup.linearPart X.varpi * MvFormalGroup.linearPart (X.act a) =
      MvFormalGroup.linearPart (X.act (WittVector.frobenius a)) * MvFormalGroup.linearPart X.varpi := by
  have h := congrArg MvFormalGroup.linearPart (X.varpi_comp_act a)
  rwa [linearPart_comp _ _ (X.isLawHom_act a).1, linearPart_comp _ _ X.isLawHom_varpi.1] at h

theorem Hom.linearPart_mul_act {X Y : FormalODModule q B} (w : X.Hom Y) (a : Zp2 q) :
    MvFormalGroup.linearPart w.toSeries * MvFormalGroup.linearPart (X.act a) =
      MvFormalGroup.linearPart (Y.act a) * MvFormalGroup.linearPart w.toSeries := by
  have h := congrArg MvFormalGroup.linearPart (w.isODHom.2.1 a)
  rwa [linearPart_comp _ _ (X.isLawHom_act a).1, linearPart_comp _ _ w.isODHom.1.1] at h

theorem Hom.linearPart_mul_varpi {X Y : FormalODModule q B} (w : X.Hom Y) :
    MvFormalGroup.linearPart w.toSeries * MvFormalGroup.linearPart X.varpi =
      MvFormalGroup.linearPart Y.varpi * MvFormalGroup.linearPart w.toSeries := by
  have h := congrArg MvFormalGroup.linearPart w.isODHom.2.2
  rwa [linearPart_comp _ _ X.isLawHom_varpi.1, linearPart_comp _ _ w.isODHom.1.1] at h

theorem Hom.exists_mul_linearPart_eq_one {X Y : FormalODModule q B} (w : X.Hom Y) (hw : w.IsIso) :
    ∃ W' : Matrix (Fin 2) (Fin 2) B, W' * MvFormalGroup.linearPart w.toSeries = 1 := by
  obtain ⟨g, hg, -⟩ := hw
  refine ⟨MvFormalGroup.linearPart g.toSeries, ?_⟩
  have h := congrArg (fun f : X.Hom X => MvFormalGroup.linearPart f.toSeries) hg
  simp only [FormalODModule.Hom.comp] at h
  rw [linearPart_comp _ _ w.isODHom.1.1] at h
  rw [h]
  exact linearPart_id

theorem Hom.isIso_cast {X X' Y : FormalODModule q B} (h : X = X') (w : X.Hom Y) (hw : w.IsIso) :
    (h ▸ w : X'.Hom Y).IsIso := by
  subst h
  exact hw

end Generic

section MatrixLemmas
variable {R S : Type} [CommRing R] [CommRing S]

theorem map_sub_smul_one (f : R →+* S) (A : Matrix (Fin 2) (Fin 2) R) (c : R) :
    (A - c • (1 : Matrix (Fin 2) (Fin 2) R)).map f = A.map f - f c • (1 : Matrix (Fin 2) (Fin 2) S) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem sub_smul_one_mulVec (A : Matrix (Fin 2) (Fin 2) R) (c : R) (v : Fin 2 → R) :
    (A - c • (1 : Matrix (Fin 2) (Fin 2) R)) *ᵥ v = A *ᵥ v - c • v := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem eq_zero_of_forall_mulVec_eq_zero (A : Matrix (Fin 2) (Fin 2) R) (h : ∀ v, A *ᵥ v = 0) : A = 0 := by
  have : Matrix.toLin' A = 0 := LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v
  exact (LinearEquiv.map_eq_zero_iff Matrix.toLin').mp this

theorem map_mulVec_apply (f : R →+* S) (A : Matrix (Fin 2) (Fin 2) R) (v : Fin 2 → R) (i : Fin 2) :
    f ((A *ᵥ v) i) = (A.map f *ᵥ (f ∘ v)) i :=
  RingHom.map_mulVec f A v i

theorem funext_fin_two {X : Type} {f g : Fin 2 → X} (h0 : f 0 = g 0) (h1 : f 1 = g 1) : f = g := by
  funext i
  exact (Fin.forall_fin_two (p := fun i => f i = g i)).mpr ⟨h0, h1⟩ i

theorem exists_smul_of_det_eq_zero {k : Type} [Field k] (v w : Fin 2 → k) (hv : v ≠ 0)
    (h : v 0 * w 1 - v 1 * w 0 = 0) : ∃ c : k, w = c • v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1; apply hv
      exact funext_fin_two (by simp [h0]) (by simp [h1])
    have hw0 : w 0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left h1
    refine ⟨w 1 / v 1, funext_fin_two ?_ ?_⟩
    · simp [h0, hw0]
    · simp [div_mul_cancel₀ _ h1]
  · refine ⟨w 0 / v 0, funext_fin_two ?_ ?_⟩
    · simp [div_mul_cancel₀ _ h0]
    · simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h

theorem existsUnique_coords (e₀ e₁ : Fin 2 → R) (δinv : R)
    (hδ : δinv * (e₀ 0 * e₁ 1 - e₀ 1 * e₁ 0) = 1) (m : Fin 2 → R) :
    ∃! c : R × R, m = c.1 • e₀ + c.2 • e₁ := by
  refine ⟨(δinv * (m 0 * e₁ 1 - m 1 * e₁ 0), δinv * (e₀ 0 * m 1 - e₀ 1 * m 0)), ?_, ?_⟩
  · refine funext_fin_two ?_ ?_
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(m 0)) * hδ
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(m 1)) * hδ
  · rintro ⟨c₁, c₂⟩ hc
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1
    ext
    · simp only
      linear_combination (-c₁) * hδ - δinv * e₁ 1 * h0 + δinv * e₁ 0 * h1
    · simp only
      linear_combination (-c₂) * hδ + δinv * e₀ 1 * h0 - δinv * e₀ 0 * h1

end MatrixLemmas

section Models

variable {q : ℕ} [Fact q.Prime]
variable (Onr : Type) [CommRing Onr] [IsDomain Onr] [IsDiscreteValuationRing Onr] [Algebra ℤ_[q] Onr]

theorem maximalIdeal_eq_span (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    maximalIdeal Onr = Ideal.span {((q : ℕ) : Onr)} := by
  rw [← IsLocalRing.eq_maximalIdeal hOnr_max, map_natCast]

theorem natCast_ne_zero (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    ((q : ℕ) : Onr) ≠ 0 := by
  intro h
  apply IsDiscreteValuationRing.not_a_field' (R := Onr)
  rw [maximalIdeal_eq_span Onr hOnr_max, h, Ideal.span_singleton_eq_bot]

theorem natCast_mem_maximalIdeal (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    ((q : ℕ) : Onr) ∈ maximalIdeal Onr := by
  rw [maximalIdeal_eq_span Onr hOnr_max]; exact Ideal.subset_span rfl

theorem natCast_not_mem_sq (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    ((q : ℕ) : Onr) ∉ maximalIdeal Onr ^ 2 := by
  intro h
  rw [maximalIdeal_eq_span Onr hOnr_max, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  obtain ⟨r, hr⟩ := h
  have hq := natCast_ne_zero Onr hOnr_max
  have h1 : ((q : ℕ) : Onr) * (1 - (q : Onr) * r) = 0 := by
    rw [mul_sub, mul_one, ← mul_assoc, ← sq, ← hr, sub_self]
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact hq h2
  · have hu : IsUnit ((q : ℕ) : Onr) := IsUnit.of_mul_eq_one r (by rwa [sub_eq_zero, eq_comm] at h2)
    exact (IsLocalRing.mem_maximalIdeal _).mp (natCast_mem_maximalIdeal Onr hOnr_max) hu

theorem isRegularLocalRing_powerSeries : IsRegularLocalRing (PowerSeries Onr) := by
  haveI : IsRegularLocalRing (MvPowerSeries (Fin 1) Onr) := IsRegularLocalRing.mvPowerSeries_fin Onr 1
  exact IsRegularLocalRing.of_ringEquiv
    (MvPowerSeries.renameEquiv Onr finOneEquiv).toRingEquiv

theorem natCast_ne_zero_powerSeries (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    ((q : ℕ) : PowerSeries Onr) ≠ 0 := by
  intro h
  apply natCast_ne_zero Onr hOnr_max
  have h1 : PowerSeries.constantCoeff (R := Onr) ((q : ℕ) : PowerSeries Onr) = 0 := by rw [h, map_zero]
  rwa [map_natCast] at h1

theorem crossing_mem_maximalIdeal (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C ((q : ℕ) : Onr) : MvPowerSeries (Fin 2) Onr) ∈
      maximalIdeal (MvPowerSeries (Fin 2) Onr) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, map_sub, map_mul,
    MvPowerSeries.constantCoeff_X, zero_mul, MvPowerSeries.constantCoeff_C, zero_sub, IsUnit.neg_iff]
  exact (IsLocalRing.mem_maximalIdeal _).mp (natCast_mem_maximalIdeal Onr hOnr_max)

theorem crossing_not_mem_sq (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C ((q : ℕ) : Onr) : MvPowerSeries (Fin 2) Onr) ∉
      maximalIdeal (MvPowerSeries (Fin 2) Onr) ^ 2 := by
  intro h

  set cc : MvPowerSeries (Fin 2) Onr →+* Onr := MvPowerSeries.constantCoeff with hcc
  have hle : Ideal.map cc (maximalIdeal (MvPowerSeries (Fin 2) Onr)) ≤ maximalIdeal Onr := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff] at hx
    exact hx
  have h2 : cc (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C ((q : ℕ) : Onr)) ∈ maximalIdeal Onr ^ 2 := by
    have h3 := Ideal.mem_map_of_mem cc h
    rw [Ideal.map_pow] at h3
    exact Ideal.pow_right_mono hle 2 h3
  rw [hcc, map_sub, map_mul, MvPowerSeries.constantCoeff_X, zero_mul, MvPowerSeries.constantCoeff_C, zero_sub,
    neg_mem_iff] at h2
  exact natCast_not_mem_sq Onr hOnr_max h2

theorem isRegularLocalRing_uvCrossingModel (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    IsRegularLocalRing (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) := by
  haveI : IsRegularLocalRing (MvPowerSeries (Fin 2) Onr) := IsRegularLocalRing.mvPowerSeries_fin Onr 2
  have hmem := crossing_mem_maximalIdeal Onr hOnr_max
  have hne : ModularCurve.uvCrossingIdeal Onr ((q : ℕ) : Onr) ≠ ⊤ := by
    intro htop
    have : (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C ((q : ℕ) : Onr) : MvPowerSeries (Fin 2) Onr) ∈
        maximalIdeal (MvPowerSeries (Fin 2) Onr) := hmem
    apply (maximalIdeal.isMaximal (MvPowerSeries (Fin 2) Onr)).ne_top
    rw [eq_top_iff, ← htop, Ideal.span_le, Set.singleton_subset_iff]
    exact this
  haveI : Nontrivial (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) := Ideal.Quotient.nontrivial_iff.mpr hne
  haveI : IsLocalRing (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  refine (IsRegularLocalRing.quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
    (MvPowerSeries (Fin 2) Onr) hmem (crossing_not_mem_sq Onr hOnr_max) ?_).1
  intro p hp
  have hp' : p = ⊥ := by
    have : p ∈ (⊥ : Ideal (MvPowerSeries (Fin 2) Onr)).minimalPrimes := hp
    rw [Ideal.minimalPrimes_eq_subsingleton_self] at this
    exact this
  rw [hp', Ideal.mem_bot, sub_eq_zero]
  intro h
  have h1 := congrArg (MvPowerSeries.constantCoeff (σ := Fin 2) (R := Onr)) h
  rw [map_mul, MvPowerSeries.constantCoeff_X, zero_mul, MvPowerSeries.constantCoeff_C] at h1
  exact natCast_ne_zero Onr hOnr_max h1.symm

theorem natCast_ne_zero_uvCrossingModel (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal) :
    ((q : ℕ) : ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) ≠ 0 := by
  haveI := isRegularLocalRing_uvCrossingModel Onr hOnr_max
  have hq : ((q : ℕ) : Onr) ∈ nonZeroDivisors Onr := mem_nonZeroDivisors_of_ne_zero (natCast_ne_zero Onr hOnr_max)
  have h := ModularCurve.UVCrossingModel.const_mem_nonZeroDivisors hq
  have hc : ModularCurve.UVCrossingModel.const ((q : ℕ) : Onr) ((q : ℕ) : Onr) =
      ((q : ℕ) : ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) := by
    show Ideal.Quotient.mk _ (MvPowerSeries.C ((q : ℕ) : Onr)) = _
    rw [map_natCast, map_natCast]
  rw [hc] at h
  exact nonZeroDivisors.ne_zero h

end Models

section Eigen
variable {A : Type} [CommRing A]

theorem eigen_coords (t₀ t₁ : Fin 2 → A) (δinv : A) (hδ : δinv * (t₀ 0 * t₁ 1 - t₀ 1 * t₁ 0) = 1)
    (T : Matrix (Fin 2) (Fin 2) A) (lam μ : A) (ht₀ : T *ᵥ t₀ = lam • t₀) (ht₁ : T *ᵥ t₁ = μ • t₁)
    (dinv : A) (hd : dinv * (lam - μ) = 1) (x : Fin 2 → A) :
    (T *ᵥ x = lam • x → ∃ α : A, x = α • t₀) ∧ (T *ᵥ x = μ • x → ∃ δ : A, x = δ • t₁) := by
  obtain ⟨⟨α, β⟩, hx, huniq⟩ := existsUnique_coords t₀ t₁ δinv hδ x
  have hcoord : ∀ a b : A, a • t₀ + b • t₁ = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    obtain ⟨c, -, hc⟩ := existsUnique_coords t₀ t₁ δinv hδ (0 : Fin 2 → A)
    have h1 := hc (a, b) hab.symm
    have h2 := hc (0, 0) (by simp)
    have := h1.trans h2.symm
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  simp only at hx
  constructor
  · intro hT
    rw [hx, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, ht₀, ht₁, smul_add, smul_smul, smul_smul,
      smul_smul, smul_smul] at hT

    have h0 : (0 : A) • t₀ + (β * (μ - lam)) • t₁ = 0 := by
      have := sub_eq_zero.mpr hT
      rw [show α * lam = lam * α from mul_comm _ _] at this
      calc (0 : A) • t₀ + (β * (μ - lam)) • t₁
          = (α * lam) • t₀ + (β * μ) • t₁ - ((lam * α) • t₀ + (lam * β) • t₁) := by
            rw [mul_comm lam α]; simp only [mul_sub, sub_smul, zero_smul, zero_add, mul_comm lam β]; abel
        _ = 0 := by rw [mul_comm α lam]; exact this
    have hβ : β * (μ - lam) = 0 := (hcoord _ _ h0).2
    have hβ0 : β = 0 := by
      have : β * (μ - lam) * (-dinv) = 0 := by rw [hβ, zero_mul]
      rw [show β * (μ - lam) * -dinv = β * (dinv * (lam - μ)) by ring, hd, mul_one] at this
      exact this
    exact ⟨α, by rw [hx, hβ0, zero_smul, add_zero]⟩
  · intro hT
    rw [hx, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, ht₀, ht₁, smul_add, smul_smul, smul_smul,
      smul_smul, smul_smul] at hT
    have h0 : (α * (lam - μ)) • t₀ + (0 : A) • t₁ = 0 := by
      have := sub_eq_zero.mpr hT
      calc (α * (lam - μ)) • t₀ + (0 : A) • t₁
          = (α * lam) • t₀ + (β * μ) • t₁ - ((μ * α) • t₀ + (μ * β) • t₁) := by
            simp only [mul_sub, sub_smul, zero_smul, add_zero, mul_comm μ α, mul_comm μ β]; abel
        _ = 0 := this
    have hα : α * (lam - μ) = 0 := (hcoord _ _ h0).1
    have hα0 : α = 0 := by
      have : α * (lam - μ) * dinv = 0 := by rw [hα, zero_mul]
      rw [show α * (lam - μ) * dinv = α * (dinv * (lam - μ)) by ring, hd, mul_one] at this
      exact this
    exact ⟨β, by rw [hx, hα0, zero_smul, zero_add]⟩

end Eigen

theorem exists_teichmuller_ne {q : ℕ} [Fact q.Prime] {k : Type} [Field k] [CharP k q]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀) :
    ∃ c : GaloisField q 2, j₀ (WittVector.teichmuller q c) ≠ j₀ (WittVector.teichmuller q (c ^ q)) := by
  by_contra hall
  push Not at hall
  have hp0 : j₀ (q : Zp2 q) = 0 := by rw [map_natCast, CharP.cast_eq_zero]
  have hred : ∀ a : Zp2 q, j₀ a = j₀ (WittVector.teichmuller q (a.coeff 0)) := by
    intro a
    have hb0 : (a - WittVector.teichmuller q (a.coeff 0)).coeff 0 = 0 := by
      have h := WittVector.add_coeff_zero (WittVector.teichmuller q (a.coeff 0)) (a - WittVector.teichmuller q (a.coeff 0))
      rw [WittVector.teichmuller_coeff_zero, add_sub_cancel] at h
      linear_combination -h
    have hbp : a - WittVector.teichmuller q (a.coeff 0) ∈ Ideal.span {(q : Zp2 q)} :=
      (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr hb0
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hbp
    have : a = WittVector.teichmuller q (a.coeff 0) + y * (q : Zp2 q) := by rw [hy]; abel
    nth_rw 1 [this]
    rw [map_add, map_mul, hp0, mul_zero, add_zero]
  have hinv : ∀ a : Zp2 q, j₀ a = j₀ (WittVector.frobenius a) := by
    intro a
    rw [hred a, hred (WittVector.frobenius a), WittVector.coeff_frobenius_charP, ← hall]
  have hEq : X₀.toFormalODModule.lieZero j₀ = X₀.toFormalODModule.lieOne j₀ := by
    ext m
    rw [mem_lieZero_iff, mem_lieOne_iff]
    exact forall_congr' fun a => by rw [hinv a]
  have hcpl := X₀.isSpecial.1
  rw [hEq] at hcpl
  have h1 : X₀.toFormalODModule.lieOne j₀ = ⊥ := by simpa using hcpl.inf_eq_bot
  have h2 : X₀.toFormalODModule.lieOne j₀ = ⊤ := by simpa using hcpl.sup_eq_top
  exact absurd (h1.symm.trans h2) bot_ne_top

theorem cot_key {A : Type} [CommRing A] (W G L L' Af At : Matrix (Fin 2) (Fin 2) A)
    (hGW : G * W = 1) (hWG : W * G = 1) (hWL : W * L = L' * W) (hWA : W * Af = At * W)
    (f₀ f₁ t₀ t₁ : Fin 2 → A) (δF : A) (hδF : δF * (f₀ 0 * f₁ 1 - f₀ 1 * f₁ 0) = 1)
    (δT : A) (hδT : δT * (t₀ 0 * t₁ 1 - t₀ 1 * t₁ 0) = 1)
    (u v U V lam μ dinv : A) (hd : dinv * (lam - μ) = 1)
    (hLf₀ : L *ᵥ f₀ = u • f₁) (hLf₁ : L *ᵥ f₁ = v • f₀) (hLt₀ : L' *ᵥ t₀ = U • t₁) (hLt₁ : L' *ᵥ t₁ = V • t₀)
    (hAf₀ : Af *ᵥ f₀ = lam • f₀) (hAf₁ : Af *ᵥ f₁ = μ • f₁) (hAt₀ : At *ᵥ t₀ = lam • t₀) (hAt₁ : At *ᵥ t₁ = μ • t₁) :
    ∃ r s : A, U = r * u ∧ V = s * v := by
  have hGA : G * At = Af * G := by
    calc G * At = G * At * (W * G) := by rw [hWG, mul_one]
      _ = G * (At * W) * G := by simp only [mul_assoc]
      _ = G * (W * Af) * G := by rw [hWA]
      _ = (G * W) * Af * G := by simp only [mul_assoc]
      _ = Af * G := by rw [hGW, one_mul]
  have hcoordT : ∀ a b : A, a • t₀ + b • t₁ = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    obtain ⟨c, -, hc⟩ := existsUnique_coords t₀ t₁ δT hδT (0 : Fin 2 → A)
    have := (hc (a, b) hab.symm).trans (hc (0, 0) (by simp)).symm
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

  obtain ⟨α, hα⟩ := (eigen_coords t₀ t₁ δT hδT At lam μ hAt₀ hAt₁ dinv hd (W *ᵥ f₀)).1
    (by rw [Matrix.mulVec_mulVec, ← hWA, ← Matrix.mulVec_mulVec, hAf₀, Matrix.mulVec_smul])
  obtain ⟨δ, hδ⟩ := (eigen_coords t₀ t₁ δT hδT At lam μ hAt₀ hAt₁ dinv hd (W *ᵥ f₁)).2
    (by rw [Matrix.mulVec_mulVec, ← hWA, ← Matrix.mulVec_mulVec, hAf₁, Matrix.mulVec_smul])

  obtain ⟨α', hα'⟩ := (eigen_coords f₀ f₁ δF hδF Af lam μ hAf₀ hAf₁ dinv hd (G *ᵥ t₀)).1
    (by rw [Matrix.mulVec_mulVec, ← hGA, ← Matrix.mulVec_mulVec, hAt₀, Matrix.mulVec_smul])
  obtain ⟨δ', hδ'⟩ := (eigen_coords f₀ f₁ δF hδF Af lam μ hAf₀ hAf₁ dinv hd (G *ᵥ t₁)).2
    (by rw [Matrix.mulVec_mulVec, ← hGA, ← Matrix.mulVec_mulVec, hAt₁, Matrix.mulVec_smul])

  have h1 : α' * α = 1 := by
    have ht : t₀ = (α' * α) • t₀ := by
      calc t₀ = (W * G) *ᵥ t₀ := by rw [hWG, Matrix.one_mulVec]
        _ = (α' * α) • t₀ := by rw [← Matrix.mulVec_mulVec, hα', Matrix.mulVec_smul, hα, smul_smul]
    have := (hcoordT (α' * α - 1) 0 (by rw [sub_smul, one_smul, ← ht, sub_self, zero_smul, add_zero])).1
    exact sub_eq_zero.mp this
  have h2 : δ' * δ = 1 := by
    have ht : t₁ = (δ' * δ) • t₁ := by
      calc t₁ = (W * G) *ᵥ t₁ := by rw [hWG, Matrix.one_mulVec]
        _ = (δ' * δ) • t₁ := by rw [← Matrix.mulVec_mulVec, hδ', Matrix.mulVec_smul, hδ, smul_smul]
    have := (hcoordT 0 (δ' * δ - 1) (by rw [sub_smul, one_smul, ← ht, sub_self, zero_smul, zero_add])).2
    exact sub_eq_zero.mp this

  have hU : α * U = u * δ := by
    have e : L' *ᵥ (W *ᵥ f₀) = W *ᵥ (L *ᵥ f₀) := by rw [Matrix.mulVec_mulVec, ← hWL, Matrix.mulVec_mulVec]
    rw [hα, Matrix.mulVec_smul, hLt₀, hLf₀, Matrix.mulVec_smul, hδ, smul_smul, smul_smul] at e
    have := (hcoordT 0 (α * U - u * δ) (by rw [sub_smul, e, sub_self, zero_smul, zero_add])).2
    exact sub_eq_zero.mp this
  have hV : δ * V = v * α := by
    have e : L' *ᵥ (W *ᵥ f₁) = W *ᵥ (L *ᵥ f₁) := by rw [Matrix.mulVec_mulVec, ← hWL, Matrix.mulVec_mulVec]
    rw [hδ, Matrix.mulVec_smul, hLt₁, hLf₁, Matrix.mulVec_smul, hα, smul_smul, smul_smul] at e
    have := (hcoordT (δ * V - v * α) 0 (by rw [sub_smul, e, sub_self, zero_smul, add_zero])).1
    exact sub_eq_zero.mp this
  refine ⟨α' * δ, δ' * α, ?_, ?_⟩
  · calc U = (α' * α) * U := by rw [h1, one_mul]
      _ = α' * (α * U) := by ring
      _ = α' * δ * u := by rw [hU]; ring
  · calc V = (δ' * δ) * V := by rw [h2, one_mul]
      _ = δ' * (δ * V) := by ring
      _ = δ' * α * v := by rw [hV]; ring

section Transport
variable {R' A : Type} [CommRing R'] [CommRing A]
open scoped Matrix

theorem push_eigen (ψ : R' →+* A) (M : Matrix (Fin 2) (Fin 2) R') (x y : Fin 2 → R') (c : R')
    (h : M *ᵥ x = c • y) : M.map ψ *ᵥ ((ψ : R' → A) ∘ x) = ψ c • ((ψ : R' → A) ∘ y) := by
  funext i
  rw [← RingHom.map_mulVec, h]
  simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_mul]

theorem exists_inv_det_map (ψ : R' →+* A) (e₀ e₁ : Fin 2 → R') (h : IsUnit (e₀ 0 * e₁ 1 - e₀ 1 * e₁ 0)) :
    ∃ δ : A, δ * (((ψ : R' → A) ∘ e₀) 0 * ((ψ : R' → A) ∘ e₁) 1 - ((ψ : R' → A) ∘ e₀) 1 * ((ψ : R' → A) ∘ e₁) 0) = 1 := by
  obtain ⟨δ, hδ⟩ := (h.map ψ).exists_left_inv
  refine ⟨δ, ?_⟩
  simp only [Function.comp_apply]
  rw [map_sub, map_mul, map_mul] at hδ
  exact hδ

theorem isUnit_det_of_existsUnique (e₀ e₁ : Fin 2 → R')
    (hbasis : ∀ m : Fin 2 → R', ∃! c : R' × R', m = c.1 • e₀ + c.2 • e₁) :
    IsUnit (e₀ 0 * e₁ 1 - e₀ 1 * e₁ 0) := by
  obtain ⟨⟨c₁, c₂⟩, hc, -⟩ := hbasis (Pi.single 0 1)
  obtain ⟨⟨d₁, d₂⟩, hd, -⟩ := hbasis (Pi.single 1 1)
  have h1 := congrFun hc 0; have h2 := congrFun hc 1; have h3 := congrFun hd 0; have h4 := congrFun hd 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
    Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide)] at h1 h2 h3 h4
  refine isUnit_iff_exists_inv.mpr ⟨c₁ * d₂ - d₁ * c₂, ?_⟩
  have key : (e₀ 0 * e₁ 1 - e₀ 1 * e₁ 0) * (c₁ * d₂ - d₁ * c₂) =
      (c₁ * e₀ 0 + c₂ * e₁ 0) * (d₁ * e₀ 1 + d₂ * e₁ 1) - (c₁ * e₀ 1 + c₂ * e₁ 1) * (d₁ * e₀ 0 + d₂ * e₁ 0) := by
    ring
  rw [key, ← h1, ← h2, ← h3, ← h4]; ring

theorem mem_map_sup_of_mk_eq {R'' S' : Type} [CommRing R''] [CommRing S'] (χ : R'' →+* S') (J : Ideal S') (M : Ideal R'')
    (x : S') (y : R'') (hy : y ∈ M) (r : S' ⧸ J)
    (h : Ideal.Quotient.mk J x = r * Ideal.Quotient.mk J (χ y)) : x ∈ M.map χ ⊔ J := by
  obtain ⟨r₀, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hx' : x - r₀ * χ y ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, h, sub_self]
  have hx : x = r₀ * χ y + (x - r₀ * χ y) := by ring
  rw [hx]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hy)) hx'

end Transport

section Key
variable {q : ℕ} [Fact q.Prime]
open scoped Matrix

theorem hsurj_key {R' S' A : Type} [CommRing R'] [CommRing S'] [CommRing A]
    (XR : FormalODModule q R') (XS : FormalODModule q S') (ψ : R' →+* A) (π : S' →+* A)
    (w : (XR.map ψ).Hom (XS.map π)) (hw : w.IsIso)
    (e₀ e₁ : Fin 2 → R') (uu vv : R') (hdetE : IsUnit (e₀ 0 * e₁ 1 - e₀ 1 * e₁ 0))
    (hu : MvFormalGroup.linearPart XR.varpi *ᵥ e₀ = uu • e₁) (hv : MvFormalGroup.linearPart XR.varpi *ᵥ e₁ = vv • e₀)
    (a : Zp2 q) (lR mR : R')
    (hAe₀ : MvFormalGroup.linearPart (XR.act a) *ᵥ e₀ = lR • e₀) (hAe₁ : MvFormalGroup.linearPart (XR.act a) *ᵥ e₁ = mR • e₁)
    (t₀ t₁ : Fin 2 → S') (U V : S') (hdetT : IsUnit (t₀ 0 * t₁ 1 - t₀ 1 * t₁ 0))
    (hLt₀ : MvFormalGroup.linearPart XS.varpi *ᵥ t₀ = U • t₁) (hLt₁ : MvFormalGroup.linearPart XS.varpi *ᵥ t₁ = V • t₀)
    (lS mS : S')
    (hAt₀ : MvFormalGroup.linearPart (XS.act a) *ᵥ t₀ = lS • t₀) (hAt₁ : MvFormalGroup.linearPart (XS.act a) *ᵥ t₁ = mS • t₁)
    (hl : ψ lR = π lS) (hm : ψ mR = π mS) (dinv : A) (hd : dinv * (π lS - π mS) = 1) :
    ∃ r s : A, π U = r * ψ uu ∧ π V = s * ψ vv := by
  obtain ⟨g, hg₁, hg₂⟩ := hw
  have hgw : g.toSeries.comp w.toSeries = Series.id _ := congrArg FormalODModule.Hom.toSeries hg₁
  have hwg : w.toSeries.comp g.toSeries = Series.id _ := congrArg FormalODModule.Hom.toSeries hg₂
  have hGW : MvFormalGroup.linearPart g.toSeries * MvFormalGroup.linearPart w.toSeries = 1 := by
    have h := congrArg MvFormalGroup.linearPart hgw
    rwa [linearPart_comp _ _ w.isODHom.1.1, linearPart_id] at h
  have hWG : MvFormalGroup.linearPart w.toSeries * MvFormalGroup.linearPart g.toSeries = 1 := by
    have h := congrArg MvFormalGroup.linearPart hwg
    rwa [linearPart_comp _ _ g.isODHom.1.1, linearPart_id] at h
  have hWL := Hom.linearPart_mul_varpi w
  have hWA := Hom.linearPart_mul_act w a
  rw [FormalODModule.map_varpi, FormalODModule.map_varpi, linearPart_map, linearPart_map] at hWL
  rw [FormalODModule.map_act, FormalODModule.map_act, linearPart_map, linearPart_map] at hWA
  obtain ⟨δF, hδF⟩ := exists_inv_det_map ψ e₀ e₁ hdetE
  obtain ⟨δT, hδT⟩ := exists_inv_det_map π t₀ t₁ hdetT
  have hLf₀ := push_eigen ψ _ e₀ e₁ uu hu
  have hLf₁ := push_eigen ψ _ e₁ e₀ vv hv
  have hAf₀ := push_eigen ψ _ e₀ e₀ lR hAe₀
  have hAf₁ := push_eigen ψ _ e₁ e₁ mR hAe₁
  have hLt₀' := push_eigen π _ t₀ t₁ U hLt₀
  have hLt₁' := push_eigen π _ t₁ t₀ V hLt₁
  have hAt₀' := push_eigen π _ t₀ t₀ lS hAt₀
  have hAt₁' := push_eigen π _ t₁ t₁ mS hAt₁
  rw [hl] at hAf₀
  rw [hm] at hAf₁
  exact cot_key _ _ _ _ _ _ hGW hWG hWL hWA _ _ _ _ δF hδF δT hδT (ψ uu) (ψ vv) (π U) (π V) (π lS) (π mS) dinv hd
    hLf₀ hLf₁ hLt₀' hLt₁' hAf₀ hAf₁ hAt₀' hAt₁'

end Key

end DDF5

open DDF5 in
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
open scoped Matrix in
theorem solution
    {q : ℕ} [Fact q.Prime]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [IsDiscreteValuationRing Onr] [CharZero Onr] [Algebra ℤ_[q] Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}) Onr)
    (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal)
    [IsAlgClosed (IsLocalRing.ResidueField Onr)]
    (ι : Zp2 q →+* Onr) (X₀ : SpecialFormalODModule q ((IsLocalRing.residue Onr).comp ι))
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra Onr R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (resR : R →+* IsLocalRing.ResidueField Onr) (hresR : resR.comp (algebraMap Onr R) = IsLocalRing.residue Onr)
    (Xu : FormalODModule q R) (wu : (Xu.map resR).Hom X₀.toFormalODModule) (hwu : wu.IsIso)
    (hPRO : (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra Onr A]
            (resA : A →+* IsLocalRing.ResidueField Onr), Function.Surjective resA →
            resA.comp (algebraMap Onr A) = IsLocalRing.residue Onr →
          ∀ (X : FormalODModule q A), X.IsSpecial ((algebraMap Onr A).comp ι) → X.HasHeight 4 →
          ∀ (w : (X.map resA).Hom X₀.toFormalODModule), w.IsIso →
            ∃! χ : R →ₐ[Onr] A, resA.comp χ.toRingHom = resR ∧
              ∃ v : (Xu.map χ.toRingHom).Hom X, v.IsIso ∧
                (w.comp (v.map resA)).toSeries = wu.toSeries))
    (hnode₀ : (∀ m ∈ X₀.toFormalODModule.lieZero ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))
    (hnode₁ : (∀ m ∈ X₀.toFormalODModule.lieOne ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)) :
    ∃ χ : R →ₐ[Onr] ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr), Function.Surjective χ := by
  classical

  have hmax : maximalIdeal Onr = Ideal.span {((q : ℕ) : Onr)} := maximalIdeal_eq_span Onr hOnr_max
  have hqmem : ((q : ℕ) : Onr) ∈ maximalIdeal Onr := natCast_mem_maximalIdeal Onr hOnr_max
  have hqnu : ¬IsUnit ((q : ℕ) : Onr) := (IsLocalRing.mem_maximalIdeal _).mp hqmem
  haveI : IsAdicComplete (maximalIdeal Onr) Onr := by rwa [IsLocalRing.eq_maximalIdeal hOnr_max] at hOnr_complete
  have hqk : ((q : ℕ) : ResidueField Onr) = 0 := by
    have := (IsLocalRing.residue_eq_zero_iff _).mpr hqmem; rwa [map_natCast] at this
  haveI : CharP (ResidueField Onr) q := (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr hqk

  haveI hSloc : IsLocalRing (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) := ModularCurve.UVCrossingModel.isLocalRing_of_not_isUnit hqnu
  haveI : IsRegularLocalRing (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) := isRegularLocalRing_uvCrossingModel Onr hOnr_max
  haveI hSnoeth : IsNoetherianRing (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) := inferInstance
  haveI hScomp : IsAdicComplete (maximalIdeal (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr))) (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) :=
    ModularCurve.UVCrossingModel.isAdicComplete_maximalIdeal ((q : ℕ) : Onr)
  have hmS : maximalIdeal (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) =
      Ideal.span {ModularCurve.UVCrossingModel.U ((q : ℕ) : Onr), ModularCurve.UVCrossingModel.V ((q : ℕ) : Onr)} :=
    ModularCurve.UVCrossingModel.maximalIdeal_eq_span_pair hmax

  letI algk : Algebra Onr (ResidueField Onr) := (IsLocalRing.residue Onr).toAlgebra
  have halgk : ∀ o, algebraMap Onr (ResidueField Onr) o = IsLocalRing.residue Onr o := fun o => rfl
  obtain ⟨φ, ⟨hφU, hφV⟩, -⟩ :=
    ModularCurve.UVCrossingModel.existsUnique_algHom_apply_U_eq_apply_V_eq_of_isAdicComplete
      ((q : ℕ) : Onr) (C := ResidueField Onr) (⊥ : Ideal (ResidueField Onr)) 0 0 (Submodule.zero_mem _)
      (Submodule.zero_mem _) (by rw [zero_mul, halgk, map_natCast, hqk])
  have hφalg : φ.toRingHom.comp (algebraMap Onr (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr))) = IsLocalRing.residue Onr :=
    RingHom.ext fun o => φ.commutes o
  have hφsurj : Function.Surjective φ.toRingHom := fun y => by
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap Onr _ o, φ.commutes o⟩
  have hkerφ : RingHom.ker φ.toRingHom = maximalIdeal (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ.toRingHom hφsurj)

  obtain ⟨γ, hγ⟩ := CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_of_isSpecial_of_free q
    ((IsLocalRing.residue Onr).comp ι) X₀.toFormalODModule X₀.isSpecial inferInstance inferInstance
  obtain ⟨a, ha, h01⟩ := CerednikDrinfeld.FormalODModule.exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis q
    ((IsLocalRing.residue Onr).comp ι) X₀.toFormalODModule γ hγ
  have hPi0 : MvFormalGroup.linearPart X₀.varpi = 0 := by
    apply eq_zero_of_forall_mulVec_eq_zero
    intro m
    have hm : m ∈ X₀.toFormalODModule.lieZero ((IsLocalRing.residue Onr).comp ι) ⊔
        X₀.toFormalODModule.lieOne ((IsLocalRing.residue Onr).comp ι) := by
      rw [X₀.isSpecial.1.sup_eq_top]; trivial
    obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := Submodule.mem_sup.mp hm
    have h0 := hnode₀ y₀ hy₀; have h1 := hnode₁ y₁ hy₁
    rw [Matrix.mulVecLin_apply] at h0 h1
    rw [Matrix.mulVec_add, h0, h1, add_zero]
  have ha0 : ∀ i : Fin 2, a 0 i = 0 := by
    intro i
    have h := CerednikDrinfeld.FormalODModule.linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants q
      X₀.toFormalODModule γ a ha i
    rw [hPi0, Matrix.zero_mulVec] at h

    by_contra hne
    have hz : MvFormalGroup.CartierModule.tangent (γ (CerednikDrinfeld.FormalODModule.piIndex 0 i)) = 0 := by
      have := congrArg (fun w => (a 0 i)⁻¹ • w) h
      simpa [smul_smul, inv_mul_cancel₀ hne] using this.symm
    apply (hγ.2).ne_zero
    have hr : ∀ k, MvFormalGroup.CartierModule.tangent (γ (CerednikDrinfeld.FormalODModule.piIndex 0 i)) k = 0 :=
      fun k => congrFun hz k
    exact Matrix.det_eq_zero_of_row_eq_zero (CerednikDrinfeld.FormalODModule.piIndex 0 i) fun k => by
      rw [Matrix.of_apply]; exact hr k

  let a' : ℕ → Fin 2 → (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) := fun m i =>
    if m = 0 then (if i = 0 then ModularCurve.UVCrossingModel.U ((q : ℕ) : Onr) else ModularCurve.UVCrossingModel.V ((q : ℕ) : Onr))
    else algebraMap Onr _ ((IsLocalRing.residue_surjective (a m i)).choose)
  have ha'00 : a' 0 0 = ModularCurve.UVCrossingModel.U ((q : ℕ) : Onr) := by simp [a']
  have ha'01 : a' 0 1 = ModularCurve.UVCrossingModel.V ((q : ℕ) : Onr) := by simp [a']
  have ha' : ∀ m i, φ.toRingHom (a' m i) = a m i := by
    intro m i
    by_cases hm : m = 0
    · subst hm
      fin_cases i
      · exact (congrArg φ.toRingHom ha'00).trans (hφU.trans (ha0 0).symm)
      · exact (congrArg φ.toRingHom ha'01).trans (hφV.trans (ha0 1).symm)
    · simp only [a', if_neg hm]
      exact (φ.commutes _).trans (IsLocalRing.residue_surjective (a m i)).choose_spec
  have h01' : a' 0 0 * a' 0 1 = ((q : ℕ) : (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr))) := by
    rw [ha'00, ha'01, ← map_natCast (algebraMap Onr (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)))]
    show ModularCurve.UVCrossingModel.mk ((q : ℕ) : Onr) (MvPowerSeries.X 0) *
        ModularCurve.UVCrossingModel.mk ((q : ℕ) : Onr) (MvPowerSeries.X 1) =
      Ideal.Quotient.mk _ (MvPowerSeries.C ((q : ℕ) : Onr))
    rw [← map_mul]
    exact (Ideal.Quotient.eq (I := ModularCurve.uvCrossingIdeal Onr ((q : ℕ) : Onr))).mpr (Ideal.subset_span rfl)

  have hsep : IsHausdorff (Ideal.span {((q : ℕ) : ResidueField Onr)}) (ResidueField Onr) := by
    rw [hqk, Ideal.span_singleton_zero]
    infer_instance
  have hjφ : φ.toRingHom.comp ((algebraMap Onr (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr))).comp ι) = (IsLocalRing.residue Onr).comp ι := by
    rw [← RingHom.comp_assoc, hφalg]
  have hγ' : X₀.toFormalODModule.IsHomogeneousVBasis (φ.toRingHom.comp ((algebraMap Onr (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr))).comp ι)) γ := by
    rw [hjφ]; exact hγ
  obtain ⟨X', γl, hγl, hal, u, hu, -⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_hasStructureConstants_and_isIso_map_of_forall_apply_eq
      q ((algebraMap Onr (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr))).comp ι) φ.toRingHom hsep X₀.toFormalODModule γ hγ' a ha a' ha' h01'

  obtain ⟨χ, hχres, hχn⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_algHom_forall_exists_isIso_of_isAdicComplete_of_isProrepresentedBy_deformations
      Onr hOnr_complete hOnr_max ι X₀ R resR hresR Xu wu hwu hPRO (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) φ.toRingHom hφsurj hφalg X' u hu

  have hsurjR : Function.Surjective resR := by
    intro y; obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap Onr R o, by rw [← RingHom.comp_apply, hresR]⟩
  have hkerR : RingHom.ker resR = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resR hsurjR)

  refine ⟨χ, IsLocalRing.surjective_of_isAdicComplete_of_maximalIdeal_le_map_sup_sq χ.toRingHom ?_ ?_ ?_⟩
  · intro r hr
    rw [← hkerφ, RingHom.mem_ker]
    rw [← hkerR, RingHom.mem_ker] at hr
    change (φ.toRingHom.comp χ.toRingHom) r = 0
    rw [hχres]; exact hr
  · intro s
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (φ.toRingHom s)
    refine ⟨algebraMap Onr R o, ?_⟩
    rw [← hkerφ, RingHom.mem_ker, map_sub, sub_eq_zero]
    change φ s = φ (χ (algebraMap Onr R o))
    rw [AlgHom.commutes, φ.commutes]
    exact ho.symm
  ·

    obtain ⟨e₀, e₁, uu, vv, he₀, he₁, hbasis, hu, hv, -, hum, hvm⟩ :=
      CerednikDrinfeld.SpecialFormalODModule.exists_lieCoordinates_mul_eq_of_isProrepresentedBy_deformations
        Onr hOnr_complete hOnr_max ι X₀ R resR hresR Xu wu hwu hPRO hnode₀ hnode₁
    rw [Matrix.mulVecLin_apply] at hu hv

    have hdetE : IsUnit (e₀ 0 * e₁ 1 - e₀ 1 * e₁ 0) := isUnit_det_of_existsUnique e₀ e₁ hbasis

    obtain ⟨w, hw, -⟩ := hχn 2 two_pos

    obtain ⟨c, hcne⟩ := exists_teichmuller_ne (j₀ := (IsLocalRing.residue Onr).comp ι) X₀
    have hunitS : IsUnit (((algebraMap Onr (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr))).comp ι) (WittVector.teichmuller q c) - ((algebraMap Onr (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr))).comp ι) (WittVector.teichmuller q (c ^ q))) := by
      by_contra hnu
      apply hcne
      have hmem : ((algebraMap Onr (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr))).comp ι) (WittVector.teichmuller q c) - ((algebraMap Onr (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr))).comp ι) (WittVector.teichmuller q (c ^ q)) ∈ maximalIdeal (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) := hnu
      rw [← hkerφ, RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
      rw [RingHom.comp_apply, RingHom.comp_apply, ← halgk, ← halgk, ← φ.commutes, ← φ.commutes]
      exact hmem
    obtain ⟨dinv, hdinv⟩ := (hunitS.map (Ideal.Quotient.mk (maximalIdeal (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) ^ 2))).exists_left_inv
    rw [map_sub] at hdinv

    have hdetT : IsUnit (MvFormalGroup.CartierModule.tangent (γl 0) 0 * MvFormalGroup.CartierModule.tangent (γl 1) 1 -
        MvFormalGroup.CartierModule.tangent (γl 0) 1 * MvFormalGroup.CartierModule.tangent (γl 1) 0) := by
      have h := hγl.2
      rw [Matrix.det_fin_two] at h
      exact h
    have hLt₀ := CerednikDrinfeld.FormalODModule.linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants q X' γl a' hal 0
    have hLt₁ := CerednikDrinfeld.FormalODModule.linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants q X' γl a' hal 1
    rw [ha'00] at hLt₀
    rw [ha'01] at hLt₁
    have hAt : ∀ i : Fin 2,
        MvFormalGroup.linearPart (X'.act (WittVector.teichmuller q c)) *ᵥ MvFormalGroup.CartierModule.tangent (γl i) =
        (((algebraMap Onr (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr))).comp ι) (WittVector.teichmuller q c) ^ q ^ (i : ℕ)) • MvFormalGroup.CartierModule.tangent (γl i) := by
      intro i
      have hmem := (CerednikDrinfeld.FormalODModule.mem_gradedPiece_iff X' ((algebraMap Onr (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr))).comp ι) i (γl i)).mp (hγl.1 i) c
      have ht := congrArg MvFormalGroup.CartierModule.tangent hmem
      rw [MvFormalGroup.CartierModule.endAct_apply, MvFormalGroup.CartierModule.tangent_map,
        CerednikDrinfeld.FormalODModule.actEnd_toPowerSeries, MvFormalGroup.CartierModule.tangent_homothety] at ht
      exact ht
    have hAt₀ := hAt 0
    have hAt₁ := hAt 1
    rw [Fin.val_zero, pow_zero, pow_one] at hAt₀
    rw [Fin.val_one, pow_one, ← map_pow, ← map_pow] at hAt₁

    have hAe₀ := (mem_lieZero_iff _ _ e₀).mp he₀ (WittVector.teichmuller q c)
    have hAe₁ := (mem_lieOne_iff _ _ e₁).mp he₁ (WittVector.teichmuller q c)
    rw [WittVector.frobenius_teichmuller_eq] at hAe₁

    obtain ⟨r, s', hrU, hsV⟩ := hsurj_key Xu X' ((Ideal.Quotient.mk (maximalIdeal (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) ^ 2)).comp χ.toRingHom) (Ideal.Quotient.mk (maximalIdeal (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) ^ 2)) w hw e₀ e₁ uu vv hdetE hu hv
      (WittVector.teichmuller q c) _ _ hAe₀ hAe₁ _ _ _ _ hdetT hLt₀ hLt₁ _ _ hAt₀ hAt₁
      (by simp only [RingHom.comp_apply]; exact congrArg (Ideal.Quotient.mk (maximalIdeal (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) ^ 2)) (χ.commutes _))
      (by simp only [RingHom.comp_apply]; exact congrArg (Ideal.Quotient.mk (maximalIdeal (ModularCurve.UVCrossingModel Onr ((q : ℕ) : Onr)) ^ 2)) (χ.commutes _))
      dinv hdinv

    refine hmS.le.trans ?_
    rw [Ideal.span_le]
    rintro x hx
    rcases hx with rfl | hx
    · exact mem_map_sup_of_mk_eq χ.toRingHom _ _ _ uu hum r hrU
    · rw [Set.mem_singleton_iff] at hx; subst hx
      exact mem_map_sup_of_mk_eq χ.toRingHom _ _ _ vv hvm s' hsV

#print axioms solution

end S_CerednikDrinfeld_SpecialFormalODModule_exists_algHom_uvCrossingModel_surjective_of_isProrepresentedBy_deformations
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_algHom_uvCrossingModel_surjective_of_isProrepresentedBy_deformations (solution)
