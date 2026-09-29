-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.exists_cover_exists_map_eq_map_of_isBaseChange_of_ker_mul_ker_eq_bot_of_lieVarpi_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/78be859b-3b2d-5871-89af-f0421630723f

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
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isIsomorphic_map_of_hasStructureConstants_of_map_eq_of_mul_eq_of_ker_mul_ker_eq_bot
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_exists_cover_forall_exists_mul_eq_and_map_eq_of_isBaseChange
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isCartierQuadruple_of_isAdmissible_of_lieVarpi_eq_zero_wittVector
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_map_of_isSpecial_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsHomogeneousVBasis_tangent_mem_and_existsUnique_smul_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_exists_cover_exists_map_eq_map_of_isBaseChange_of_ker_mul_ker_eq_bot_of_lieVarpi_eq_zero
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType DrinfeldCurve.instAlgebraCoordRing DrinfeldCurve.instCommRingCoordRing CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj DrinfeldCurve.LocalChart.ChartPresentation.mk.sizeOf_spec"
p2m_attr_erase "simp" "DrinfeldCurve.LocalChart.ChartPresentation.mk.injEq"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace ReduceLL2

theorem surjective_loc {R T R₁ T₁ : Type} [CommRing R] [CommRing T] [CommRing R₁] [CommRing T₁]
    [Algebra R R₁] [Algebra T T₁] (φ : R →+* T) (r : R)
    [IsLocalization.Away r R₁] [IsLocalization.Away (φ r) T₁]
    (φ₁ : R₁ →+* T₁) (h : φ₁.comp (algebraMap R R₁) = (algebraMap T T₁).comp φ)
    (hφ : Function.Surjective φ) : Function.Surjective φ₁ := by
  intro y
  obtain ⟨n, a, hy⟩ := IsLocalization.Away.surj (φ r) y
  obtain ⟨b, rfl⟩ := hφ a
  have hu : IsUnit (algebraMap R R₁ r) := IsLocalization.Away.algebraMap_isUnit r
  obtain ⟨u, hu'⟩ := hu
  have hφu : φ₁ (u : R₁) = algebraMap T T₁ (φ r) := by
    rw [hu']; exact RingHom.congr_fun h r
  refine ⟨algebraMap R R₁ b * ((u⁻¹ : R₁ˣ) : R₁) ^ n, ?_⟩
  have hunit : IsUnit (algebraMap T T₁ (φ r) ^ n) := (IsLocalization.Away.algebraMap_isUnit (φ r)).pow n
  rw [← hunit.mul_left_inj, hy, map_mul, map_pow, mul_assoc, ← mul_pow, ← hφu, ← map_mul,
    Units.inv_mul, map_one, one_pow, mul_one]
  exact RingHom.congr_fun h b

theorem ker_loc_le {R T R₁ T₁ : Type} [CommRing R] [CommRing T] [CommRing R₁] [CommRing T₁]
    [Algebra R R₁] [Algebra T T₁] (φ : R →+* T) (r : R)
    [IsLocalization.Away r R₁] [IsLocalization.Away (φ r) T₁]
    (φ₁ : R₁ →+* T₁) (h : φ₁.comp (algebraMap R R₁) = (algebraMap T T₁).comp φ) :
    RingHom.ker φ₁ ≤ Ideal.map (algebraMap R R₁) (RingHom.ker φ) := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  obtain ⟨n, a, hxa⟩ := IsLocalization.Away.surj r x
  have h0 : algebraMap T T₁ (φ a) = algebraMap T T₁ 0 := by
    rw [map_zero, ← RingHom.comp_apply, ← h, RingHom.comp_apply, ← hxa, map_mul, hx, zero_mul]
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (S := T₁) (φ r) h0
  rw [mul_zero, ← map_pow, ← map_mul, ← RingHom.mem_ker] at hm
  have hmem : algebraMap R R₁ (r ^ m * a) ∈ Ideal.map (algebraMap R R₁) (RingHom.ker φ) :=
    Ideal.mem_map_of_mem _ hm
  have hu : IsUnit (algebraMap R R₁ r ^ (m + n)) := (IsLocalization.Away.algebraMap_isUnit r).pow _
  obtain ⟨u, hu'⟩ := hu
  have hx' : x = algebraMap R R₁ (r ^ m * a) * ((u⁻¹ : R₁ˣ) : R₁) := by
    rw [map_mul, map_pow, ← hxa, eq_comm, Units.mul_inv_eq_iff_eq_mul, hu', pow_add]; ring
  rw [hx']
  exact Ideal.mul_mem_right _ _ hmem

theorem ker_mul_ker_eq_bot_loc {R T R₁ T₁ : Type} [CommRing R] [CommRing T] [CommRing R₁] [CommRing T₁]
    [Algebra R R₁] [Algebra T T₁] (φ : R →+* T) (r : R)
    [IsLocalization.Away r R₁] [IsLocalization.Away (φ r) T₁]
    (φ₁ : R₁ →+* T₁) (h : φ₁.comp (algebraMap R R₁) = (algebraMap T T₁).comp φ)
    (hsq : RingHom.ker φ * RingHom.ker φ = ⊥) : RingHom.ker φ₁ * RingHom.ker φ₁ = ⊥ := by
  rw [eq_bot_iff]
  calc RingHom.ker φ₁ * RingHom.ker φ₁
      ≤ Ideal.map (algebraMap R R₁) (RingHom.ker φ) * Ideal.map (algebraMap R R₁) (RingHom.ker φ) :=
        Ideal.mul_mono (ker_loc_le φ r φ₁ h) (ker_loc_le φ r φ₁ h)
    _ = Ideal.map (algebraMap R R₁) (RingHom.ker φ * RingHom.ker φ) := (Ideal.map_mul _ _ _).symm
    _ = ⊥ := by rw [hsq, Ideal.map_bot]
    _ ≤ ⊥ := le_rfl

theorem exists_cover_of_forall_maximal {R : Type} [CommRing R] (P : R → Prop)
    (h : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → ∃ r, r ∉ 𝔪 ∧ P r) :
    ∃ (n : ℕ) (f : Fin n → R), Ideal.span (Set.range f) = ⊤ ∧ ∀ i, P (f i) := by
  classical
  have htop : Ideal.span {r : R | P r} = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hPr⟩ := h 𝔪 h𝔪
    exact hr (hle (Ideal.subset_span hPr))
  have h1 : (1 : R) ∈ Ideal.span {r : R | P r} := by rw [htop]; trivial
  obtain ⟨T, hTS, h1T⟩ := Submodule.mem_span_finite_of_mem_span h1
  refine ⟨T.card, fun i => (T.equivFin.symm i : R), ?_, fun i => hTS (T.equivFin.symm i).2⟩
  have hrange : Set.range (fun i : Fin T.card => ((T.equivFin.symm i) : R)) = (T : Set R) := by
    ext r; constructor
    · rintro ⟨i, rfl⟩; exact (T.equivFin.symm i).2
    · intro hr; exact ⟨T.equivFin ⟨r, hr⟩, by simp⟩
  rw [hrange, Ideal.eq_top_iff_one]
  exact h1T

theorem nil_of_map {q : ℕ} {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (h : IsNilpotent (q : R)) :
    IsNilpotent (q : S) := by
  obtain ⟨n, hn⟩ := h; exact ⟨n, by rw [← map_natCast f, ← map_pow, hn, map_zero]⟩

theorem ker_le_of_isPrime {R T : Type} [CommRing R] [CommRing T] (φ : R →+* T)
    (hsq : RingHom.ker φ * RingHom.ker φ = ⊥) (𝔭 : Ideal R) (h𝔭 : 𝔭.IsPrime) : RingHom.ker φ ≤ 𝔭 := by
  intro y hy
  have : y * y ∈ RingHom.ker φ * RingHom.ker φ := Ideal.mul_mem_mul hy hy
  rw [hsq, Ideal.mem_bot] at this
  exact h𝔭.mem_of_pow_mem 2 (by rw [pow_two, this]; exact 𝔭.zero_mem)

theorem not_mem_of_apply_not_mem_map {R T : Type} [CommRing R] [CommRing T] (φ : R →+* T)
    (𝔪 : Ideal R) (a : R) (h : φ a ∉ Ideal.map φ 𝔪) : a ∉ 𝔪 :=
  fun ha => h (Ideal.mem_map_of_mem φ ha)

theorem isMaximal_map_of_surjective {R T : Type} [CommRing R] [CommRing T] (φ : R →+* T)
    (hφ : Function.Surjective φ) (hsq : RingHom.ker φ * RingHom.ker φ = ⊥)
    (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal) : (Ideal.map φ 𝔪).IsMaximal := by
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective φ hφ h𝔪 with h | h
  · exfalso
    have hc := Ideal.comap_map_of_surjective φ hφ 𝔪
    rw [h, Ideal.comap_top] at hc
    have hk : Ideal.comap φ ⊥ ≤ 𝔪 := by
      rw [← RingHom.ker_eq_comap_bot]; exact ker_le_of_isPrime φ hsq 𝔪 h𝔪.isPrime
    exact h𝔪.ne_top (top_le_iff.mp (hc.le.trans (sup_le le_rfl hk)))
  · exact h

theorem apply_not_mem_map {R T : Type} [CommRing R] [CommRing T] (φ : R →+* T)
    (hφ : Function.Surjective φ) (hsq : RingHom.ker φ * RingHom.ker φ = ⊥)
    (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal) (a : R) (ha : a ∉ 𝔪) : φ a ∉ Ideal.map φ 𝔪 := by
  intro h
  rw [Ideal.mem_map_iff_of_surjective φ hφ] at h
  obtain ⟨m, hm, hma⟩ := h
  have : a - m ∈ RingHom.ker φ := by rw [RingHom.mem_ker, map_sub, hma, sub_self]
  have := ker_le_of_isPrime φ hsq 𝔪 h𝔪.isPrime this
  exact ha (by simpa using 𝔪.add_mem this hm)

theorem isBaseChange_iff_eq_map {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B B' : Type} [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    (d : FormalOmega.DeligneDatum (K := K) π B) (d' : FormalOmega.DeligneDatum (K := K) π B') :
    FormalOmega.DeligneDatum.IsBaseChange (K := K) (π := π) f d d' ↔ d' = d.map π f :=
  ⟨fun h => FormalOmega.DeligneDatum.ext' (funext fun M => (h M).trans ((FormalOmega.DeligneDatum.isBaseChange_map π f d) M).symm),
   fun h => h ▸ FormalOmega.DeligneDatum.isBaseChange_map π f d⟩

theorem dmap_comp {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B₁ B₂ B₃ : Type} [CommRing B₁] [Algebra 𝒪 B₁] [CommRing B₂] [Algebra 𝒪 B₂] [CommRing B₃] [Algebra 𝒪 B₃]
    (f : B₁ →ₐ[𝒪] B₂) (g : B₂ →ₐ[𝒪] B₃) (d : FormalOmega.DeligneDatum (K := K) π B₁) :
    d.map π (g.comp f) = (d.map π f).map π g :=
  (FormalOmega.Omega K π).map_comp f g d

def algHomOf {R S S' : Type} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    (g : S →+* S') (hg : ∀ z : R, g (algebraMap R S z) = algebraMap R S' z) : S →ₐ[R] S' :=
  { toRingHom := g, commutes' := hg }

@[scoped simp] theorem coe_algHomOf {R S S' : Type} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    (g : S →+* S') (hg : ∀ z : R, g (algebraMap R S z) = algebraMap R S' z) :
    (algHomOf g hg : S →+* S') = g := RingHom.ext fun _ => rfl

end ReduceLL2
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_exists_cover_exists_map_eq_map_of_isBaseChange_of_ker_mul_ker_eq_bot_of_lieVarpi_eq_zero.ReduceLL2"

theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0 : ∀ m ∈ Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι), Φ.lieVarpi m = 0)
(M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
(η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
Rigidified p Φ B → M.obj B ψ hB)
(hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
(t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
(η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
(∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
(hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
(hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
(∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
(hL : IsNilpotent (p : L)),
∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
η L ((algebraMap B L).comp ψ) hL t =
M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
(θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
M.obj B ψ hB → OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B)
(hθ : CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap p k ι Φ M η hcΦ rΦ θ)
    :
    (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B']
    [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
    (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
    (φ : B' →ₐ[ℤ_[p]] B) (hφ : (φ : B' →+* B).comp ψ' = ψ) (_hφs : Function.Surjective φ)
    (_hφ2 : RingHom.ker (φ : B' →+* B) * RingHom.ker (φ : B' →+* B) = ⊥)
    (x : M.obj B ψ hB) (d' : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B'),
    DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) φ d' (θ B ψ hB x) →
    ∃ (n : ℕ) (f : Fin n → B'), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L' : Type) [CommRing L'] [IsNoetherianRing L'] [Algebra B' L'] [IsLocalization.Away (f i) L']
        (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (φ (f i)) L]
        (hL' : IsNilpotent (p : L')) (hL : IsNilpotent (p : L))
        (φL : L' →+* L) (_hφL : φL.comp (algebraMap B' L') = (algebraMap B L).comp (φ : B' →+* B))
        (hφLψ : φL.comp ((algebraMap B' L').comp ψ') = (algebraMap B L).comp ψ),
        (M.fibre hL' hL φL hφLψ (M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl x)).Nonempty) := by
  intro B B' _ _ _ _ _ _ ψ ψ' hB hB' φ hφ hφs hφ2 x d' hd'
  classical

  let P : B' → Prop := fun r =>
    ∀ (L' : Type) [CommRing L'] [IsNoetherianRing L'] [Algebra B' L'] [IsLocalization.Away r L']
      (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (φ r) L]
      (hL' : IsNilpotent (p : L')) (hL : IsNilpotent (p : L))
      (φL : L' →+* L) (_hφL : φL.comp (algebraMap B' L') = (algebraMap B L).comp (φ : B' →+* B))
      (hφLψ : φL.comp ((algebraMap B' L').comp ψ') = (algebraMap B L).comp ψ),
      (M.fibre hL' hL φL hφLψ (M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl x)).Nonempty
  suffices hpt : ∀ 𝔪 : Ideal B', 𝔪.IsMaximal → ∃ r, r ∉ 𝔪 ∧ P r by
    obtain ⟨n, f, hf, hP⟩ := ReduceLL2.exists_cover_of_forall_maximal P hpt
    exact ⟨n, f, hf, fun i => hP i⟩
  intro 𝔪 h𝔪
  have hφB : ((φ : B' →+* B)) = (φ : B' →+* B) := rfl

  obtain ⟨n₀, g, hgspan, hgloc⟩ := hη.2.2 B ψ hB x
  set 𝔭 : Ideal B := Ideal.map (φ : B' →+* B) 𝔪 with h𝔭def
  have h𝔭 : 𝔭.IsMaximal := ReduceLL2.isMaximal_map_of_surjective (φ : B' →+* B) hφs hφ2 𝔪 h𝔪
  obtain ⟨j, hj⟩ : ∃ j, g j ∉ 𝔭 := by
    by_contra hall
    push_neg at hall
    have : Ideal.span (Set.range g) ≤ 𝔭 := Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hall j)
    rw [hgspan, top_le_iff] at this
    exact h𝔭.ne_top this

  let L₀ : Type := Localization.Away (g j)
  have hL₀ : IsNilpotent (p : L₀) := ReduceLL2.nil_of_map (algebraMap B L₀) hB
  obtain ⟨t₀, ht₀, hηt₀⟩ := hgloc j L₀ hL₀
  letI algL₀ : Algebra ℤ_[p] L₀ := ((algebraMap B L₀).comp (algebraMap ℤ_[p] B)).toAlgebra

  have hdisj : Disjoint (↑(Submonoid.powers (g j)) : Set B) ↑𝔭 := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hk
    exact hj (h𝔭.isPrime.mem_of_pow_mem k hk)
  let 𝔭₀ : PrimeSpectrum L₀ := ⟨Ideal.map (algebraMap B L₀) 𝔭,
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (g j)) L₀ 𝔭 h𝔭.isPrime hdisj⟩

  obtain ⟨h, hh, γ, hγ⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_map_of_isSpecial_of_isNilpotent p
      (structureMap ι ((algebraMap B L₀).comp ψ)) hL₀ t₀.X ht₀.1 𝔭₀

  obtain ⟨kk, a, hka⟩ := IsLocalization.Away.surj (g j) h
  have ha : a ∉ 𝔭 := by
    intro ha
    have h1 : algebraMap B L₀ a ∈ 𝔭₀.asIdeal := Ideal.mem_map_of_mem _ ha
    rw [← hka] at h1
    rcases (𝔭₀.2.mem_or_mem h1) with h2 | h2
    · exact hh h2
    · have h3 : algebraMap B L₀ (g j) ∈ 𝔭₀.asIdeal := by
        exact 𝔭₀.2.mem_of_pow_mem kk h2
      have h4 : g j ∈ (Ideal.map (algebraMap B L₀) 𝔭).under B := h3
      rw [IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (g j)) L₀ h𝔭.isPrime hdisj] at h4
      exact hj h4
  obtain ⟨a', ha'⟩ := hφs a
  obtain ⟨gj', hgj'⟩ := hφs (g j)
  have ha'e : (φ : B' →+* B) a' = a := ha'
  have hgj'e : (φ : B' →+* B) gj' = g j := hgj'
  have ha'𝔪 : a' ∉ 𝔪 := ReduceLL2.not_mem_of_apply_not_mem_map (φ : B' →+* B) 𝔪 a' (by rw [ha'e]; exact ha)
  have hgj'𝔪 : gj' ∉ 𝔪 := ReduceLL2.not_mem_of_apply_not_mem_map (φ : B' →+* B) 𝔪 gj' (by rw [hgj'e]; exact hj)

  let L₀h : Type := Localization.Away h
  let f₀ : L₀ →+* L₀h := algebraMap L₀ L₀h
  let r₁ : B := g j * a
  let L₁ : Type := Localization.Away r₁
  have hL₁ : IsNilpotent (p : L₁) := ReduceLL2.nil_of_map (algebraMap B L₁) hB
  let ψ₀ : WittVector p k →+* L₀ := (algebraMap B L₀).comp ψ
  let ψ₁ : WittVector p k →+* L₁ := (algebraMap B L₁).comp ψ
  have hu_gj : IsUnit (algebraMap B L₁ (g j)) := IsLocalization.Away.isUnit_of_dvd (x := r₁) ⟨a, rfl⟩
  have hu_a : IsUnit (algebraMap B L₁ a) := IsLocalization.Away.isUnit_of_dvd (x := r₁) ⟨g j, mul_comm _ _⟩
  let e₀₁ : L₀ →+* L₁ := IsLocalization.Away.lift (g j) (g := algebraMap B L₁) hu_gj
  have he₀₁ : e₀₁.comp (algebraMap B L₀) = algebraMap B L₁ := IsLocalization.Away.lift_comp _ _
  have hu_h : IsUnit (e₀₁ h) := by
    have he₀₁' : ∀ b : B, e₀₁ (algebraMap B L₀ b) = algebraMap B L₁ b := fun b => RingHom.congr_fun he₀₁ b
    have e : e₀₁ h * e₀₁ (algebraMap B L₀ (g j)) ^ kk = algebraMap B L₁ a := by
      rw [← map_pow, ← map_mul, hka]; exact he₀₁' a
    exact isUnit_of_mul_isUnit_left (e.symm ▸ hu_a)
  let f₁ : L₀h →+* L₁ := IsLocalization.Away.lift h (g := e₀₁) hu_h
  have hf₁ : f₁.comp f₀ = e₀₁ := IsLocalization.Away.lift_comp _ _
  have hf₁₀ : (f₁.comp f₀).comp (algebraMap B L₀) = algebraMap B L₁ := by rw [hf₁, he₀₁]
  let t₁ : Rigidified p Φ L₁ := (t₀.map f₀).map f₁
  have hj₁ : f₁.comp (f₀.comp (structureMap ι ψ₀)) = structureMap ι ψ₁ := by
    show f₁.comp (f₀.comp (((algebraMap B L₀).comp ψ).comp ι)) = ((algebraMap B L₁).comp ψ).comp ι
    simp only [← RingHom.comp_assoc]
    rw [show ((f₁.comp f₀).comp (algebraMap B L₀)) = algebraMap B L₁ from hf₁₀]
  let γ₁ : Fin 2 → MvFormalGroup.CartierModule p t₁.X.F := fun i => MvFormalGroup.CartierModule.baseChange f₁ (γ i)
  have hγ₁ : t₁.X.IsHomogeneousVBasis (structureMap ι ψ₁) γ₁ := hj₁ ▸ hγ.map f₁
  have ht₁ : t₁.IsAdmissible ι ψ₁ := by
    have h1 := CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι ψ₀ f₀ t₀ ht₀
    have h2 := CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι (f₀.comp ψ₀) f₁ (t₀.map f₀) h1
    have e : f₁.comp (f₀.comp ψ₀) = ψ₁ := by
      show f₁.comp (f₀.comp ((algebraMap B L₀).comp ψ)) = (algebraMap B L₁).comp ψ
      simp only [← RingHom.comp_assoc]; rw [hf₁₀]
    exact e ▸ h2
  have mapIrrel : ∀ {S S' : Type} [CommRing S] [CommRing S'] {χ : WittVector p k →+* S} {χ' : WittVector p k →+* S'}
      (hS : IsNilpotent (p : S)) (hS' : IsNilpotent (p : S')) (u₁ u₂ : S →+* S') (e : u₁ = u₂)
      (p₁ : u₁.comp χ = χ') (p₂ : u₂.comp χ = χ') (y : M.obj S χ hS),
      M.map hS hS' u₁ p₁ y = M.map hS hS' u₂ p₂ y := by
    intro S S' _ _ χ χ' hS hS' u₁ u₂ e p₁ p₂ y; subst e; rfl
  have hηt₁ : η L₁ ψ₁ hL₁ t₁ = M.map (ψ' := ψ₁) hB hL₁ (algebraMap B L₁) rfl x := by
    have hcomp : (f₁.comp f₀).comp ψ₀ = ψ₁ := by
      show (f₁.comp f₀).comp ((algebraMap B L₀).comp ψ) = (algebraMap B L₁).comp ψ
      rw [← RingHom.comp_assoc, hf₁₀]
    have e1 : t₁ = t₀.map (f₁.comp f₀) := (Rigidified.map_comp f₁ f₀ t₀).symm
    rw [e1, hη.2.1 L₀ L₁ ψ₀ ψ₁ hL₀ hL₁ (f₁.comp f₀) hcomp t₀ ht₀, hηt₀,
      ← M.map_comp hB hL₀ hL₁ (f₁.comp f₀) (algebraMap B L₀) rfl hcomp x]
    exact mapIrrel hB hL₁ _ _ hf₁₀ _ rfl x

  obtain ⟨ac, hac, -⟩ :=
    CerednikDrinfeld.FormalODModule.exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis p (structureMap ι ψ₁) t₁.X γ₁ hγ₁
  obtain ⟨⟨hm0, hm1⟩, hu0, hu1, -⟩ :=
    CerednikDrinfeld.FormalODModule.IsHomogeneousVBasis.tangent_mem_and_existsUnique_smul_of_isNilpotent p
      (structureMap ι ψ₁) hL₁ t₁.X γ₁ hγ₁

  letI algL₁ : Algebra ℤ_[p] L₁ := ((algebraMap B L₁).comp (algebraMap ℤ_[p] B)).toAlgebra
  have h0' : Φ.lieZero (Rigidified.jbar ι) ≤ LinearMap.ker Φ.lieVarpi := fun m hm => LinearMap.mem_ker.mpr (h0 m hm)
  obtain ⟨Q, hQ⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_isCartierQuadruple_of_isAdmissible_of_lieVarpi_eq_zero_wittVector p k ι Φ hΦ hΦ4
      h0' hcΦ rΦ
      (CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed p k ι Φ hΦ hcΦ)
      hrΦ ψ₁ hL₁ t₁ ht₁
  let d₁ : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) L₁ := θ L₁ ψ₁ hL₁ (η L₁ ψ₁ hL₁ t₁)
  have hQd : Q.IsQuadrupleOf d₁ := hθ.1 L₁ ψ₁ hL₁ t₁ ht₁ Q hQ
  obtain ⟨-, τ₀, τ₁, hT0, hT1, -⟩ := hQ

  let e₀ : Q.T₀ := τ₀.symm ⟨MvFormalGroup.CartierModule.tangent (γ₁ 0), hm0⟩
  let e₁ : Q.T₁ := τ₁.symm ⟨MvFormalGroup.CartierModule.tangent (γ₁ 1), hm1⟩
  have hτe₀ : τ₀ e₀ = ⟨MvFormalGroup.CartierModule.tangent (γ₁ 0), hm0⟩ := LinearEquiv.apply_symm_apply _ _
  have hτe₁ : τ₁ e₁ = ⟨MvFormalGroup.CartierModule.tangent (γ₁ 1), hm1⟩ := LinearEquiv.apply_symm_apply _ _
  have he₀ : ∀ s : Q.T₀, ∃! b : L₁, s = b • e₀ := by
    intro s
    obtain ⟨b, hb, huniq⟩ := hu0 (τ₀ s : t₁.X.Lie) (τ₀ s).2
    refine ⟨b, ?_, fun b' hb' => huniq b' ?_⟩
    · apply τ₀.injective
      rw [map_smul, hτe₀]
      exact Subtype.ext (by rw [Submodule.coe_smul]; exact hb)
    · have e := congrArg (fun z : Q.T₀ => ((τ₀ z : ↥(t₁.X.lieZero (structureMap ι ψ₁))) : t₁.X.Lie)) hb'
      simp only [map_smul, Submodule.coe_smul, hτe₀] at e
      exact e
  have he₁ : ∀ s : Q.T₁, ∃! b : L₁, s = b • e₁ := by
    intro s
    obtain ⟨b, hb, huniq⟩ := hu1 (τ₁ s : t₁.X.Lie) (τ₁ s).2
    refine ⟨b, ?_, fun b' hb' => huniq b' ?_⟩
    · apply τ₁.injective
      rw [map_smul, hτe₁]
      exact Subtype.ext (by rw [Submodule.coe_smul]; exact hb)
    · have e := congrArg (fun z : Q.T₁ => ((τ₁ z : ↥(t₁.X.lieOne (structureMap ι ψ₁))) : t₁.X.Lie)) hb'
      simp only [map_smul, Submodule.coe_smul, hτe₁] at e
      exact e
  have hLRC := CerednikDrinfeld.FormalODModule.linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants p t₁.X γ₁ ac hac
  have hpi0 : CerednikDrinfeld.FormalODModule.piIndex 0 0 = 1 := rfl
  have hpi1 : CerednikDrinfeld.FormalODModule.piIndex 0 1 = 0 := rfl
  have hα : Q.Pi₀ e₀ = ac 0 0 • e₁ := by
    apply τ₁.injective
    apply Subtype.ext
    rw [hT0 e₀, map_smul, Submodule.coe_smul, hτe₀, hτe₁]
    show t₁.X.lieVarpi (MvFormalGroup.CartierModule.tangent (γ₁ 0)) = ac 0 0 • MvFormalGroup.CartierModule.tangent (γ₁ 1)
    rw [FormalODModule.lieVarpi, Matrix.mulVecLin_apply, hLRC 0, hpi0]
  have hβ : Q.Pi₁ e₁ = ac 0 1 • e₀ := by
    apply τ₀.injective
    apply Subtype.ext
    rw [hT1 e₁, map_smul, Submodule.coe_smul, hτe₀, hτe₁]
    show t₁.X.lieVarpi (MvFormalGroup.CartierModule.tangent (γ₁ 1)) = ac 0 1 • MvFormalGroup.CartierModule.tangent (γ₁ 0)
    rw [FormalODModule.lieVarpi, Matrix.mulVecLin_apply, hLRC 1, hpi1]

  let r₁' : B' := gj' * a'
  let L₁' : Type := Localization.Away r₁'
  have hL₁' : IsNilpotent (p : L₁') := ReduceLL2.nil_of_map (algebraMap B' L₁') hB'
  have hφr₁' : (φ : B' →+* B) r₁' = r₁ := by show (φ : B' →+* B) (gj' * a') = g j * a; rw [map_mul, hgj'e, ha'e]
  have hu_r₁ : IsUnit (((algebraMap B L₁).comp (φ : B' →+* B)) r₁') := by
    rw [RingHom.comp_apply, hφr₁']; exact IsLocalization.Away.algebraMap_isUnit r₁
  let φ₁ : L₁' →+* L₁ := IsLocalization.Away.lift r₁' (g := (algebraMap B L₁).comp (φ : B' →+* B)) hu_r₁
  have hφ₁ : φ₁.comp (algebraMap B' L₁') = (algebraMap B L₁).comp (φ : B' →+* B) := IsLocalization.Away.lift_comp _ _
  haveI : IsLocalization.Away ((φ : B' →+* B) r₁') L₁ := by rw [hφr₁']; infer_instance
  have hφ₁s : Function.Surjective φ₁ := ReduceLL2.surjective_loc (φ : B' →+* B) r₁' φ₁ hφ₁ hφs
  have hφ₁2 : RingHom.ker φ₁ * RingHom.ker φ₁ = ⊥ := ReduceLL2.ker_mul_ker_eq_bot_loc (φ : B' →+* B) r₁' φ₁ hφ₁ hφ2
  letI algL₁' : Algebra ℤ_[p] L₁' := ((algebraMap B' L₁').comp (algebraMap ℤ_[p] B')).toAlgebra
  let algₐ' : B' →ₐ[ℤ_[p]] L₁' := ReduceLL2.algHomOf (algebraMap B' L₁') (fun z => rfl)
  let algₐ : B →ₐ[ℤ_[p]] L₁ := ReduceLL2.algHomOf (algebraMap B L₁) (fun z => rfl)
  let φ₁ₐ : L₁' →ₐ[ℤ_[p]] L₁ := ReduceLL2.algHomOf φ₁ (fun z => by
    show φ₁ (algebraMap B' L₁' (algebraMap ℤ_[p] B' z)) = algebraMap B L₁ (algebraMap ℤ_[p] B z)
    have e1 := RingHom.congr_fun hφ₁ (algebraMap ℤ_[p] B' z)
    rw [RingHom.comp_apply, RingHom.comp_apply] at e1
    rw [e1]
    exact congrArg (algebraMap B L₁) (φ.commutes z))
  let d₁' : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) L₁' := d'.map (p : ℤ_[p]) algₐ'
  have hd₁' : DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) φ₁ₐ d₁' d₁ := by
    rw [ReduceLL2.isBaseChange_iff_eq_map]

    have e1 : d₁ = θ L₁ ψ₁ hL₁ (M.map (ψ' := ψ₁) hB hL₁ (algebraMap B L₁) rfl x) := by
      show θ L₁ ψ₁ hL₁ (η L₁ ψ₁ hL₁ t₁) = _; rw [hηt₁]
    have e2 : θ L₁ ψ₁ hL₁ (M.map (ψ' := ψ₁) hB hL₁ (algₐ : B →+* L₁) rfl x) = (θ B ψ hB x).map (p : ℤ_[p]) algₐ :=
      (ReduceLL2.isBaseChange_iff_eq_map _ _ _).mp (hθ.2 B L₁ ψ ψ₁ hB hL₁ algₐ rfl x)
    have e3 : θ B ψ hB x = d'.map (p : ℤ_[p]) φ := (ReduceLL2.isBaseChange_iff_eq_map _ _ _).mp hd'
    have e4 : algₐ.comp φ = φ₁ₐ.comp algₐ' := by
      apply AlgHom.ext; intro b
      show algebraMap B L₁ (φ b) = φ₁ (algebraMap B' L₁' b)
      exact (RingHom.congr_fun hφ₁ b).symm
    have e5 : M.map (ψ' := ψ₁) hB hL₁ (algebraMap B L₁) rfl x = M.map (ψ' := ψ₁) hB hL₁ (algₐ : B →+* L₁) rfl x :=
      mapIrrel hB hL₁ _ _ (ReduceLL2.coe_algHomOf _ _).symm _ _ x
    rw [e1, e5, e2, e3, ← ReduceLL2.dmap_comp, e4, ReduceLL2.dmap_comp]

  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Finite (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) :=
    Finite.of_equiv (ZMod p)
      (((RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZMod (p := p)))).symm.toEquiv).trans
        (Ideal.quotEquivOfEq ((PadicInt.ker_toZMod (p := p)).trans (PadicInt.maximalIdeal_eq_span_p (p := p)))).toEquiv)
  have hφ₁n : IsNilpotent (RingHom.ker (φ₁ₐ : L₁' →+* L₁)) := by
    rw [ReduceLL2.coe_algHomOf]; exact ⟨2, by rw [pow_two]; exact hφ₁2⟩
  have hφ₁ₐs : Function.Surjective φ₁ₐ := hφ₁s
  have hL₁'π : IsNilpotent (algebraMap ℤ_[p] L₁' (p : ℤ_[p])) := by rw [map_natCast]; exact hL₁'
  obtain ⟨n₂, c, hcspan, hcloc⟩ :=
    CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.exists_cover_forall_exists_mul_eq_and_map_eq_of_isBaseChange
      (PadicInt.irreducible_p (p := p)) φ₁ₐ hφ₁ₐs hφ₁n hL₁'π hQd e₀ e₁ he₀ he₁ (ac 0 0) (ac 0 1) hα hβ d₁' hd₁'

  have hr₁'𝔪 : r₁' ∉ 𝔪 := fun hmem => (h𝔪.isPrime.mem_or_mem hmem).elim hgj'𝔪 ha'𝔪
  have hdisj' : Disjoint (↑(Submonoid.powers r₁') : Set B') ↑𝔪 := by
    rw [Set.disjoint_left]; rintro _ ⟨kk', rfl⟩ hk; exact hr₁'𝔪 (h𝔪.isPrime.mem_of_pow_mem kk' hk)
  have h𝔪₁' : (Ideal.map (algebraMap B' L₁') 𝔪).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers r₁') L₁' 𝔪 h𝔪.isPrime hdisj'
  obtain ⟨k₂, hk₂⟩ : ∃ k₂, c k₂ ∉ Ideal.map (algebraMap B' L₁') 𝔪 := by
    by_contra hall; push_neg at hall
    have : Ideal.span (Set.range c) ≤ Ideal.map (algebraMap B' L₁') 𝔪 := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
    rw [hcspan, top_le_iff] at this
    exact h𝔪₁'.ne_top this
  obtain ⟨m₂, b', hmb'⟩ := IsLocalization.Away.surj r₁' (c k₂)
  have hb'𝔪 : b' ∉ 𝔪 := by
    intro hb
    have h1 : algebraMap B' L₁' b' ∈ Ideal.map (algebraMap B' L₁') 𝔪 := Ideal.mem_map_of_mem _ hb
    rw [← hmb'] at h1
    rcases h𝔪₁'.mem_or_mem h1 with h2 | h2
    · exact hk₂ h2
    · have h3 : r₁' ∈ (Ideal.map (algebraMap B' L₁') 𝔪).under B' := h𝔪₁'.mem_of_pow_mem m₂ h2
      rw [IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers r₁') L₁' h𝔪.isPrime hdisj'] at h3
      exact hr₁'𝔪 h3
  refine ⟨r₁' * b', fun hmem => (h𝔪.isPrime.mem_or_mem hmem).elim hr₁'𝔪 hb'𝔪, ?_⟩

  intro L' _ _ _ _ L _ _ _ _ hL' hL φL hφL hφLψ
  let ψL : WittVector p k →+* L := (algebraMap B L).comp ψ
  let ψL' : WittVector p k →+* L' := (algebraMap B' L').comp ψ'

  have hu1' : IsUnit (algebraMap B' L' r₁') := IsLocalization.Away.isUnit_of_dvd (x := r₁' * b') ⟨b', rfl⟩
  have hub' : IsUnit (algebraMap B' L' b') := IsLocalization.Away.isUnit_of_dvd (x := r₁' * b') ⟨r₁', mul_comm _ _⟩
  let e₁' : L₁' →+* L' := IsLocalization.Away.lift r₁' (g := algebraMap B' L') hu1'
  have he₁' : e₁'.comp (algebraMap B' L₁') = algebraMap B' L' := IsLocalization.Away.lift_comp _ _
  have he₁'a : ∀ b : B', e₁' (algebraMap B' L₁' b) = algebraMap B' L' b := fun b => RingHom.congr_fun he₁' b
  have hu_c : IsUnit (e₁' (c k₂)) := by
    have e : e₁' (c k₂) * e₁' (algebraMap B' L₁' r₁') ^ m₂ = algebraMap B' L' b' := by
      rw [← map_pow, ← map_mul, hmb']; exact he₁'a b'
    exact isUnit_of_mul_isUnit_left (e.symm ▸ hub')
  let L₂' : Type := Localization.Away (c k₂)
  let e₂' : L₂' →+* L' := IsLocalization.Away.lift (c k₂) (g := e₁') hu_c
  have he₂' : e₂'.comp (algebraMap L₁' L₂') = e₁' := IsLocalization.Away.lift_comp _ _
  have hφrb : (φ : B' →+* B) (r₁' * b') = r₁ * φ b' := by rw [map_mul, hφr₁']; rfl
  haveI instL : IsLocalization.Away ((φ : B' →+* B) (r₁' * b')) L := ‹IsLocalization.Away (φ (r₁' * b')) L›
  have hu1 : IsUnit (algebraMap B L r₁) :=
    IsLocalization.Away.isUnit_of_dvd (x := (φ : B' →+* B) (r₁' * b')) ⟨(φ : B' →+* B) b', hφrb⟩
  have hub : IsUnit (algebraMap B L ((φ : B' →+* B) b')) :=
    IsLocalization.Away.isUnit_of_dvd (x := (φ : B' →+* B) (r₁' * b')) ⟨r₁, by rw [hφrb]; exact mul_comm _ _⟩
  let e₁ : L₁ →+* L := IsLocalization.Away.lift r₁ (g := algebraMap B L) hu1
  have he₁ : e₁.comp (algebraMap B L₁) = algebraMap B L := IsLocalization.Away.lift_comp _ _
  have he₁a : ∀ b : B, e₁ (algebraMap B L₁ b) = algebraMap B L b := fun b => RingHom.congr_fun he₁ b
  have hφ₁a : ∀ b : B', φ₁ (algebraMap B' L₁' b) = algebraMap B L₁ ((φ : B' →+* B) b) := fun b => RingHom.congr_fun hφ₁ b
  let L₂ : Type := Localization.Away (φ₁ₐ (c k₂))
  let φ₂ : L₂' →+* L₂ := IsLocalization.Away.lift (c k₂) (g := (algebraMap L₁ L₂).comp φ₁)
    (IsLocalization.Away.algebraMap_isUnit (φ₁ₐ (c k₂)))
  have hφ₂ : φ₂.comp (algebraMap L₁' L₂') = (algebraMap L₁ L₂).comp (φ₁ₐ : L₁' →+* L₁) :=
    IsLocalization.Away.lift_comp _ _
  have hu_φc : IsUnit (e₁ (φ₁ₐ (c k₂))) := by
    have e0 := congrArg φ₁ hmb'
    rw [map_mul, map_pow, hφ₁a, hφ₁a, hφr₁'] at e0
    have e : e₁ (φ₁ (c k₂)) * algebraMap B L r₁ ^ m₂ = algebraMap B L ((φ : B' →+* B) b') := by
      rw [← he₁a r₁, ← he₁a, ← map_pow, ← map_mul, e0]
    exact isUnit_of_mul_isUnit_left (e.symm ▸ hub)
  let e₂ : L₂ →+* L := IsLocalization.Away.lift (φ₁ₐ (c k₂)) (g := e₁) hu_φc
  have he₂ : e₂.comp (algebraMap L₁ L₂) = e₁ := IsLocalization.Away.lift_comp _ _

  obtain ⟨α', β', hα', hβ', hαβ'⟩ := hcloc k₂ L₂' L₂ φ₂ hφ₂
  have hcomm₁ : φL.comp e₁' = e₁.comp φ₁ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r₁')
    rw [RingHom.comp_assoc, he₁', hφL, RingHom.comp_assoc, hφ₁, ← RingHom.comp_assoc, he₁]
  have hcomm₂ : φL.comp e₂' = e₂.comp φ₂ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (c k₂))
    rw [RingHom.comp_assoc, he₂', hcomm₁, RingHom.comp_assoc, hφ₂, ← RingHom.comp_assoc, he₂,
      ReduceLL2.coe_algHomOf]
  have hαL : φL (e₂' α') = e₁ (ac 0 0) := by
    have := RingHom.congr_fun hcomm₂ α'
    rw [RingHom.comp_apply, RingHom.comp_apply, hα', ← RingHom.comp_apply e₂, he₂] at this
    exact this
  have hβL : φL (e₂' β') = e₁ (ac 0 1) := by
    have := RingHom.congr_fun hcomm₂ β'
    rw [RingHom.comp_apply, RingHom.comp_apply, hβ', ← RingHom.comp_apply e₂, he₂] at this
    exact this
  have hαβL : e₂' α' * e₂' β' = (p : L') := by
    rw [← map_mul, hαβ', map_natCast, map_natCast, map_natCast]

  have hgs : Function.Surjective φL := ReduceLL2.surjective_loc (φ : B' →+* B) (r₁' * b') φL hφL hφs
  have hg2 : RingHom.ker φL * RingHom.ker φL = ⊥ := ReduceLL2.ker_mul_ker_eq_bot_loc (φ : B' →+* B) (r₁' * b') φL hφL hφ2
  have he₁ψ : e₁.comp ψ₁ = ψL := by
    show e₁.comp ((algebraMap B L₁).comp ψ) = (algebraMap B L).comp ψ
    rw [← RingHom.comp_assoc, he₁]
  have htL : (t₁.map e₁).IsAdmissible ι ψL := by
    have h := CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι ψ₁ e₁ t₁ ht₁
    rw [he₁ψ] at h
    exact h
  have hjL : e₁.comp (structureMap ι ψ₁) = structureMap ι ψL := by
    show e₁.comp (ψ₁.comp ι) = ψL.comp ι; rw [← RingHom.comp_assoc, he₁ψ]
  have hγL : (t₁.map e₁).X.IsHomogeneousVBasis (structureMap ι ψL)
      (fun i => MvFormalGroup.CartierModule.baseChange e₁ (γ₁ i)) := hjL ▸ hγ₁.map e₁
  have haL : (t₁.map e₁).X.HasStructureConstants (fun i => MvFormalGroup.CartierModule.baseChange e₁ (γ₁ i))
      (fun m i => e₁ (ac m i)) := hac.map e₁
  obtain ⟨t', ht', hiso⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_and_isIsomorphic_map_of_hasStructureConstants_of_map_eq_of_mul_eq_of_ker_mul_ker_eq_bot
      p ι Φ ψL ψL' hL' φL hφLψ hgs hg2 (t₁.map e₁) htL (fun i => MvFormalGroup.CartierModule.baseChange e₁ (γ₁ i)) hγL
      (fun m i => e₁ (ac m i)) haL (e₂' α') (e₂' β') hαL hβL hαβL

  refine ⟨η L' ψL' hL' t', ?_⟩
  show M.map hL' hL φL hφLψ (η L' ψL' hL' t') = M.map (ψ' := ψL) hB hL (algebraMap B L) rfl x
  have hadm1 : (t'.map φL).IsAdmissible ι ψL := by
    have h := CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι ψL' φL t' ht'
    rw [show φL.comp ψL' = ψL from hφLψ] at h
    exact h
  rw [← hη.2.1 L' L ψL' ψL hL' hL φL hφLψ t' ht', (hη.1 L ψL hL (t'.map φL) (t₁.map e₁) hadm1 htL).mpr hiso,
    hη.2.1 L₁ L ψ₁ ψL hL₁ hL e₁ he₁ψ t₁ ht₁, hηt₁, ← M.map_comp hB hL₁ hL e₁ (algebraMap B L₁) rfl he₁ψ x]
  exact mapIrrel hB hL _ _ he₁ _ rfl x

#print axioms solution

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_exists_cover_exists_map_eq_map_of_isBaseChange_of_ker_mul_ker_eq_bot_of_lieVarpi_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_exists_cover_exists_map_eq_map_of_isBaseChange_of_ker_mul_ker_eq_bot_of_lieVarpi_eq_zero (solution)
