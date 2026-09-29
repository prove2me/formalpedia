-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.stalkMap_surjective_of_tangent_germ_wittVector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b638068c-9cf2-57af-8409-dc911aa06ac7

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_mem_iff_exists_isEtaSection_zero_map_of_isAlgClosed_of_ker_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_mem_iff_exists_isEtaSection_one_map_of_isAlgClosed_of_ker_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Theorems.Thm_CerednikDrinfeld_FormalODModule_lieZero_le_span_tangent_and_lieOne_le_span_tangent_of_mem_etaPiece_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_awayToLoc_tangent_eq_of_isEtaSection_of_isEtaSection
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_of_mem_etaPiece_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_stalkMap_surjective_of_tangent_germ_wittVector
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj"

set_option autoImplicit false

namespace StalkOnto

theorem eq_top_of_mem_of_not_mem_smul_top {R : Type} [CommRing R] [IsLocalRing R] {M : Type} [AddCommGroup M] [Module R M]
    [Module.Invertible R M] (G : Submodule R M) (m : M) (hm : m ∈ G)
    (hnot : m ∉ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M)) : G = ⊤ := by
  haveI : Module.Free R M := inferInstance
  obtain ⟨e⟩ := (Module.Invertible.free_iff_linearEquiv (R := R) (M := M)).mp this
  set g : M := e.symm 1
  have hrep : ∀ n : M, n = e n • g := by
    intro n; apply e.injective; simp [g]
  have hunit : IsUnit (e m) := by
    by_contra hu
    apply hnot
    have hmem : e m ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hu
    rw [hrep m]
    exact Submodule.smul_mem_smul hmem Submodule.mem_top
  obtain ⟨c, hc⟩ := hunit
  have hg : g ∈ G := by
    have : g = ((c⁻¹ : Rˣ) : R) • m := by
      rw [hrep m, ← hc, smul_smul, Units.inv_mul, one_smul]
    rw [this]; exact G.smul_mem _ hm
  refine Submodule.eq_top_iff'.mpr fun n => ?_
  rw [hrep n]; exact G.smul_mem _ hg

section GeomPoint

variable {B : Type} [CommRing B] (x : PrimeSpectrum B) (P : Submodule B (Fin 2 → B))

theorem apply_eq_zero_of_mk_mem_maximalIdeal_smul_top {K : Type} [CommRing K] [IsDomain K] (φ : B →+* K)
    (hφ0 : ∀ a ∈ x.asIdeal, φ a = 0) (hφ1 : ∀ c ∉ x.asIdeal, φ c ≠ 0)
    (s : ↥P) (b : x.asIdeal.primeCompl)
    (h : LocalizedModule.mk s b ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime x.asIdeal)) • (⊤ : Submodule (Localization.AtPrime x.asIdeal) (LocalizedModule x.asIdeal.primeCompl ↥P))) :
    ∀ i, φ ((s : Fin 2 → B) i) = 0 := by
  let Z : Submodule (Localization.AtPrime x.asIdeal) (LocalizedModule x.asIdeal.primeCompl ↥P) :=
    { carrier := {m | ∃ (s' : ↥P) (b' : x.asIdeal.primeCompl), m = LocalizedModule.mk s' b' ∧ ∀ i, φ ((s' : Fin 2 → B) i) = 0}
      zero_mem' := ⟨0, 1, (LocalizedModule.zero_mk 1).symm, fun i => by simp⟩
      add_mem' := by
        rintro _ _ ⟨s₁, b₁, rfl, e₁⟩ ⟨s₂, b₂, rfl, e₂⟩
        refine ⟨b₂ • s₁ + b₁ • s₂, b₁ * b₂, LocalizedModule.mk_add_mk, fun i => ?_⟩
        have hs : ((b₂ • s₁ + b₁ • s₂ : ↥P) : Fin 2 → B) i = (b₂ : B) * (s₁ : Fin 2 → B) i + (b₁ : B) * (s₂ : Fin 2 → B) i := rfl
        rw [hs, map_add, map_mul, map_mul, e₁, e₂, mul_zero, mul_zero, add_zero]
      smul_mem' := by
        rintro c _ ⟨s', b', rfl, e'⟩
        induction c using Localization.induction_on with
        | H y =>
          obtain ⟨a, d⟩ := y
          refine ⟨a • s', d * b', (LocalizedModule.mk_smul_mk a s' d b'), fun i => ?_⟩
          have hs : ((a • s' : ↥P) : Fin 2 → B) i = a * (s' : Fin 2 → B) i := rfl
          rw [hs, map_mul, e', mul_zero] }
  have hle : (IsLocalRing.maximalIdeal (Localization.AtPrime x.asIdeal)) •
      (⊤ : Submodule (Localization.AtPrime x.asIdeal) (LocalizedModule x.asIdeal.primeCompl ↥P)) ≤ Z := by
    refine Submodule.smul_le.mpr fun r hr n _ => ?_
    induction n using LocalizedModule.induction_on with
    | h s₀ b₀ =>
      induction r using Localization.induction_on with
      | H y =>
        obtain ⟨a, d⟩ := y
        have ha : a ∈ x.asIdeal := by
          have h1 : Localization.mk a d * algebraMap B (Localization.AtPrime x.asIdeal) (d : B) =
              algebraMap B (Localization.AtPrime x.asIdeal) a := by
            rw [Localization.mk_eq_mk']; exact IsLocalization.mk'_spec _ a d
          have h2 : algebraMap B (Localization.AtPrime x.asIdeal) a ∈
              IsLocalRing.maximalIdeal (Localization.AtPrime x.asIdeal) := by
            rw [← h1]; exact Ideal.mul_mem_right _ _ hr
          exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime x.asIdeal) x.asIdeal a).mp h2
        refine ⟨a • s₀, d * b₀, LocalizedModule.mk_smul_mk a s₀ d b₀, fun i => ?_⟩
        have hs : ((a • s₀ : ↥P) : Fin 2 → B) i = a * (s₀ : Fin 2 → B) i := rfl
        rw [hs, map_mul, hφ0 a ha, zero_mul]
  obtain ⟨s', b', heq, e'⟩ := hle h
  rw [LocalizedModule.mk_eq] at heq
  obtain ⟨c, hc⟩ := heq
  intro i
  have hci : (c : B) * ((b' : B) * (s : Fin 2 → B) i) = (c : B) * ((b : B) * (s' : Fin 2 → B) i) := by
    have := congrArg (fun (v : ↥P) => (v : Fin 2 → B) i) hc
    exact this
  have := congrArg φ hci
  rw [map_mul, map_mul, map_mul, map_mul, e' i, mul_zero, mul_zero] at this
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 (hφ1 c c.2)
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd h2 (hφ1 (b' : B) b'.2)
  · exact h2

theorem exists_algClosed_point :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (φ : B →+* K), RingHom.ker φ = x.asIdeal := by
  let D := B ⧸ x.asIdeal
  let F := FractionRing D
  let K := AlgebraicClosure F
  refine ⟨K, inferInstance, inferInstance,
    ((algebraMap F K).comp (algebraMap D F)).comp (Ideal.Quotient.mk x.asIdeal), ?_⟩
  have hinj : Function.Injective ((algebraMap F K).comp (algebraMap D F)) :=
    (algebraMap F K).injective.comp (IsFractionRing.injective D F)
  rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp hinj, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker]

end GeomPoint

end StalkOnto

namespace StalkOnto

theorem exists_ne_zero_of_span_eq_top' {R M : Type} [Semiring R] [AddCommMonoid M] [Module R M]
    (P : Submodule R M) [Nontrivial ↥P] (T : Set M) (h : P ≤ Submodule.span R T) : ∃ t ∈ T, t ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hle : Submodule.span R T ≤ ⊥ := Submodule.span_le.mpr fun t ht =>
    show t ∈ ((⊥ : Submodule R M) : Set M) from by simp [hcon t ht]
  have hP : P = ⊥ := le_bot_iff.mp (h.trans hle)
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := exists_pair_ne (↥P)
  apply hab
  rw [hP, Submodule.mem_bot] at ha hb
  exact Subtype.ext (ha.trans hb.symm)

end StalkOnto

namespace StalkOnto

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

theorem tangent_eq_of_mkQ_eq {p : ℕ} [Fact p.Prime] {S : Type} [CommRing S] (X : FormalODModule p S) (jS : Zp2 p →+* S)
    (hc : IsCompl (X.gradedPiece jS 0) (X.gradedPiece jS 1)) (m m' : CartierModule p X.F)
    (h : (X.toGradedCartierModuleData jS hc).vRange.mkQ m = (X.toGradedCartierModuleData jS hc).vRange.mkQ m') :
    tangent m = tangent m' := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨y, hy⟩ := ((X.toGradedCartierModuleData jS hc).mem_vRange_iff _).mp h
  have hy' : verschiebungInt y = m - m' := hy
  have : tangent (m - m') = 0 := by
    rw [← hy']
    exact tangent_verschiebungInt y
  rwa [map_sub, sub_eq_zero] at this

theorem awayToLoc_awayHom {B : Type} [CommRing B] (x : PrimeSpectrum B) (f : B) (hf : f ∉ x.asIdeal) (b : B) :
    Rigidified.awayToLoc x f hf (Rigidified.awayHom f b) = Rigidified.locHom x b := by
  unfold Rigidified.awayToLoc
  exact IsLocalization.Away.lift_eq f _ b

end StalkOnto

namespace StalkOnto

theorem nontrivial_of_invertible_of_nontrivial {R M : Type} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M]
    [Module.Invertible R M] : Nontrivial M := by
  by_contra h
  haveI : Subsingleton M := not_nontrivial_iff_subsingleton.mp h
  have : (0 : R) = 1 := (FaithfulSMul.eq_of_smul_eq_smul (M := R) (α := M) fun m => Subsingleton.elim _ _)
  exact zero_ne_one this

theorem isField_baway_one (K : Type) [Field K] : IsField (CerednikDrinfeld.SpecialFormal.Rigidified.Baway (1 : K)) := by
  have hu : ∀ s ∈ Submonoid.powers (1 : K), IsUnit s := by
    rintro s ⟨n, rfl⟩; simp
  let e : K ≃+* CerednikDrinfeld.SpecialFormal.Rigidified.Baway (1 : K) :=
    (IsLocalization.atUnits K (Submonoid.powers (1 : K)) hu).toRingEquiv
  refine ⟨⟨e 0, e 1, fun h => zero_ne_one (e.injective h)⟩, mul_comm, fun {a} ha => ⟨e ((e.symm a)⁻¹), ?_⟩⟩
  have ha' : e.symm a ≠ 0 := fun h => ha (by rw [← e.apply_symm_apply a, h, map_zero])
  calc a * e ((e.symm a)⁻¹) = e (e.symm a) * e ((e.symm a)⁻¹) := by rw [e.apply_symm_apply]
    _ = 1 := by rw [← map_mul, mul_inv_cancel₀ ha', map_one]

noncomputable def equivBawayOne (K : Type) [Field K] : K ≃+* CerednikDrinfeld.SpecialFormal.Rigidified.Baway (1 : K) :=
  (IsLocalization.atUnits K (Submonoid.powers (1 : K)) (by rintro s ⟨n, rfl⟩; simp)).toRingEquiv

end StalkOnto

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem stalkOnto_core
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
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (N₀ N₁ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v)
    (hN₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v)
    (hfull₀ : ∀ x, LT.LatticeTree.IsFullLattice (N₀ x)) (hfull₁ : ∀ x, LT.LatticeTree.IsFullLattice (N₁ x))
    (hle : ∀ x, N₀ x ≤ N₁ x) (hsmul : ∀ x, ∀ v ∈ N₁ x, algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ N₀ x)
    (Pi₀ : ↥(t.X.lieZero (structureMap ι ψ)) →ₗ[B] ↥(t.X.lieOne (structureMap ι ψ))) (Pi₁ : ↥(t.X.lieOne (structureMap ι ψ)) →ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
    (hPi₀ : ∀ s : ↥(t.X.lieZero (structureMap ι ψ)), ((Pi₀ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) = t.X.lieVarpi (s : t.X.Lie))
    (hPi₁ : ∀ s : ↥(t.X.lieOne (structureMap ι ψ)), ((Pi₁ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) = t.X.lieVarpi (s : t.X.Lie))
    (u₀ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₀ x, hfull₀ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieZero (structureMap ι ψ)))
    (u₁ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₁ x, hfull₁ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieOne (structureMap ι ψ)))
    (hg₀ :
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₀ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
          (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v),
        ∃ (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M) (s : ↥(t.X.lieZero (structureMap ι ψ)))
          (b : x.asIdeal.primeCompl),
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          u₀ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ x))) = LocalizedModule.mk s b ∧
          ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i)))
    (hg₁ :
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₁ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
          (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v),
        ∃ (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M) (s : ↥(t.X.lieOne (structureMap ι ψ)))
          (b : x.asIdeal.primeCompl),
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          u₁ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ x))) = LocalizedModule.mk s b ∧
          ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i)))
    (Hw₀ : ∀ x : PrimeSpectrum B, ∃ (K : Type) (_ : Field K) (φ : B →+* K) (_ : RingHom.ker φ = x.asIdeal)
      (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₀ x) (f : B) (hf : f ∉ x.asIdeal)
      (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
      (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
      (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
      (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v)
      (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M)
      (_ : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m = ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩)
      (χ : Rigidified.Baway f →+* K) (_ : χ.comp (Rigidified.awayHom f) = φ),
      ∃ i, χ (MvFormalGroup.CartierModule.tangent m i) ≠ 0)
    (Hw₁ : ∀ x : PrimeSpectrum B, ∃ (K : Type) (_ : Field K) (φ : B →+* K) (_ : RingHom.ker φ = x.asIdeal)
      (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₁ x) (f : B) (hf : f ∉ x.asIdeal)
      (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
      (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
      (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
      (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v)
      (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M)
      (_ : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m = ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩)
      (χ : Rigidified.Baway f →+* K) (_ : χ.comp (Rigidified.awayHom f) = φ),
      ∃ i, χ (MvFormalGroup.CartierModule.tangent m i) ≠ 0) :
    (∀ x, Function.Surjective (u₀ x)) ∧ (∀ x, Function.Surjective (u₁ x)) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · obtain ⟨K, _instK, φ, hker, v, hv, f, hf, hc, hcb, hcΦf, L, hL, z, hz, m, hm, χ, hχ, i₀, hi₀⟩ := Hw₀ x
    haveI : Module.Invertible B ↥(t.X.lieZero (structureMap ι ψ)) := ht.1.2.1
    suffices hTop : LinearMap.range (u₀ x) = ⊤ from LinearMap.range_eq_top.mp hTop
    obtain ⟨m', s, b, hm', hu, hs⟩ := hg₀ x v hv f hf hc hcb hcΦf L hL z hz
    have htan : MvFormalGroup.CartierModule.tangent m' = MvFormalGroup.CartierModule.tangent m :=
      StalkOnto.tangent_eq_of_mkQ_eq _ _ hc m' m (hm'.trans hm.symm)
    apply StalkOnto.eq_top_of_mem_of_not_mem_smul_top (LinearMap.range (u₀ x)) (LocalizedModule.mk s b)
      (LinearMap.mem_range.mpr ⟨_, hu⟩)
    intro hmem
    have hφ0 : ∀ a ∈ x.asIdeal, φ a = 0 := fun a ha => by rw [← RingHom.mem_ker, hker]; exact ha
    have hφ1 : ∀ c ∉ x.asIdeal, φ c ≠ 0 := fun c hc0 h0 => hc0 (by rw [← hker]; exact h0)
    have hzero := StalkOnto.apply_eq_zero_of_mk_mem_maximalIdeal_smul_top x _ φ hφ0 hφ1 s b hmem
    have hunits : ∀ y : x.asIdeal.primeCompl, IsUnit (φ y) := fun y => isUnit_iff_ne_zero.mpr (hφ1 y y.2)
    let ψx : Localization.AtPrime x.asIdeal →+* K := IsLocalization.lift hunits
    have hψloc : ∀ b₀ : B, ψx (Rigidified.locHom x b₀) = φ b₀ := fun b₀ => IsLocalization.lift_eq hunits b₀
    have hψχ : ∀ y, ψx (Rigidified.awayToLoc x f hf y) = χ y := by
      intro y
      have hext : ψx.comp (Rigidified.awayToLoc x f hf) = χ := by
        apply IsLocalization.ringHom_ext (Submonoid.powers f)
        ext b₀
        simp only [RingHom.comp_apply]
        rw [StalkOnto.awayToLoc_awayHom, hψloc, ← hχ, RingHom.comp_apply]
      rw [← hext, RingHom.comp_apply]
    have key := congrArg ψx (hs i₀)
    rw [hψloc, map_mul, hψloc, hψχ, htan] at key
    exact mul_ne_zero (hφ1 (b : B) b.2) hi₀ (key ▸ hzero i₀)
  · obtain ⟨K, _instK, φ, hker, v, hv, f, hf, hc, hcb, hcΦf, L, hL, z, hz, m, hm, χ, hχ, i₀, hi₀⟩ := Hw₁ x
    haveI : Module.Invertible B ↥(t.X.lieOne (structureMap ι ψ)) := ht.1.2.2
    suffices hTop : LinearMap.range (u₁ x) = ⊤ from LinearMap.range_eq_top.mp hTop
    obtain ⟨m', s, b, hm', hu, hs⟩ := hg₁ x v hv f hf hc hcb hcΦf L hL z hz
    have htan : MvFormalGroup.CartierModule.tangent m' = MvFormalGroup.CartierModule.tangent m :=
      StalkOnto.tangent_eq_of_mkQ_eq _ _ hc m' m (hm'.trans hm.symm)
    apply StalkOnto.eq_top_of_mem_of_not_mem_smul_top (LinearMap.range (u₁ x)) (LocalizedModule.mk s b)
      (LinearMap.mem_range.mpr ⟨_, hu⟩)
    intro hmem
    have hφ0 : ∀ a ∈ x.asIdeal, φ a = 0 := fun a ha => by rw [← RingHom.mem_ker, hker]; exact ha
    have hφ1 : ∀ c ∉ x.asIdeal, φ c ≠ 0 := fun c hc0 h0 => hc0 (by rw [← hker]; exact h0)
    have hzero := StalkOnto.apply_eq_zero_of_mk_mem_maximalIdeal_smul_top x _ φ hφ0 hφ1 s b hmem
    have hunits : ∀ y : x.asIdeal.primeCompl, IsUnit (φ y) := fun y => isUnit_iff_ne_zero.mpr (hφ1 y y.2)
    let ψx : Localization.AtPrime x.asIdeal →+* K := IsLocalization.lift hunits
    have hψloc : ∀ b₀ : B, ψx (Rigidified.locHom x b₀) = φ b₀ := fun b₀ => IsLocalization.lift_eq hunits b₀
    have hψχ : ∀ y, ψx (Rigidified.awayToLoc x f hf y) = χ y := by
      intro y
      have hext : ψx.comp (Rigidified.awayToLoc x f hf) = χ := by
        apply IsLocalization.ringHom_ext (Submonoid.powers f)
        ext b₀
        simp only [RingHom.comp_apply]
        rw [StalkOnto.awayToLoc_awayHom, hψloc, ← hχ, RingHom.comp_apply]
      rw [← hext, RingHom.comp_apply]
    have key := congrArg ψx (hs i₀)
    rw [hψloc, map_mul, hψloc, hψχ, htan] at key
    exact mul_ne_zero (hφ1 (b : B) b.2) hi₀ (key ▸ hzero i₀)

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
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (N₀ N₁ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v)
    (hN₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v)
    (hfull₀ : ∀ x, LT.LatticeTree.IsFullLattice (N₀ x)) (hfull₁ : ∀ x, LT.LatticeTree.IsFullLattice (N₁ x))
    (hle : ∀ x, N₀ x ≤ N₁ x) (hsmul : ∀ x, ∀ v ∈ N₁ x, algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ N₀ x)
    (Pi₀ : ↥(t.X.lieZero (structureMap ι ψ)) →ₗ[B] ↥(t.X.lieOne (structureMap ι ψ))) (Pi₁ : ↥(t.X.lieOne (structureMap ι ψ)) →ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
    (hPi₀ : ∀ s : ↥(t.X.lieZero (structureMap ι ψ)), ((Pi₀ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) = t.X.lieVarpi (s : t.X.Lie))
    (hPi₁ : ∀ s : ↥(t.X.lieOne (structureMap ι ψ)), ((Pi₁ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) = t.X.lieVarpi (s : t.X.Lie))
    (u₀ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₀ x, hfull₀ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieZero (structureMap ι ψ)))
    (u₁ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₁ x, hfull₁ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieOne (structureMap ι ψ)))
    (hg₀ :
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₀ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
          (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v),
        ∃ (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M) (s : ↥(t.X.lieZero (structureMap ι ψ)))
          (b : x.asIdeal.primeCompl),
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          u₀ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ x))) = LocalizedModule.mk s b ∧
          ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i)))
    (hg₁ :
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₁ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
          (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v),
        ∃ (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M) (s : ↥(t.X.lieOne (structureMap ι ψ)))
          (b : x.asIdeal.primeCompl),
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          u₁ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ x))) = LocalizedModule.mk s b ∧
          ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i)))
 :

    (∀ x, Function.Surjective (u₀ x)) ∧ (∀ x, Function.Surjective (u₁ x)) := by
  refine stalkOnto_core p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht N₀ N₁ hN₀ hN₁ hfull₀ hfull₁ hle hsmul
    Pi₀ Pi₁ hPi₀ hPi₁ u₀ u₁ hg₀ hg₁ (fun x => ?_) (fun x => ?_)
  ·
    obtain ⟨K, instF, instAC, φ, hker⟩ := StalkOnto.exists_algClosed_point x
    letI instAlg : Algebra ℤ_[p] K := (φ.comp (algebraMap ℤ_[p] B)).toAlgebra
    have hg : φ.comp (algebraMap ℤ_[p] B) = algebraMap ℤ_[p] K := rfl
    have hφ0 : ∀ a ∈ x.asIdeal, φ a = 0 := fun a ha => by rw [← RingHom.mem_ker, hker]; exact ha
    have hφ1 : ∀ c ∉ x.asIdeal, φ c ≠ 0 := fun c hc0 h0 => hc0 (by rw [← hker]; exact h0)
    have hunit : ∀ c ∉ x.asIdeal, IsUnit (φ c) := fun c hc0 => isUnit_iff_ne_zero.mpr (hφ1 c hc0)
    have hpx : (p : B) ∈ x.asIdeal := by
      obtain ⟨n, hn⟩ := hB
      exact x.isPrime.mem_of_pow_mem n (by rw [hn]; exact x.asIdeal.zero_mem)
    have hKp0 : (p : K) = 0 := by rw [← map_natCast φ, hφ0 _ hpx]
    have hKp : IsNilpotent (p : K) := ⟨1, by rw [pow_one, hKp0]⟩
    haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hKp0
    have ht' : (t.map φ).IsAdmissible ι (φ.comp ψ) :=
      CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι ψ φ t ht
    let x' : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
    have h1x' : (1 : K) ∉ x'.asIdeal := fun h => one_ne_zero ((Ideal.mem_bot).mp h)
    have h0' : Φ.lieZero (Rigidified.jbar ι) ≤ LinearMap.ker Φ.lieVarpi := h0Φ

    obtain ⟨f₀, hf₀, hc₀, hcb₀, hcΦ₀, L₀, hL₀, z₀, hz₀⟩ := (hN₀ x 0).mp (N₀ x).zero_mem
    obtain ⟨hc', hcb', hcΦ', L', hL', -, -, -, -⟩ :=
      CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
        p ι Φ hcΦ rΦ ψ hB t ht f₀ hc₀ hcb₀ hcΦ₀ L₀ hL₀ 0 z₀ 0 hz₀ φ hg hKp (hunit f₀ hf₀) ht'

    let eK := StalkOnto.equivBawayOne K
    letI instFS : Field (Rigidified.Baway (1 : K)) := (StalkOnto.isField_baway_one K).toField
    haveI : IsAlgClosed (Rigidified.Baway (1 : K)) := IsAlgClosed.of_ringEquiv K (Rigidified.Baway (1 : K)) eK
    haveI : CharP (Rigidified.Baway (1 : K)) p := charP_of_injective_ringHom eK.injective p
    have ht'' : ((t.map φ).map (Rigidified.awayHom (1 : K))).IsAdmissible ι ((Rigidified.awayHom (1 : K)).comp (φ.comp ψ)) :=
      CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι (φ.comp ψ) (Rigidified.awayHom (1 : K)) (t.map φ) ht'
    have hXsp : ((t.map φ).XS (Rigidified.awayHom (1 : K))).IsSpecial (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K))) := ht''.1
    have hX4' : ((t.map φ).XS (Rigidified.awayHom (1 : K))).HasHeight 4 := ht''.2.1
    have hβ := (CerednikDrinfeld.FormalODModule.lieZero_le_span_tangent_and_lieOne_le_span_tangent_of_mem_etaPiece_of_isAlgClosed p (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K))) ((t.map φ).XS (Rigidified.awayHom (1 : K))) hXsp hX4' hc' L' hL').1
    haveI : Module.Invertible (Rigidified.Baway (1 : K)) ↥(((t.map φ).XS (Rigidified.awayHom (1 : K))).lieZero (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K)))) := hXsp.2.1
    haveI : Nontrivial ↥(((t.map φ).XS (Rigidified.awayHom (1 : K))).lieZero (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K)))) := StalkOnto.nontrivial_of_invertible_of_nontrivial (R := Rigidified.Baway (1 : K))
    obtain ⟨τ, ⟨a, ⟨zS, hzS, hzSa⟩, rfl⟩, hτ0⟩ := StalkOnto.exists_ne_zero_of_span_eq_top' (((t.map φ).XS (Rigidified.awayHom (1 : K))).lieZero (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K)))) _ hβ

    obtain ⟨v, hv'⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_of_mem_etaPiece_of_isAlgClosed
      p k ι Φ hΦ hΦ4 h0' hcΦ rΦ hrΦ K (φ.comp ψ) hKp (t.map φ) ht' hc' hcb' hcΦ' L' hL' 0 zS hzS
    have hvN : v ∈ N₀ x :=
      (CerednikDrinfeld.SpecialFormal.Rigidified.mem_iff_exists_isEtaSection_zero_map_of_isAlgClosed_of_ker_eq p ι Φ hΦ hΦ4 h0' hcΦ rΦ hLΦ hrΦ ψ hB t ht N₀ hN₀ φ hg x hker ht' x' v).mpr
        ⟨1, h1x', hc', hcb', hcΦ', L', hL', zS, hv'⟩

    obtain ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hN₀ x v).mp hvN
    obtain ⟨m, s, b, hm, hu, hs⟩ := hg₀ x v hvN f hf hc hcb hcΦf L hL z hz
    obtain ⟨hc'', hcb'', hcΦ'', L'', hL'', z'', hz'', -, hrep⟩ :=
      CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
        p ι Φ hcΦ rΦ ψ hB t ht f hc hcb hcΦf L hL 0 z v hz φ hg hKp (hunit f hf) ht'
    obtain ⟨m'', hm'', htan''⟩ := hrep m hm

    have hq := CerednikDrinfeld.SpecialFormal.Rigidified.awayToLoc_tangent_eq_of_isEtaSection_of_isEtaSection
      p ι Φ hΦ hΦ4 hcΦ rΦ hLΦ hrΦ (φ.comp ψ) hKp (t.map φ) ht' x' 0 v 1 h1x' hc' hcb' hcΦ' L' hL' zS hv' a hzSa.symm
      1 h1x' hc'' hcb'' hcΦ'' L'' hL'' z'' hz'' m'' hm''
    obtain ⟨j₀, hj₀⟩ : ∃ j₀, MvFormalGroup.CartierModule.tangent a j₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hτ0 (funext hall)
    refine ⟨K, instF, φ, hker, v, hvN, f, hf, hc, hcb, hcΦf, L, hL, z, hz, m, hm,
      IsLocalization.Away.lift f (hunit f hf), IsLocalization.Away.lift_comp f (hunit f hf), j₀, fun hzero => hj₀ ?_⟩
    have hinj : Function.Injective (Rigidified.awayToLoc x' (1 : K) h1x') := (Rigidified.awayToLoc x' (1 : K) h1x').injective
    apply hinj
    rw [hq j₀, htan'' j₀, hzero, map_zero, map_zero]
  ·
    obtain ⟨K, instF, instAC, φ, hker⟩ := StalkOnto.exists_algClosed_point x
    letI instAlg : Algebra ℤ_[p] K := (φ.comp (algebraMap ℤ_[p] B)).toAlgebra
    have hg : φ.comp (algebraMap ℤ_[p] B) = algebraMap ℤ_[p] K := rfl
    have hφ0 : ∀ a ∈ x.asIdeal, φ a = 0 := fun a ha => by rw [← RingHom.mem_ker, hker]; exact ha
    have hφ1 : ∀ c ∉ x.asIdeal, φ c ≠ 0 := fun c hc0 h0 => hc0 (by rw [← hker]; exact h0)
    have hunit : ∀ c ∉ x.asIdeal, IsUnit (φ c) := fun c hc0 => isUnit_iff_ne_zero.mpr (hφ1 c hc0)
    have hpx : (p : B) ∈ x.asIdeal := by
      obtain ⟨n, hn⟩ := hB
      exact x.isPrime.mem_of_pow_mem n (by rw [hn]; exact x.asIdeal.zero_mem)
    have hKp0 : (p : K) = 0 := by rw [← map_natCast φ, hφ0 _ hpx]
    have hKp : IsNilpotent (p : K) := ⟨1, by rw [pow_one, hKp0]⟩
    haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hKp0
    have ht' : (t.map φ).IsAdmissible ι (φ.comp ψ) :=
      CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι ψ φ t ht
    let x' : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
    have h1x' : (1 : K) ∉ x'.asIdeal := fun h => one_ne_zero ((Ideal.mem_bot).mp h)
    have h0' : Φ.lieZero (Rigidified.jbar ι) ≤ LinearMap.ker Φ.lieVarpi := h0Φ

    obtain ⟨f₀, hf₀, hc₀, hcb₀, hcΦ₀, L₀, hL₀, z₀, hz₀⟩ := (hN₁ x 0).mp (N₁ x).zero_mem
    obtain ⟨hc', hcb', hcΦ', L', hL', -, -, -, -⟩ :=
      CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
        p ι Φ hcΦ rΦ ψ hB t ht f₀ hc₀ hcb₀ hcΦ₀ L₀ hL₀ 1 z₀ 0 hz₀ φ hg hKp (hunit f₀ hf₀) ht'

    let eK := StalkOnto.equivBawayOne K
    letI instFS : Field (Rigidified.Baway (1 : K)) := (StalkOnto.isField_baway_one K).toField
    haveI : IsAlgClosed (Rigidified.Baway (1 : K)) := IsAlgClosed.of_ringEquiv K (Rigidified.Baway (1 : K)) eK
    haveI : CharP (Rigidified.Baway (1 : K)) p := charP_of_injective_ringHom eK.injective p
    have ht'' : ((t.map φ).map (Rigidified.awayHom (1 : K))).IsAdmissible ι ((Rigidified.awayHom (1 : K)).comp (φ.comp ψ)) :=
      CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι (φ.comp ψ) (Rigidified.awayHom (1 : K)) (t.map φ) ht'
    have hXsp : ((t.map φ).XS (Rigidified.awayHom (1 : K))).IsSpecial (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K))) := ht''.1
    have hX4' : ((t.map φ).XS (Rigidified.awayHom (1 : K))).HasHeight 4 := ht''.2.1
    have hβ := (CerednikDrinfeld.FormalODModule.lieZero_le_span_tangent_and_lieOne_le_span_tangent_of_mem_etaPiece_of_isAlgClosed p (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K))) ((t.map φ).XS (Rigidified.awayHom (1 : K))) hXsp hX4' hc' L' hL').2
    haveI : Module.Invertible (Rigidified.Baway (1 : K)) ↥(((t.map φ).XS (Rigidified.awayHom (1 : K))).lieOne (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K)))) := hXsp.2.2
    haveI : Nontrivial ↥(((t.map φ).XS (Rigidified.awayHom (1 : K))).lieOne (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K)))) := StalkOnto.nontrivial_of_invertible_of_nontrivial (R := Rigidified.Baway (1 : K))
    obtain ⟨τ, ⟨a, ⟨zS, hzS, hzSa⟩, rfl⟩, hτ0⟩ := StalkOnto.exists_ne_zero_of_span_eq_top' (((t.map φ).XS (Rigidified.awayHom (1 : K))).lieOne (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K)))) _ hβ

    obtain ⟨v, hv'⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_of_mem_etaPiece_of_isAlgClosed
      p k ι Φ hΦ hΦ4 h0' hcΦ rΦ hrΦ K (φ.comp ψ) hKp (t.map φ) ht' hc' hcb' hcΦ' L' hL' 1 zS hzS
    have hvN : v ∈ N₁ x :=
      (CerednikDrinfeld.SpecialFormal.Rigidified.mem_iff_exists_isEtaSection_one_map_of_isAlgClosed_of_ker_eq p ι Φ hΦ hΦ4 h0' hcΦ rΦ hLΦ hrΦ ψ hB t ht N₁ hN₁ φ hg x hker ht' x' v).mpr
        ⟨1, h1x', hc', hcb', hcΦ', L', hL', zS, hv'⟩

    obtain ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hN₁ x v).mp hvN
    obtain ⟨m, s, b, hm, hu, hs⟩ := hg₁ x v hvN f hf hc hcb hcΦf L hL z hz
    obtain ⟨hc'', hcb'', hcΦ'', L'', hL'', z'', hz'', -, hrep⟩ :=
      CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
        p ι Φ hcΦ rΦ ψ hB t ht f hc hcb hcΦf L hL 1 z v hz φ hg hKp (hunit f hf) ht'
    obtain ⟨m'', hm'', htan''⟩ := hrep m hm

    have hq := CerednikDrinfeld.SpecialFormal.Rigidified.awayToLoc_tangent_eq_of_isEtaSection_of_isEtaSection
      p ι Φ hΦ hΦ4 hcΦ rΦ hLΦ hrΦ (φ.comp ψ) hKp (t.map φ) ht' x' 1 v 1 h1x' hc' hcb' hcΦ' L' hL' zS hv' a hzSa.symm
      1 h1x' hc'' hcb'' hcΦ'' L'' hL'' z'' hz'' m'' hm''
    obtain ⟨j₀, hj₀⟩ : ∃ j₀, MvFormalGroup.CartierModule.tangent a j₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hτ0 (funext hall)
    refine ⟨K, instF, φ, hker, v, hvN, f, hf, hc, hcb, hcΦf, L, hL, z, hz, m, hm,
      IsLocalization.Away.lift f (hunit f hf), IsLocalization.Away.lift_comp f (hunit f hf), j₀, fun hzero => hj₀ ?_⟩
    have hinj : Function.Injective (Rigidified.awayToLoc x' (1 : K) h1x') := (Rigidified.awayToLoc x' (1 : K) h1x').injective
    apply hinj
    rw [hq j₀, htan'' j₀, hzero, map_zero, map_zero]

end S_CerednikDrinfeld_SpecialFormal_Rigidified_stalkMap_surjective_of_tangent_germ_wittVector
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_stalkMap_surjective_of_tangent_germ_wittVector (solution)
