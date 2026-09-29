-- Prove2me | solution 1 for CerednikDrinfeld.comp_degeneracy_eq_pointEquivPlace_symm_restrictAlong_of_withExtraLevel_isPullback_repT_of_iso_pullback_completion_one_zero_of_two_mul_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/ca79c675-d88b-5f27-a488-04c20bfc4475

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_DescentIntertwining_v2
import Definitions.Def_CerednikDrinfeld_DescentIntertwiningBase
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_and_isLevelIsogeny_of_withExtraLevel_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_comp_degeneracy_eq_pointEquivPlace_symm_restrictAlong_of_withExtraLevel_isPullback_repT_of_iso_pullback_completion_one_zero_of_two_mul_dvd
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical
open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra

theorem solution
    {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D)
    (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')

    {a₂ b₂ : ℚ} (hdef₂ : IsDefiniteRamifiedExactlyAt (a := a₂) (b := b₂) q)
    (Λ₂ R₂ : Submodule ℤ ℍ[ℚ, a₂, b₂]) (hΛ₂ : IsMaximalOrder Λ₂) (hR₂ : IsEichlerOrder R₂ N) (hRΛ₂ : R₂ ≤ Λ₂)
    (n₂ : (ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₂ : n₂ ∈ primeHeckeSet R₂ q')
    (hS₂ : IsEichlerOrder (meetOrder R₂ n₂) (N * q'))
    (hnorm₂ : Submodule.conjByFiniteIdele (meetOrder R₂ n₂) n₂ = meetOrder R₂ n₂)
    (hsq₂ : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)),
      classSetShift _ n₂ (classSetShift _ n₂ x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    (hlaws₂ : ClassSetHeckeLaws N q' Λ₂ R₂ n₂)

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (x : SchemeHomOver s πX), ∃ E : FakeEllipticCurve Λ N k, pt k s E = x)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')

    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) [CategoryTheory.IsIso e𝔐]
    (he𝔐 : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)
    (gal : ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)

    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT)

    [hiso₁ : Fact (A₁.DecompositionIsometric ℚ)]
    (v₁ : HeightOneSpectrum (𝓞 ℚ)) (hv₁ : ((q' : ℕ) : 𝓞 ℚ) ∈ v₁.asIdeal)

    (ι₁ : ℍ[ℚ, a₂, b₂] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁)) (hι₁ : Function.Injective ι₁)
    (ρ₁ : (ℍ[ℚ, a₂, b₂])ˣ →* PGL(2, ↥(ValuationSubring.ratClosure A₁)))
    (hρ₁ : ∀ x : (ℍ[ℚ, a₂, b₂])ˣ, ρ₁ x = Matrix.ProjGenLinGroup.mk (Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁)) x))

    (ϖ₁ : Omega.PseudoUniformizer ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion)
    (hϖ₁ : algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion ϖ₁.ϖ = ((q' : AlgebraicClosure ℚ) : A₁.valuation.Completion))
    [hdom₁ : IsDomain (Omega.HolRingOf ϖ₁ ρ₁)]

    (s₁ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₂, b₂])ˣ)
    (sf₁ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs₁ : ∀ ℓ : HeckeTower.AwayPrime q q',
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₂, b₂] u (sf₁ ℓ : ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s₁ ℓ : ℍ[ℚ, a₂, b₂]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₂, b₂] u (sf₁ ℓ : ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₂, b₂]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf₁ ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₂ (meetOrder R₂ n₂) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₂ n₂) (ℓ.1 : ℕ)) ∧
      nrd (s₁ ℓ : ℍ[ℚ, a₂, b₂]) = ((ℓ.1 : ℕ) : ℚ))

    (Γ₁ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a₂, b₂])ˣ)
    (hΓ₁0 : ∀ x : (ℍ[ℚ, a₂, b₂])ˣ, x ∈ Γ₁ none ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ∧ Even (padicValRat q' (nrd (x : ℍ[ℚ, a₂, b₂]))))
    (hΓ₁ℓ : ∀ ℓ : HeckeTower.AwayPrime q q', Γ₁ (some ℓ) = Γ₁ none ⊓ (Γ₁ none).map (MulAut.conj (s₁ ℓ)).toMonoidHom)

    (w₁ wbar₁ : HeckeTower.Obj q q' → (ℍ[ℚ, a₂, b₂])ˣ)
    (hw₁ : (w₁ none ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ∧ nrd (w₁ none : ℍ[ℚ, a₂, b₂]) = (q' : ℚ)) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        w₁ (some ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits (meetOrder R₂ (sf₁ ℓ)) v₁ ∧ nrd (w₁ (some ℓ) : ℍ[ℚ, a₂, b₂]) = (q' : ℚ))
    (hwbar₁ :
      (nrd (wbar₁ none : ℍ[ℚ, a₂, b₂]) = (q : ℚ) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
          CosetGraph.toLoc u (wbar₁ none) ∈ Submodule.localBoxUnits R₂ u) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ∀ x : CosetGraph.Loc a₂ b₂ u,
          ((((CosetGraph.toLoc u (wbar₁ none))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
              ((CosetGraph.toLoc u (wbar₁ none) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox R₂ u ↔
            x ∈ Submodule.localBox R₂ u) ∧
          ((((CosetGraph.toLoc u (wbar₁ none))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
              ((CosetGraph.toLoc u (wbar₁ none) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox Λ₂ u ↔
            x ∈ Submodule.localBox Λ₂ u))) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        (nrd (wbar₁ (some ℓ) : ℍ[ℚ, a₂, b₂]) = (q : ℚ) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
            CosetGraph.toLoc u (wbar₁ (some ℓ)) ∈ Submodule.localBoxUnits (meetOrder R₂ (sf₁ ℓ)) u) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ∀ x : CosetGraph.Loc a₂ b₂ u,
            ((((CosetGraph.toLoc u (wbar₁ (some ℓ)))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
                ((CosetGraph.toLoc u (wbar₁ (some ℓ)) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox (meetOrder R₂ (sf₁ ℓ)) u ↔
              x ∈ Submodule.localBox (meetOrder R₂ (sf₁ ℓ)) u) ∧
            ((((CosetGraph.toLoc u (wbar₁ (some ℓ)))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
                ((CosetGraph.toLoc u (wbar₁ (some ℓ)) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox Λ₂ u ↔
              x ∈ Submodule.localBox Λ₂ u))))

    (dIso₁ : ↥(A₁.decompositionSubgroup ℚ) →* Omega.IsometricAut ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion)
    (hdIso₁ : ∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (x : A₁.valuation.Completion), (dIso₁ τ).toRingEquiv x = τ • x)

    (χ : ↥(A₁.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
    (hχ₁ : (∀ τ : ↥(A₁.decompositionSubgroup ℚ), (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A₁.inertiaSubgroupIn ℚ → χ τ = 1))
    (hχ₂ : (∀ φ : ↥(A₁.decompositionSubgroup ℚ), A₁.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) q' → χ φ ≠ 1))
    (hχ₃ : (∀ τ : ↥(A₁.decompositionSubgroup ℚ), χ τ = 1 ↔ ∀ x : IsLocalRing.ResidueField ↥A₁, x ^ (q' ^ 2) = x → τ • x = x))

    (𝒪₀ : Type) [CommRing 𝒪₀] [IsDomain 𝒪₀] [CharZero 𝒪₀] (hdvr₀ : IsDiscreteValuationRing 𝒪₀)
    (π : 𝒪₀) (hπ : Irreducible π) (hcpl : IsAdicComplete (Ideal.span {π}) 𝒪₀) (hres : Nat.card (𝒪₀ ⧸ Ideal.span {π}) = q')
    (hunr : Ideal.span {((q' : ℕ) : 𝒪₀)} = Ideal.span {π})
    [Algebra 𝒪₀ ↥(ValuationSubring.ratClosure A₁)] [IsFractionRing 𝒪₀ ↥(ValuationSubring.ratClosure A₁)]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪₀ Onr] (Fr : Onr ≃ₐ[𝒪₀] Onr)
    (hOc : IsAdicComplete (Ideal.span {algebraMap 𝒪₀ Onr π}) Onr)
    (hOm : (Ideal.span {algebraMap 𝒪₀ Onr π}).IsMaximal)
    (hOa : ∀ x : Onr, ∃ p : Polynomial 𝒪₀, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
    (hOcl : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ q' ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ↥(ValuationSubring.ratClosure A₁) →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ↥(ValuationSubring.ratClosure A₁)) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪₀ˣ, (Matrix.GeneralLinearGroup.det g : ↥(ValuationSubring.ratClosure A₁)) = algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁) (u : 𝒪₀) * (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁) π) ^ n)
    (ψ₀ : Onr →+* A₁.valuation.Completion)
    (hπϖ : algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁) π = ϖ₁.ϖ) (hN₀ : IsUnit ((N : ℕ) : 𝒪₀))
    (h𝒪₀ : ∀ x : ↥(ValuationSubring.ratClosure A₁), x ∈ Set.range (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)) ↔ Valued.v (algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion x) ≤ 1)
    (hψ₀ : ∀ y : Onr, Valued.v (ψ₀ y) ≤ 1)
    (hψ₀𝒪 : ψ₀.comp (algebraMap 𝒪₀ Onr) = (algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))
    (hrk : ∀ x y : A₁.valuation.Completion, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)

    (𝒳₀ : Scheme.{0}) (f₀ : 𝒳₀ ⟶ Spec (CommRingCat.of 𝒪₀))
    (pt₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)), FakeEllipticCurve Λ N S → SchemeHomOver s f₀)
    (h𝒳₀ : IsCoarseModuli Λ N 𝒳₀ f₀ pt₀) [IsIntegral 𝒳₀] [Flat f₀] [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (𝒴₀ : HeckeTower.AwayPrime q' q → Scheme.{0}) (g₀ : ∀ ℓ : HeckeTower.AwayPrime q' q, 𝒴₀ ℓ ⟶ Spec (CommRingCat.of 𝒪₀))
    (ptT₀ : ∀ (ℓ : HeckeTower.AwayPrime q' q) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g₀ ℓ))
    (h𝒴₀ : ∀ ℓ : HeckeTower.AwayPrime q' q, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴₀ ℓ) (g₀ ℓ) (ptT₀ ℓ))
    (d₀₀ d₁₀ : ∀ ℓ : HeckeTower.AwayPrime q' q, 𝒴₀ ℓ ⟶ 𝒳₀)
    (hd₀f : ∀ ℓ, d₀₀ ℓ ≫ f₀ = g₀ ℓ) (hd₁f : ∀ ℓ, d₁₀ ℓ ≫ f₀ = g₀ ℓ)
    (hd₀ : ∀ (ℓ : HeckeTower.AwayPrime q' q) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT₀ ℓ S s u).1 ≫ d₀₀ ℓ = (pt₀ S s u.1).1)
    (hd₁ : ∀ (ℓ : HeckeTower.AwayPrime q' q) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) u d → (ptT₀ ℓ S s u).1 ≫ d₁₀ ℓ = (pt₀ S s d).1)

    (ar arbar : 𝒳₀ ⟶ 𝒳₀) (harf : ar ≫ f₀ = f₀) (harbarf : arbar ≫ f₀ = f₀)
    (har : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient q' E E' → (pt₀ S s E).1 ≫ ar = (pt₀ S s E').1)
    (harbar : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient q E E' → (pt₀ S s E).1 ≫ arbar = (pt₀ S s E').1)

    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B → (Scheme.nilpPoints f₀).obj B)
    (ΘT : ∀ ℓ : HeckeTower.AwayPrime q' q, ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B → (Scheme.nilpPoints (g₀ ℓ)).obj B)
    (hCD :

      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
          (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), Θ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).map φ x) = (Scheme.nilpPoints f₀).map φ (Θ B hB x)) ∧
      (∀ ℓ : HeckeTower.AwayPrime q' q, (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
          (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), ΘT ℓ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).map φ x) = (Scheme.nilpPoints (g₀ ℓ)).map φ (ΘT ℓ B hB x))) ∧

      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₂, b₂])ˣ), γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ →
          ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) x x' → Θ B hB x' = Θ B hB x) ∧
      (∀ ℓ : HeckeTower.AwayPrime q' q, (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₂, b₂])ˣ), γ ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ⊓ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁).map (MulAut.conj (s₁ ⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩)).toMonoidHom) →
          ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) x x' → ΘT ℓ B hB x' = ΘT ℓ B hB x)) ∧

      (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪₀ k] (hk : IsNilpotent (algebraMap 𝒪₀ k π)) (ψ : Onr →ₐ[𝒪₀] k),
          (∀ y : (Scheme.nilpPoints f₀).obj k, ∃ P : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π).obj k, Θ k hk (ψ, P) = y) ∧
          ∀ P P' : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π).obj k, Θ k hk (ψ, P) = Θ k hk (ψ, P') ↔
            ∃ γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet k ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) (ψ, P) (ψ, P')) ∧
      (∀ ℓ : HeckeTower.AwayPrime q' q, (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪₀ k] (hk : IsNilpotent (algebraMap 𝒪₀ k π)) (ψ : Onr →ₐ[𝒪₀] k),
          (∀ y : (Scheme.nilpPoints (g₀ ℓ)).obj k, ∃ P : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π).obj k, ΘT ℓ k hk (ψ, P) = y) ∧
          ∀ P P' : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π).obj k, ΘT ℓ k hk (ψ, P) = ΘT ℓ k hk (ψ, P') ↔
            ∃ γ ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ⊓ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁).map (MulAut.conj (s₁ ⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩)).toMonoidHom), FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet k ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) (ψ, P) (ψ, P'))) ∧

      (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪₀))
          (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B → (Scheme.nilpPoints t).obj B),
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
            (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), ρ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₂, b₂])ˣ), γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ →
            ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) x x' → ρ B hB x' = ρ B hB x) →
          ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints f₀).obj B → (Scheme.nilpPoints t).obj B,
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
              (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints f₀).obj B), u B' hB' ((Scheme.nilpPoints f₀).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), u B hB (Θ B hB x) = ρ B hB x) ∧
            ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints f₀).obj B → (Scheme.nilpPoints t).obj B,
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
                (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints f₀).obj B), u' B' hB' ((Scheme.nilpPoints f₀).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), u' B hB (Θ B hB x) = ρ B hB x) →
              ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (y : (Scheme.nilpPoints f₀).obj B), u' B hB y = u B hB y) ∧
      (∀ ℓ : HeckeTower.AwayPrime q' q, (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪₀))
          (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B → (Scheme.nilpPoints t).obj B),
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
            (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), ρ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₂, b₂])ˣ), γ ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ⊓ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁).map (MulAut.conj (s₁ ⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩)).toMonoidHom) →
            ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) x x' → ρ B hB x' = ρ B hB x) →
          ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints (g₀ ℓ)).obj B → (Scheme.nilpPoints t).obj B,
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
              (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints (g₀ ℓ)).obj B), u B' hB' ((Scheme.nilpPoints (g₀ ℓ)).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), u B hB (ΘT ℓ B hB x) = ρ B hB x) ∧
            ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints (g₀ ℓ)).obj B → (Scheme.nilpPoints t).obj B,
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
                (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints (g₀ ℓ)).obj B), u' B' hB' ((Scheme.nilpPoints (g₀ ℓ)).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), u' B hB (ΘT ℓ B hB x) = ρ B hB x) →
              ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (y : (Scheme.nilpPoints (g₀ ℓ)).obj B), u' B hB y = u B hB y)) ∧

      (∀ (ℓ : HeckeTower.AwayPrime q' q) (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B),
        (Scheme.nilpPoints.mapHom (g₀ ℓ) f₀ (d₀₀ ℓ) (hd₀f ℓ)).app B (ΘT ℓ B hB x) = Θ B hB x) ∧
      (∀ (ℓ : HeckeTower.AwayPrime q' q) (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B),
        FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) (s₁ ⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩)) x' x →
        (Scheme.nilpPoints.mapHom (g₀ ℓ) f₀ (d₁₀ ℓ) (hd₁f ℓ)).app B (ΘT ℓ B hB x) = Θ B hB x') ∧

      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B),
        (Scheme.nilpPoints.mapHom f₀ f₀ ar harf).app B (Θ B hB x) = Θ B hB (FormalOmega.frobTwist Onr Fr 1 x.1, x.2)) ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) (wbar₁ none)) x x' →
        (Scheme.nilpPoints.mapHom f₀ f₀ arbar harbarf).app B (Θ B hB x) = Θ B hB x'))
    [hXCint : IsIntegral (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))]
    [hYCint : ∀ ℓ : HeckeTower.AwayPrime q' q, IsIntegral (Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))]

    (u : (Limits.pullback πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar)) ≅ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))))
    (hu : u.hom ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar))
    (hupt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of A₁.valuation.Completion)) (E : FakeEllipticCurve Λ N S),
        Limits.pullback.lift (pt S (s ≫ (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar)) E).1 s (pt S (s ≫ (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar)) E).2 ≫ u.hom =
          Limits.pullback.lift (pt₀ S (s ≫ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) E).1 s (pt₀ S (s ≫ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) E).2)

    (ℓ : HeckeTower.AwayPrime q q')

    [hYlft : LocallyOfFiniteType (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q))] [hYsep : IsSeparated (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q))]
    (dC₀ dC₁ : (Limits.pullback (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))))
    (hdC₀ : dC₀ ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.fst (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) ≫ d₀₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (hdC₀' : dC₀ ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.snd (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))
    (hdC₁ : dC₁ ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.fst (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) ≫ d₁₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (hdC₁' : dC₁ ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.snd (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))
    (hdom₀ : dC₀.base (genericPoint ((Limits.pullback (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) = (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0}))) (hdom₁ : dC₁.base (genericPoint ((Limits.pullback (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) = (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})))
    :
    ∀ (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ))
      (u' : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) A₁.valuation.Completion)
      (hu' : FakeEllipticCurve.WithExtraLevel.IsPullback (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)) (tw.repT ℓ P) u'),
      (Limits.pullback.lift (ptT₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q) A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) u').1 (𝟙 _)
            (by rw [Category.id_comp]; exact (ptT₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q) A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) u').2)) ≫ dC₀ ≫
          u.inv ≫ Limits.pullback.lift (Limits.pullback.fst πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar)) (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar) ≫ Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) (by simp only [Category.assoc, Limits.pullback.condition]) ≫ CategoryTheory.inv e𝔐 =
        Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ (𝔐.pointEquivPlace.symm (P.restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0)))).1 ∧
      (Limits.pullback.lift (ptT₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q) A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) u').1 (𝟙 _)
            (by rw [Category.id_comp]; exact (ptT₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q) A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) u').2)) ≫ dC₁ ≫
          u.inv ≫ Limits.pullback.lift (Limits.pullback.fst πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar)) (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ sbar) ≫ Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) (by simp only [Category.assoc, Limits.pullback.condition]) ≫ CategoryTheory.inv e𝔐 =
        Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))) ≫ (𝔐.pointEquivPlace.symm (P.restrictAlong (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 1)))).1 := by
  intro P u' hu'
  have hu'1 : FakeEllipticCurve.IsPullback (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)) (tw.repT ℓ P).1 u'.1 := by
    obtain ⟨g, hg, hmul, hact, hlev⟩ := hu'
    exact ⟨g, hg, hmul, hact, fun t' Q h => (hlev t' Q).1 h⟩
  obtain ⟨d, hdpb, hdiso⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_and_isLevelIsogeny_of_withExtraLevel_isPullback
    (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)) (ℓ.1 : ℕ) (tw.repT ℓ P) u' hu' (tw.rep (P.restrictAlong (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 1)))) (tw.restrict_one ℓ P)
  have hA₀ := hd₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q) A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) u'
  have hA₁ := hd₁ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q) A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) u' d hdiso
  have hB₀ := hupt A₁.valuation.Completion (𝟙 _) u'.1
  have hB₁ := hupt A₁.valuation.Completion (𝟙 _) d
  have hC₀ := pt_pullback (AlgebraicClosure ℚ) A₁.valuation.Completion (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)) sbar ((Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ sbar) rfl (tw.repT ℓ P).1 u'.1 hu'1
  have hC₁ := pt_pullback (AlgebraicClosure ℚ) A₁.valuation.Completion (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)) sbar ((Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ sbar) rfl _ d hdpb
  have hD₀ := pt_iso (AlgebraicClosure ℚ) sbar _ _ (tw.restrict_zero ℓ P)
  have hE₀ := tw.pt_rep (P.restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0)))
  have hE₁ := tw.pt_rep (P.restrictAlong (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 1)))

  have key : ∀ (E : FakeEllipticCurve Λ N A₁.valuation.Completion) (dC : (Limits.pullback (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))) (dd : 𝒴₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q) ⟶ 𝒳₀)
      (hfst : dC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.fst (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) ≫ dd)
      (hsnd : dC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.snd (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))
      (Q : Place (AlgebraicClosure ℚ) Fbar)
      (hptE : (ptT₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q) A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) u').1 ≫ dd = (pt₀ A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) E).1)
      (hpb : (pt A₁.valuation.Completion ((Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ sbar) E).1 = (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ (𝔐.pointEquivPlace.symm Q).1 ≫ e𝔐 ≫ Limits.pullback.fst πX sbar),
      (Limits.pullback.lift (ptT₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q) A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) u').1 (𝟙 _)
            (by rw [Category.id_comp]; exact (ptT₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q) A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) u').2)) ≫ dC ≫ u.inv ≫ (Limits.pullback.lift (Limits.pullback.fst πX ((Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ sbar)) (Limits.pullback.snd πX ((Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ sbar) ≫ (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))))) (by simp only [Category.assoc, Limits.pullback.condition])) ≫ CategoryTheory.inv e𝔐 = (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ (𝔐.pointEquivPlace.symm Q).1 := by
    intro E dC dd hfst hsnd Q hptE hpb

    have hpt₀ : (pt₀ A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) E).1 ≫ f₀ = 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) := by rw [Category.id_comp]; exact (pt₀ A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) E).2
    have hptX : (pt A₁.valuation.Completion ((Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ sbar) E).1 ≫ πX = 𝟙 _ ≫ ((Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ sbar) := by rw [Category.id_comp]; exact (pt A₁.valuation.Completion ((Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ sbar) E).2
    have h1 : (Limits.pullback.lift (ptT₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q) A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) u').1 (𝟙 _)
            (by rw [Category.id_comp]; exact (ptT₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q) A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) u').2)) ≫ dC = Limits.pullback.lift (pt₀ A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) E).1 (𝟙 _) hpt₀ := by
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, hfst, Limits.pullback.lift_fst_assoc, Limits.pullback.lift_fst, hptE]
      · rw [Category.assoc, hsnd, Limits.pullback.lift_snd, Limits.pullback.lift_snd]
    have hB := hupt A₁.valuation.Completion (𝟙 _) E
    have h2 : Limits.pullback.lift (pt A₁.valuation.Completion ((Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ sbar) E).1 (𝟙 _) hptX ≫ u.hom =
        Limits.pullback.lift (pt₀ A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) E).1 (𝟙 _) hpt₀ := by
      have el : Limits.pullback.lift (pt A₁.valuation.Completion (𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ sbar) E).1 (𝟙 _) (pt A₁.valuation.Completion (𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ sbar) E).2 =
          Limits.pullback.lift (pt A₁.valuation.Completion ((Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ sbar) E).1 (𝟙 _) hptX :=
        Limits.pullback.hom_ext (by rw [Limits.pullback.lift_fst, Limits.pullback.lift_fst]; exact congrArg (fun s => (pt A₁.valuation.Completion s E).1) (Category.id_comp _))
          (by rw [Limits.pullback.lift_snd, Limits.pullback.lift_snd])
      have er : Limits.pullback.lift (pt₀ A₁.valuation.Completion (𝟙 _ ≫ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) E).1 (𝟙 _) (pt₀ A₁.valuation.Completion (𝟙 _ ≫ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) E).2 =
          Limits.pullback.lift (pt₀ A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) E).1 (𝟙 _) hpt₀ :=
        Limits.pullback.hom_ext (by rw [Limits.pullback.lift_fst, Limits.pullback.lift_fst]; exact congrArg (fun s => (pt₀ A₁.valuation.Completion s E).1) (Category.id_comp _))
          (by rw [Limits.pullback.lift_snd, Limits.pullback.lift_snd])
      rw [← el, ← er]; exact hB
    have h2' : Limits.pullback.lift (pt₀ A₁.valuation.Completion (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) E).1 (𝟙 _) hpt₀ ≫ u.inv =
        Limits.pullback.lift (pt A₁.valuation.Completion ((Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ sbar) E).1 (𝟙 _) hptX := by
      rw [← h2, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h3 : Limits.pullback.lift (pt A₁.valuation.Completion ((Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ sbar) E).1 (𝟙 _) hptX ≫ (Limits.pullback.lift (Limits.pullback.fst πX ((Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ sbar)) (Limits.pullback.snd πX ((Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ sbar) ≫ (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom))))) (by simp only [Category.assoc, Limits.pullback.condition])) =
        (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₁.valuation).symm.toRingHom)))) ≫ (𝔐.pointEquivPlace.symm Q).1 ≫ e𝔐 := by
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst, hpb, Category.assoc, Category.assoc]
      · rw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc, Category.id_comp, Category.assoc, Category.assoc,
          he𝔐, (𝔐.pointEquivPlace.symm Q).2, Category.comp_id]
    rw [← Category.assoc, h1, ← Category.assoc, h2', ← Category.assoc, h3, Category.assoc, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  refine ⟨key u'.1 dC₀ (d₀₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) hdC₀ hdC₀' _ hA₀ ?_, key d dC₁ (d₁₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) hdC₁ hdC₁' _ hA₁ ?_⟩
  · rw [hC₀, show (pt (AlgebraicClosure ℚ) sbar (tw.repT ℓ P).1).1 = _ from congrArg Subtype.val hD₀, hE₀]
  · rw [hC₁, hE₁]

end S_CerednikDrinfeld_comp_degeneracy_eq_pointEquivPlace_symm_restrictAlong_of_withExtraLevel_isPullback_repT_of_iso_pullback_completion_one_zero_of_two_mul_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_comp_degeneracy_eq_pointEquivPlace_symm_restrictAlong_of_withExtraLevel_isPullback_repT_of_iso_pullback_completion_one_zero_of_two_mul_dvd (solution)
