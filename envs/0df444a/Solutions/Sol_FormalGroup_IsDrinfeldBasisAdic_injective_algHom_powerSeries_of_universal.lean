-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.injective_algHom_powerSeries_of_universal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f08f07de-cce8-5fef-9c23-7e7e00e27c89

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_exists_moduleFinite_isLocalRing_represents_isDrinfeldBasisAdic
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_injective_algebraMap_of_represents_isDrinfeldBasisAdic
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_injective_algHom_powerSeries_of_universal_of_cover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_injective_algHom_powerSeries_of_universal
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.instIsCommAddMv MvFormalGroup.instIsCommOfFormalGroup"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries"

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (R : Type) [CommRing R] [IsLocalRing R] [Algebra W₀ R] [IsAdicComplete (maximalIdeal R) R] [IsNoetherianRing R]
    (resR : R →+* k) (hresR : Function.Surjective resR) (hkerR : RingHom.ker resR = maximalIdeal R)
    (hresR₀ : ∀ w : W₀, resR (algebraMap W₀ R w) = res₀ w)
    (F : FormalGroup R) [F.IsComm] (hF : F.IsBaseChange resR F₀)
    (x₀ x₁ : R) (hx₀ : x₀ ∈ maximalIdeal R) (hx₁ : x₁ ∈ maximalIdeal R)
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q x₀ x₁)

    (huniv : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
        ∀ (y₀ y₁ : T), y₀ ∈ maximalIdeal T → y₁ ∈ maximalIdeal T →
        G.IsDrinfeldBasisAdic (maximalIdeal T) q y₀ y₁ →
          ∃! φ : R →ₐ[W₀] T, (∀ r : R, resT (φ r) = resR r) ∧
            ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ.toRingHom F') (ψ : FormalGroup.LawIso F' G),
              (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
              ψ.toLawHom.appAdic (maximalIdeal T) (φ x₀) = y₀ ∧ ψ.toLawHom.appAdic (maximalIdeal T) (φ x₁) = y₁)
    (Fu : FormalGroup (PowerSeries W₀)) [Fu.IsComm]
    (hFu : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀)
    (hLT : (∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
          (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
          (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
          ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
            ∃! φ : PowerSeries W₀ →ₐ[W₀] T,
              (∀ r : PowerSeries W₀, resT (φ r) = res₀ (PowerSeries.constantCoeff r)) ∧
              ∃ (G' : FormalGroup T) (_ : Fu.IsBaseChange φ.toRingHom G') (ψ : FormalGroup.LawIso G' G),
                ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0))
    (φ : PowerSeries W₀ →ₐ[W₀] R)
    (hφres : ∀ r : PowerSeries W₀, resR (φ r) = res₀ (PowerSeries.constantCoeff r))
    (F' : FormalGroup R) (hbc : Fu.IsBaseChange φ.toRingHom F') (ψ : FormalGroup.LawIso F' F)
    (hψ : ∀ n : ℕ, resR (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) :
    Function.Injective φ := by
  obtain ⟨C, instC, instA, instL, instF, instAd, resC, hresC, hkerC, hresC₀, Gc, hGc, c₀, c₁, hc₀, hc₁, hcD, hCuniv⟩ :=
    FormalGroup.IsDrinfeldBasisAdic.exists_moduleFinite_isLocalRing_represents_isDrinfeldBasisAdic
      q k W₀ hW₀ res₀ hres₀ hker₀ F₀ hF₀ Fu hFu
  letI := instC; letI := instA; letI := instL; letI := instF; letI := instAd
  have hinj : Function.Injective (algebraMap (PowerSeries W₀) C) :=
    FormalGroup.IsDrinfeldBasisAdic.injective_algebraMap_of_represents_isDrinfeldBasisAdic
      q k W₀ hW₀ res₀ hres₀ hker₀ F₀ hF₀ Fu hFu C resC hresC hkerC hresC₀ Gc hGc c₀ c₁ hc₀ hc₁ hcD hCuniv
  exact FormalGroup.IsDrinfeldBasisAdic.injective_algHom_powerSeries_of_universal_of_cover
    q k W₀ hW₀ res₀ hres₀ hker₀ F₀ hF₀ R resR hresR hkerR hresR₀ F hF x₀ x₁ hx₀ hx₁ hD huniv Fu hFu hLT φ hφres F' hbc ψ hψ
    C resC hresC hkerC hresC₀ Gc hGc c₀ c₁ hc₀ hc₁ hcD hinj

end S_FormalGroup_IsDrinfeldBasisAdic_injective_algHom_powerSeries_of_universal
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_injective_algHom_powerSeries_of_universal (solution)
