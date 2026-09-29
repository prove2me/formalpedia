-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.existsUnique_algHom_powerSeries_lift_of_smallExtension_of_sqZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a2312856-ba8a-5a8a-90cb-cc120e56fc3d

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_algHom_eq_of_smallExtension_of_sqZero
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_exists_algHom_powerSeries_lift_of_smallExtension_of_sqZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_existsUnique_algHom_powerSeries_lift_of_smallExtension_of_sqZero
p2m_attr_erase "instance" "IsLocalRing.SmallExtension.algebra MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "IsLocalRing.SmallExtension.snd_pair IsLocalRing.SmallExtension.res_mk IsLocalRing.SmallExtension.snd_apply IsLocalRing.SmallExtension.coe_diag IsLocalRing.SmallExtension.fst_pair IsLocalRing.SmallExtension.fst_apply FormalGroup.ofPair_toPowerSeries IsLocalRing.SmallExtension.mk_thetaLiftAlgHom FormalGroup.LawIso.map_series IsLocalRing.SmallExtension.fst_pairRingHom FormalGroup.LawIso.ofPair_series FormalGroup.LawHom.ofPair_series IsLocalRing.SmallExtension.snd_pairRingHom IsLocalRing.SmallExtension.snd_pairAlgHom IsLocalRing.SmallExtension.fst_pairAlgHom FormalGroup.LawHom.map_series IsLocalRing.SmallExtension.fst_thetaLift IsLocalRing.SmallExtension.mk_thetaLift IsLocalRing.SmallExtension.fst_thetaLiftAlgHom MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (Fu : FormalGroup (PowerSeries W₀)) [Fu.IsComm]
    (hFu : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀)
    (hFu1 : (∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) → (maximalIdeal T) ^ 2 = ⊥ → (q : T) = 0 →
        ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
          ∃! φ : PowerSeries W₀ →ₐ[W₀] T,
            (∀ r : PowerSeries W₀, resT (φ r) = res₀ (PowerSeries.constantCoeff r)) ∧
            ∃ (G' : FormalGroup T) (_ : Fu.IsBaseChange φ.toRingHom G') (ψ : FormalGroup.LawIso G' G),
              ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0))

    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (hresT₀ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
    (S : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [Algebra W₀ S]
    (resS : S →+* k) (hresS : Function.Surjective resS) (hkerS : RingHom.ker resS = maximalIdeal S)
    (σ : T →ₐ[W₀] S) (hσ : Function.Surjective σ) (hσres : ∀ t : T, resS (σ t) = resT t)
    (hsmall : RingHom.ker σ.toRingHom * maximalIdeal T = ⊥)

    (G : FormalGroup T) [G.IsComm] (hG : G.IsBaseChange resT F₀)
    (Gσ : FormalGroup S) (hGσ : G.IsBaseChange σ.toRingHom Gσ)
    (φbar : PowerSeries W₀ →ₐ[W₀] S)
    (hφbar : ∀ r : PowerSeries W₀, resS (φbar r) = res₀ (PowerSeries.constantCoeff r))
    (Gbar' : FormalGroup S) (hbcbar : Fu.IsBaseChange φbar.toRingHom Gbar') (ψbar : FormalGroup.LawIso Gbar' Gσ)
    (hψbar : ∀ n : ℕ, resS (PowerSeries.coeff n ψbar.series) = if n = 1 then 1 else 0) :
    ∃! φ : PowerSeries W₀ →ₐ[W₀] T,
      σ.comp φ = φbar ∧
      ∃ (G' : FormalGroup T) (_ : Fu.IsBaseChange φ.toRingHom G') (ψ : FormalGroup.LawIso G' G),
        ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0 := by
  obtain ⟨φ, h1, G', hbc, ψ, hψ⟩ := FormalGroup.IsDrinfeldBasisAdic.exists_algHom_powerSeries_lift_of_smallExtension_of_sqZero q k W₀ hW₀ res₀ hres₀ hker₀ F₀ hF₀ Fu hFu hFu1 T resT hresT hkerT hresT₀ S resS hresS hkerS σ hσ hσres hsmall G hG Gσ hGσ φbar hφbar Gbar' hbcbar ψbar hψbar
  refine ⟨φ, ⟨h1, G', hbc, ψ, hψ⟩, ?_⟩
  rintro φ' ⟨h1', G'', hbc', ψ', hψ'⟩
  exact FormalGroup.IsDrinfeldBasisAdic.algHom_eq_of_smallExtension_of_sqZero q k W₀ hW₀ res₀ hres₀ hker₀ F₀ hF₀ Fu hFu hFu1 T resT hresT hkerT hresT₀ S resS hresS hkerS σ hσ hσres hsmall G hG Gσ hGσ φbar hφbar Gbar' hbcbar ψbar hψbar φ' φ h1' h1 G'' hbc' ψ' hψ' G' hbc ψ hψ

#print axioms solution

end S_FormalGroup_IsDrinfeldBasisAdic_existsUnique_algHom_powerSeries_lift_of_smallExtension_of_sqZero
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_existsUnique_algHom_powerSeries_lift_of_smallExtension_of_sqZero (solution)
