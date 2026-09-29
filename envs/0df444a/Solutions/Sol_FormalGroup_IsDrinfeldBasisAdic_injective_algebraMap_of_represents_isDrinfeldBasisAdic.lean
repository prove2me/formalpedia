-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.injective_algebraMap_of_represents_isDrinfeldBasisAdic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f59795e0-9620-544b-ae4c-6c49122b51d0

import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_exists_isDomain_injective_isDrinfeldBasisAdic
import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_injective_algebraMap_of_represents_isDrinfeldBasisAdic
p2m_attr_erase "instance" "MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.instIsCommAddMv MvFormalGroup.instIsCommOfFormalGroup"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries"

set_option autoImplicit false

open FormalGroup IsLocalRing

set_option maxHeartbeats 1600000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (Fu : FormalGroup (PowerSeries W₀)) [Fu.IsComm]
    (hFu : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀)
    (C : Type) [CommRing C] [Algebra (PowerSeries W₀) C] [IsLocalRing C]
    [Module.Finite (PowerSeries W₀) C] [IsAdicComplete (maximalIdeal C) C]
    (resC : C →+* k) (hresC : Function.Surjective resC) (hkerC : RingHom.ker resC = maximalIdeal C)
    (hresC₀ : ∀ f : PowerSeries W₀, resC (algebraMap (PowerSeries W₀) C f) = res₀ (PowerSeries.constantCoeff f))
    (Gc : FormalGroup C) (hGc : Fu.IsBaseChange (algebraMap (PowerSeries W₀) C) Gc)
    (c₀ c₁ : C) (hc₀ : c₀ ∈ maximalIdeal C) (hc₁ : c₁ ∈ maximalIdeal C)
    (hcD : Gc.IsDrinfeldBasisAdic (maximalIdeal C) q c₀ c₁)
    (hCuniv : ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra (PowerSeries W₀) B] [IsAdicComplete (maximalIdeal B) B]
        (G : FormalGroup B), Fu.IsBaseChange (algebraMap (PowerSeries W₀) B) G →
        ∀ (y₀ y₁ : B), y₀ ∈ maximalIdeal B → y₁ ∈ maximalIdeal B →
          G.IsDrinfeldBasisAdic (maximalIdeal B) q y₀ y₁ →
          ∃! χ : C →ₐ[PowerSeries W₀] B, χ c₀ = y₀ ∧ χ c₁ = y₁) :
    Function.Injective (algebraMap (PowerSeries W₀) C) := by
  obtain ⟨V, _, _, _, _, _, hinjV, G, hG, α, β, hα, hβ, hD⟩ :=
    FormalGroup.IsDrinfeldBasisAdic.exists_isDomain_injective_isDrinfeldBasisAdic q k W₀ hW₀ res₀ hres₀ hker₀ F₀ hF₀ Fu hFu
  obtain ⟨χ, -, -⟩ := hCuniv V G hG α β hα hβ hD
  intro a b h
  apply hinjV
  rw [← χ.commutes a, ← χ.commutes b, h]

end S_FormalGroup_IsDrinfeldBasisAdic_injective_algebraMap_of_represents_isDrinfeldBasisAdic
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_injective_algebraMap_of_represents_isDrinfeldBasisAdic (solution)
