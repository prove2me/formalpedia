-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.exists_isDomain_injective_isDrinfeldBasisAdic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/915063a2-5928-5377-89bd-6ea2365584c3

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_FormalGroup_IsBaseChange_exists_monic_natDegree_eq_mul_self_nthSeries_eq_mul
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
import Theorems.Thm_Polynomial_exists_isDomain_isLocalRing_moduleFinite_eq_prod_X_sub_C_of_monic_of_coeff_mem_maximalIdeal
import Theorems.Thm_FormalGroup_derivative_eval_ne_zero_of_nthSeries_eq_mul
import Theorems.Thm_FormalGroup_exists_isDrinfeldBasisAdic_of_nthSeries_eq_prod_mul_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_isDomain_injective_isDrinfeldBasisAdic
p2m_attr_erase "instance" "MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.instIsCommAddMv MvFormalGroup.instIsCommOfFormalGroup"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries"

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace DW2R4b

theorem isComm_map {R S : Type*} [CommRing R] [CommRing S] (F : FormalGroup R) [hF : F.IsComm] (f : R →+* S) :
    (F.map f).IsComm := by
  constructor
  show (F.map f).toPowerSeries = MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] (F.map f).toPowerSeries
  have h : F.toPowerSeries = MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] F.toPowerSeries := hF.comm
  have hswap : (fun i => MvPowerSeries.map f
      ((![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R) i)) =
      (![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) S) := by
    funext i; fin_cases i <;> simp [MvPowerSeries.map_X]
  rw [FormalGroup.map_toPowerSeries]
  conv_lhs => rw [h]
  rw [MvPowerSeries.map_subst MvPowerSeries.HasSubst.X_X, hswap]

theorem derivative_prod_eval_eq_zero {V : Type*} [CommRing V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → V) {i j : ι} (hij : i ≠ j) (h : r i = r j) :
    (Polynomial.derivative (∏ l, (Polynomial.X - Polynomial.C (r l)))).eval (r i) = 0 := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
    ← Finset.prod_erase_mul _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  simp [Polynomial.derivative_mul, h]

end DW2R4b

set_option maxHeartbeats 3200000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (Fu : FormalGroup (PowerSeries W₀)) [Fu.IsComm]
    (hFu : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (_ : Algebra (PowerSeries W₀) V)
      (_ : IsAdicComplete (maximalIdeal V) V),
      Function.Injective (algebraMap (PowerSeries W₀) V) ∧
      ∃ (G : FormalGroup V) (_ : Fu.IsBaseChange (algebraMap (PowerSeries W₀) V) G) (α β : V),
        α ∈ maximalIdeal V ∧ β ∈ maximalIdeal V ∧ G.IsDrinfeldBasisAdic (maximalIdeal V) q α β := by
  classical
  haveI : IsAdicComplete (maximalIdeal (PowerSeries W₀)) (PowerSeries W₀) :=
    MvPowerSeries.isAdicComplete_maximalIdeal (σ := Unit) (R := W₀)

  obtain ⟨P, U, hPm, hdeg, hP𝔪, hU, hPU⟩ :=
    FormalGroup.IsBaseChange.exists_monic_natDegree_eq_mul_self_nthSeries_eq_mul q k W₀ res₀ hres₀ hker₀ F₀ hF₀ Fu hFu
  have hqpos : 0 < q := (Fact.out : q.Prime).pos
  have hdegpos : 0 < P.natDegree := by rw [hdeg]; exact Nat.mul_pos hqpos hqpos

  obtain ⟨V, iV1, iV2, iV3, iV4, iV5, iV6, hinj, -, r, hr, hsplit⟩ :=
    Polynomial.exists_isDomain_isLocalRing_moduleFinite_eq_prod_X_sub_C_of_monic_of_coeff_mem_maximalIdeal P hPm hdegpos
      (fun i hi => hP𝔪 i (hdeg ▸ hi))

  have hqW : (q : W₀) ≠ 0 := by
    intro h
    have hbot : maximalIdeal W₀ = ⊥ := by rw [hW₀, h, Ideal.span_singleton_eq_bot]
    exact IsDiscreteValuationRing.not_isField W₀ (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)
  have hqS : (q : PowerSeries W₀) ≠ 0 := by
    intro h
    apply hqW
    have := congrArg (PowerSeries.constantCoeff (R := W₀)) h
    rwa [map_natCast, map_zero] at this
  have hqV : (q : V) ≠ 0 := by
    intro h
    apply hqS
    apply hinj
    rw [map_natCast, map_zero, h]

  let G : FormalGroup V := Fu.map (algebraMap (PowerSeries W₀) V)
  haveI : G.IsComm := DW2R4b.isComm_map Fu _
  have hbc : Fu.IsBaseChange (algebraMap (PowerSeries W₀) V) G := rfl
  have hU' : IsUnit (PowerSeries.map (algebraMap (PowerSeries W₀) V) U) := hU.map _
  have hqG : G.nthSeries q = ((∏ i, (Polynomial.X - Polynomial.C (r i)) : Polynomial V) : PowerSeries V) *
      PowerSeries.map (algebraMap (PowerSeries W₀) V) U := by
    rw [FormalGroup.IsBaseChange.nthSeries_eq_map Fu (algebraMap (PowerSeries W₀) V) G hbc q, hPU, map_mul,
      ← Polynomial.polynomial_map_coe, hsplit]

  have hrinj : Function.Injective r := by
    intro i j hij
    by_contra hne
    have hroot : (∏ l, (Polynomial.X - Polynomial.C (r l))).eval (r i) = 0 := by
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    exact FormalGroup.derivative_eval_ne_zero_of_nthSeries_eq_mul q hqV G _ _ hU' hqG (r i) (hr i) hroot
      (DW2R4b.derivative_prod_eval_eq_zero r hne hij)

  let e : Fin (q * q) ≃ Fin P.natDegree := finCongr hdeg.symm
  have hprod : (∏ a, (Polynomial.X - Polynomial.C (r (e a))) : Polynomial V) = ∏ b, (Polynomial.X - Polynomial.C (r b)) :=
    Fintype.prod_equiv e (fun a => Polynomial.X - Polynomial.C (r (e a))) (fun b => Polynomial.X - Polynomial.C (r b))
      (fun a => rfl)
  rw [← hprod] at hqG

  obtain ⟨α, β, hα, hβ, hD⟩ :=
    FormalGroup.exists_isDrinfeldBasisAdic_of_nthSeries_eq_prod_mul_of_injective q G (r ∘ e)
      (fun a => hr (e a)) (hrinj.comp e.injective) _ hU' hqG
  exact ⟨V, iV1, iV2, iV3, iV4, iV6, hinj, G, hbc, α, β, hα, hβ, hD⟩

end S_FormalGroup_IsDrinfeldBasisAdic_exists_isDomain_injective_isDrinfeldBasisAdic
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_isDomain_injective_isDrinfeldBasisAdic (solution)
