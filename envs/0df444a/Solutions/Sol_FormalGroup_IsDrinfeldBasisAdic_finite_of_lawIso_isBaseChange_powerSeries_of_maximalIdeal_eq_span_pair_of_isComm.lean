-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.finite_of_lawIso_isBaseChange_powerSeries_of_maximalIdeal_eq_span_pair_of_isComm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/09cbad6d-fc6c-54d1-8de7-9776f42303cd

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
import Theorems.Thm_Module_Finite_of_isAdicComplete_of_isHausdorff_of_quotient
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_FormalGroup_IsBaseChange_exists_monic_natDegree_eq_mul_self_nthSeries_eq_mul
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_exists_maximalIdeal_eq_span_pair_and_eval_eq_zero_of_lawIso
import Theorems.Thm_IsLocalRing_exists_sub_sum_monomial_mem_of_maximalIdeal_eq_span_pair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_finite_of_lawIso_isBaseChange_powerSeries_of_maximalIdeal_eq_span_pair_of_isComm
p2m_attr_erase "instance" "MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.instIsCommAddMv MvFormalGroup.instIsCommOfFormalGroup"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries"

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
    (hmax : maximalIdeal R = Ideal.span {x₀, x₁})

    (Fu : FormalGroup (PowerSeries W₀)) [Fu.IsComm]
    (hFu : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀)
    (φ : PowerSeries W₀ →ₐ[W₀] R) (hφ : φ PowerSeries.X ∈ maximalIdeal R)

    (F' : FormalGroup R) [F'.IsComm] (hbc : Fu.IsBaseChange φ.toRingHom F') (ψ : FormalGroup.LawIso F' F)
    (hψ : ∀ n : ℕ, resR (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) :
    φ.toRingHom.Finite := by
  classical
  haveI hSc : IsAdicComplete (maximalIdeal (PowerSeries W₀)) (PowerSeries W₀) :=
    MvPowerSeries.isAdicComplete_maximalIdeal (σ := Unit) (R := W₀)
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le

  letI alg : Algebra (PowerSeries W₀) R := φ.toRingHom.toAlgebra
  have halg : ∀ s : PowerSeries W₀, algebraMap (PowerSeries W₀) R s = φ s := fun s => rfl

  have hqR : algebraMap W₀ R (q : W₀) ∈ maximalIdeal R := by
    rw [← hkerR, RingHom.mem_ker, hresR₀]
    have : (q : W₀) ∈ RingHom.ker res₀ := by
      rw [hker₀, hW₀]; exact Ideal.mem_span_singleton_self _
    exact this
  have hloc : ∀ s ∈ maximalIdeal (PowerSeries W₀), φ s ∈ maximalIdeal R := by
    intro s hs

    obtain ⟨s', hs'⟩ : ∃ s' : PowerSeries W₀, s = PowerSeries.C (PowerSeries.constantCoeff s) + PowerSeries.X * s' := by
      have hdvd : PowerSeries.X ∣ s - PowerSeries.C (PowerSeries.constantCoeff s) := by
        rw [PowerSeries.X_dvd_iff]; simp
      obtain ⟨s', hs'⟩ := hdvd
      exact ⟨s', by rw [← hs']; ring⟩
    have hc : PowerSeries.constantCoeff s ∈ maximalIdeal W₀ := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs ⊢
      rwa [PowerSeries.isUnit_iff_constantCoeff] at hs
    rw [hs', map_add, map_mul]
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hφ)
    have : φ (PowerSeries.C (PowerSeries.constantCoeff s)) = algebraMap W₀ R (PowerSeries.constantCoeff s) := by
      rw [PowerSeries.C_eq_algebraMap]
      exact φ.commutes _
    rw [this]
    rw [hW₀] at hc
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hc
    rw [← hc, map_mul]
    exact Ideal.mul_mem_left _ _ hqR

  have hres : ∀ r : R, ∃ w : W₀, r - algebraMap W₀ R w ∈ maximalIdeal R := by
    intro r
    obtain ⟨w, hw⟩ := hres₀ (resR r)
    exact ⟨w, by rw [← hkerR, RingHom.mem_ker, map_sub, hresR₀, hw, sub_self]⟩

  obtain ⟨P₀, U₀, hmonic, hdeg, hcoef, hU₀, hfac⟩ :=
    FormalGroup.IsBaseChange.exists_monic_natDegree_eq_mul_self_nthSeries_eq_mul q k W₀ res₀ hres₀ hker₀ F₀ hF₀ Fu hFu

  have hfac' : F'.nthSeries q =
      ((P₀.map φ.toRingHom : Polynomial R) : PowerSeries R) * PowerSeries.map φ.toRingHom U₀ := by
    rw [FormalGroup.IsBaseChange.nthSeries_eq_map Fu φ.toRingHom F' hbc q, hfac, map_mul,
      Polynomial.polynomial_map_coe]
  have hU' : IsUnit (PowerSeries.map φ.toRingHom U₀) := hU₀.map _

  obtain ⟨y₀, y₁, hy₀, hy₁, hmaxy, hP0, hP1⟩ :=
    FormalGroup.IsDrinfeldBasisAdic.exists_maximalIdeal_eq_span_pair_and_eval_eq_zero_of_lawIso
      F' F ψ q hq2 x₀ x₁ hx₀ hx₁ hD hmax (P₀.map φ.toRingHom) _ hU' hfac'

  set J : Ideal R := Ideal.map φ.toRingHom (maximalIdeal (PowerSeries W₀)) with hJ
  have hJle : J ≤ maximalIdeal R := by
    rw [hJ, Ideal.map_le_iff_le_comap]
    intro s hs
    exact hloc s hs

  have hyD : ∀ y : R, (P₀.map φ.toRingHom).eval y = 0 → y ^ (q * q) ∈ J := by
    intro y hy
    have hdeg' : (P₀.map φ.toRingHom).natDegree = q * q := by
      rw [hmonic.natDegree_map]; exact hdeg
    have hlead : (P₀.map φ.toRingHom).coeff (q * q) = 1 := by
      have := (hmonic.map φ.toRingHom).coeff_natDegree
      rwa [hdeg'] at this
    rw [Polynomial.eval_eq_sum_range, hdeg', Finset.sum_range_succ, hlead, one_mul] at hy
    have : y ^ (q * q) = -(∑ i ∈ Finset.range (q * q), (P₀.map φ.toRingHom).coeff i * y ^ i) := by
      linear_combination hy
    rw [this]
    refine neg_mem (Ideal.sum_mem _ fun i hi => ?_)
    rw [Polynomial.coeff_map]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hcoef i (Finset.mem_range.mp hi)))
  have hy₀D : y₀ ^ (q * q) ∈ J := hyD y₀ hP0
  have hy₁D : y₁ ^ (q * q) ∈ J := hyD y₁ hP1

  have hsmul : (maximalIdeal (PowerSeries W₀)) • (⊤ : Submodule (PowerSeries W₀) R) =
      J.restrictScalars (PowerSeries W₀) := by
    rw [Ideal.smul_top_eq_map]
    rfl
  have hquot : Module.Finite (PowerSeries W₀)
      (R ⧸ ((maximalIdeal (PowerSeries W₀)) • (⊤ : Submodule (PowerSeries W₀) R) : Submodule (PowerSeries W₀) R)) := by
    rw [hsmul]
    set N : Submodule (PowerSeries W₀) R := J.restrictScalars (PowerSeries W₀) with hN
    set idx : Finset (ℕ × ℕ) := Finset.range (q * q) ×ˢ Finset.range (q * q) with hidx
    set mons : Finset R := idx.image fun p => y₀ ^ p.1 * y₁ ^ p.2 with hmons
    refine ⟨⟨mons.image (Submodule.mkQ N), ?_⟩⟩
    rw [Finset.coe_image, Submodule.span_image, eq_top_iff]
    rintro z -
    obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective N z
    obtain ⟨c, hc⟩ := IsLocalRing.exists_sub_sum_monomial_mem_of_maximalIdeal_eq_span_pair
      y₀ y₁ hmaxy hres J (q * q) hy₀D hy₁D r
    refine Submodule.mem_map.mpr ⟨∑ p ∈ idx, (PowerSeries.C (c p) : PowerSeries W₀) • (y₀ ^ p.1 * y₁ ^ p.2), ?_, ?_⟩
    · refine Submodule.sum_mem _ fun p hp => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      rw [hmons, Finset.coe_image]
      exact ⟨p, Finset.mem_coe.mpr hp, rfl⟩
    · have hr2 : (∑ p ∈ idx, (PowerSeries.C (c p) : PowerSeries W₀) • (y₀ ^ p.1 * y₁ ^ p.2)) =
          ∑ p ∈ idx, algebraMap W₀ R (c p) * (y₀ ^ p.1 * y₁ ^ p.2) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Algebra.smul_def, halg, PowerSeries.C_eq_algebraMap, AlgHom.commutes]
      rw [hr2, eq_comm, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hN,
        Submodule.restrictScalars_mem]
      exact hc

  have hpow : ∀ n : ℕ, ((maximalIdeal (PowerSeries W₀)) ^ n • (⊤ : Submodule (PowerSeries W₀) R) :
      Submodule (PowerSeries W₀) R) ≤ ((maximalIdeal R) ^ n).restrictScalars (PowerSeries W₀) := by
    intro n
    rw [Ideal.smul_top_eq_map, Ideal.map_pow]
    intro x hx
    rw [Submodule.restrictScalars_mem] at hx ⊢
    exact Ideal.pow_right_mono (by rw [Ideal.map_le_iff_le_comap]; intro s hs; exact hloc s hs) n hx
  haveI hH : IsHausdorff (maximalIdeal (PowerSeries W₀)) R := by
    refine ⟨fun x hx => ?_⟩
    have hx' : ∀ n : ℕ, x ∈ (maximalIdeal R) ^ n := by
      intro n
      have h1 := hx n
      rw [SModEq.sub_mem, sub_zero] at h1
      exact hpow n h1
    refine IsHausdorff.haus' (I := maximalIdeal R) x fun n => ?_
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    exact hx' n

  have hfin : Module.Finite (PowerSeries W₀) R :=
    Module.Finite.of_isAdicComplete_of_isHausdorff_of_quotient (maximalIdeal (PowerSeries W₀)) R hquot
  exact hfin

end S_FormalGroup_IsDrinfeldBasisAdic_finite_of_lawIso_isBaseChange_powerSeries_of_maximalIdeal_eq_span_pair_of_isComm
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_finite_of_lawIso_isBaseChange_powerSeries_of_maximalIdeal_eq_span_pair_of_isComm (solution)
