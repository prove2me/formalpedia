-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_isRegularLocalRing_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/4b0bd5a3-eea6-579c-8f60-74882ddf8dde

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_Ideal_mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq_of_natCast_mem
import Theorems.Thm_IsLocalRing_exists_isDiscreteValuationRing_ringHom_of_finite_residueField
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_exists_natCast_eq_mul_prod_pow_sub_one_of_isAdicComplete
import Theorems.Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two
import Theorems.Thm_Associated_of_pow_eq_units_mul_pow
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_IsRegularLocalRing_exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_eq_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_isRegularLocalRing_of_prime
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.instIsCommAddMv MvFormalGroup.instIsCommOfFormalGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries"

set_option autoImplicit false

open IsLocalRing

namespace ChartAllq

theorem ramifiedCoef
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Finite (ResidueField R)]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    (ι : A →+* R) [IsLocalHom ι] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (σ : A →+* W) (_ : maximalIdeal W = Ideal.span {σ ϖ})
      (g : W →+* R) (_ : IsLocalHom g),
      g.comp σ = ι ∧ ∀ r : R, ∃ w : W, r - g w ∈ maximalIdeal R := by
  letI : Algebra A R := ι.toAlgebra
  haveI : IsLocalHom (algebraMap A R) := ‹IsLocalHom ι›
  obtain ⟨W, iW1, iW2, iW3, iW4, σ, hσ, τ, hτ, hsurj, hcomp⟩ :=
    IsLocalRing.exists_isDiscreteValuationRing_ringHom_of_finite_residueField A ϖ hϖ R
  refine ⟨W, iW1, iW2, iW3, iW4, σ, hσ, τ, hτ, hcomp, fun r => ?_⟩
  obtain ⟨w, hw⟩ := hsurj (residue R r)
  refine ⟨w, ?_⟩
  rw [RingHom.comp_apply] at hw
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact hw.symm

theorem chart
    (q : ℕ) [Fact q.Prime]
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (hreg : IsRegularLocalRing R) (hdim : ringKrullDim R = 2)
    (hchar : CharP (ResidueField R) q) [Finite (ResidueField R)]
    (F : FormalGroup R) [F.IsComm]
    (x₀ x₁ : R) (hmax : maximalIdeal R = Ideal.span {x₀, x₁})
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q x₀ x₁)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) (ε : A) (hε : IsUnit ε) (hϖq : ϖ ^ (q - 1) = ε * (q : A))
    (ι : A →+* R) [IsLocalHom ι] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (σ : A →+* W)
      (_ : maximalIdeal W = Ideal.span {σ ϖ})
      (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
      (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
      (e : R ≃+* MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u}),
      (∀ a : A, e (ι a) = Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) ∧
      e x₀ = Ideal.Quotient.mk _ (MvPowerSeries.X 0) ∧ e x₁ = Ideal.Quotient.mk _ (MvPowerSeries.X 1) := by

  have hx₀ : x₀ ∈ maximalIdeal R := hmax ▸ Ideal.subset_span (by simp)
  have hx₁ : x₁ ∈ maximalIdeal R := hmax ▸ Ideal.subset_span (by simp)

  obtain ⟨W, _, _, _, _, σ, hσ, g, _, hgσ, hres⟩ :=
    ramifiedCoef R A ϖ hϖ ι

  obtain ⟨u, hu, P, hP, hq'⟩ := FormalGroup.IsDrinfeldBasisAdic.exists_natCast_eq_mul_prod_pow_sub_one_of_isAdicComplete q R F x₀ x₁ hx₀ hx₁ hD
  set Fd : R := x₀ * ∏ c : ZMod q, P c with hFd

  haveI : IsRegularLocalRing R := hreg
  haveI : IsDomain R := IsRegularLocalRing.isDomain R
  haveI : UniqueFactorizationMonoid R := IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two R (le_of_eq hdim)

  have hιq : ι ((q : ℕ) : A) = ((q : ℕ) : R) := map_natCast ι q
  have hpow : (ι ϖ) ^ (q - 1) = (ι ε * u) * Fd ^ (q - 1) := by
    rw [← map_pow, hϖq, map_mul, hιq, hq', mul_assoc]
  have hunit : IsUnit (ι ε * u) := (hε.map ι).mul hu
  obtain ⟨w, hw⟩ : Associated (ι ϖ) Fd := by
    have hq1 : q - 1 ≠ 0 := by
      have := (Fact.out : q.Prime).two_le
      omega
    exact Associated.of_pow_eq_units_mul_pow (ι ϖ) Fd (q - 1) hq1 hunit.unit (by simpa using hpow)

  have hπF : g (σ ϖ) = ((w⁻¹ : Rˣ) : R) * Fd := by
    have : ι ϖ = g (σ ϖ) := by rw [← RingHom.comp_apply, hgσ]
    rw [← this, ← hw, mul_comm (ι ϖ) (w : R), ← mul_assoc, Units.inv_mul, one_mul]

  have hFd_mem : Fd ∈ maximalIdeal R ^ (q + 1) := by
    have h1 : (∏ c : ZMod q, P c) ∈ maximalIdeal R ^ q := by
      have hPc : ∀ c : ZMod q, P c ∈ maximalIdeal R := by
        intro c
        have h2 : P c - (x₁ + ((c.val : ℕ) : R) * x₀) ∈ maximalIdeal R :=
          Ideal.pow_le_self (by norm_num) (hP c)
        have h3 : x₁ + ((c.val : ℕ) : R) * x₀ ∈ maximalIdeal R :=
          Ideal.add_mem _ hx₁ (Ideal.mul_mem_left _ _ hx₀)
        simpa using Ideal.add_mem _ h2 h3
      have := Ideal.prod_mem_prod (s := (Finset.univ : Finset (ZMod q))) (fun c _ => hPc c)
      simpa [Finset.prod_const, ZMod.card] using this
    have : x₀ * ∏ c : ZMod q, P c ∈ maximalIdeal R ^ (1 + q) := by
      rw [pow_add]; exact Ideal.mul_mem_mul (by simpa using hx₀) h1
    simpa [hFd, add_comm] using this
  have hqmem : ((q : ℕ) : R) ∈ maximalIdeal R := by
    have hq1 : q - 1 ≠ 0 := by
      have := (Fact.out : q.Prime).two_le
      omega
    rw [hq']
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Ideal.pow_le_self (by omega) hFd_mem) _ (Nat.pos_of_ne_zero hq1))

  have hF : Fd - (x₀ * x₁ ^ q - x₀ ^ q * x₁) ∈ maximalIdeal R ^ (q + 2) :=
    Ideal.mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq_of_natCast_mem q R (maximalIdeal R) hqmem x₀ x₁ hx₀ hx₁ P hP

  obtain ⟨f, u', v, hu', hv, hf, e, hconst, he₀, he₁⟩ :=
    IsRegularLocalRing.exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_eq_mul q R hreg hdim x₀ x₁ hmax W (σ ϖ) hσ g hres Fd ((w⁻¹ : Rˣ) : R) (Units.isUnit _) hπF hF
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, σ, hσ, f, u', v, hu', hv, hf, e, ?_, he₀, he₁⟩
  intro a
  have hιa : g (σ a) = ι a := by rw [← RingHom.comp_apply, hgσ]
  simpa only [hιa] using hconst (σ a)

end ChartAllq

theorem solution
    (q : ℕ) [Fact q.Prime]
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (hreg : IsRegularLocalRing R) (hdim : ringKrullDim R = 2)
    (hchar : CharP (ResidueField R) q) [Finite (ResidueField R)]
    (F : FormalGroup R) [F.IsComm]
    (x₀ x₁ : R) (hmax : maximalIdeal R = Ideal.span {x₀, x₁})
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q x₀ x₁)

    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) (ε : A) (hε : IsUnit ε) (hϖq : ϖ ^ (q - 1) = ε * (q : A))
    (ι : A →+* R) [IsLocalHom ι] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (σ : A →+* W)
      (_ : maximalIdeal W = Ideal.span {σ ϖ})
      (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
      (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
      (e : R ≃+* MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u}),
      (∀ a : A, e (ι a) = Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) ∧
      e x₀ = Ideal.Quotient.mk _ (MvPowerSeries.X 0) ∧ e x₁ = Ideal.Quotient.mk _ (MvPowerSeries.X 1) :=
  ChartAllq.chart q R hreg hdim hchar F x₀ x₁ hmax hD A ϖ hϖ ε hε hϖq ι

end S_FormalGroup_IsDrinfeldBasisAdic_exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_isRegularLocalRing_of_prime
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_isRegularLocalRing_of_prime (solution)
