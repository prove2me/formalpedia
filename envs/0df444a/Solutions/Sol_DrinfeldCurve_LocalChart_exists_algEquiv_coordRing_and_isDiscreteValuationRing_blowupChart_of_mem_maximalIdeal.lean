-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.exists_algEquiv_coordRing_and_isDiscreteValuationRing_blowupChart_of_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/fd534447-7c79-5486-b75a-68fdb646aedb

import Mathlib
import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_DrinfeldCurve_LocalChart
import Theorems.Thm_DrinfeldCurve_LocalChart_exists_isPrime_algEquiv_coordRing_blowupChart_quotient_of_mem_maximalIdeal
import Theorems.Thm_IsLocalRing_isDomain_and_isPrincipalIdealRing_of_maximalIdeal_eq_span_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_exists_algEquiv_coordRing_and_isDiscreteValuationRing_blowupChart_of_mem_maximalIdeal

set_option autoImplicit false

noncomputable section

open MvPowerSeries IsLocalRing DrinfeldCurve DrinfeldCurve.LocalChart

namespace B34Assembly

theorem dvr_of_span_singleton_nonZeroDivisor {R : Type*} [CommRing R] [IsNoetherianRing R] (τ : R)
    (P : Ideal R) [P.IsPrime] (hPτ : P = Ideal.span {τ}) (hτ : τ ∈ nonZeroDivisors R) :
    ∃ (_ : IsDomain (Localization.AtPrime P)),
      IsDiscreteValuationRing (Localization.AtPrime P) ∧
      maximalIdeal (Localization.AtPrime P) =
        Ideal.span {algebraMap R (Localization.AtPrime P) τ} := by
  subst hPτ
  have hmax : maximalIdeal (Localization.AtPrime (Ideal.span {τ})) =
      Ideal.span {algebraMap R (Localization.AtPrime (Ideal.span {τ})) τ} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hpow : ∀ n : ℕ, (algebraMap R (Localization.AtPrime (Ideal.span {τ})) τ) ^ n ≠ 0 := by
    intro n h
    rw [← map_pow, IsLocalization.map_eq_zero_iff (Ideal.span {τ}).primeCompl] at h
    obtain ⟨s, hs⟩ := h
    have hs0 : (s : R) = 0 := (mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hτ n)).mp hs
    exact s.2 (hs0 ▸ Ideal.zero_mem _)
  obtain ⟨hdom, hpir⟩ :=
    IsLocalRing.isDomain_and_isPrincipalIdealRing_of_maximalIdeal_eq_span_singleton
      (algebraMap R (Localization.AtPrime (Ideal.span {τ})) τ) hmax hpow
  refine ⟨hdom, ?_, hmax⟩
  have hne : maximalIdeal (Localization.AtPrime (Ideal.span {τ})) ≠ ⊥ := by
    intro hbot
    have hmem : algebraMap R (Localization.AtPrime (Ideal.span {τ})) τ ∈
        maximalIdeal (Localization.AtPrime (Ideal.span {τ})) := by
      rw [hmax]; exact Ideal.mem_span_singleton_self _
    rw [hbot, Ideal.mem_bot] at hmem
    exact hpow 1 (by rw [pow_one]; exact hmem)
  exact { toIsPrincipalIdealRing := hpir, not_a_field' := hne }

theorem residueField_atPrime {k R A : Type*} [Field k] [CommRing R] [CommRing A]
    (P : Ideal R) [P.IsPrime] [Algebra k (R ⧸ P)] [Algebra k A] (e : (R ⧸ P) ≃ₐ[k] A) :
    ∃ (algW : Algebra k (ResidueField (Localization.AtPrime P)))
      (_ : ∀ x : k, algebraMap k (ResidueField (Localization.AtPrime P)) x =
        algebraMap (R ⧸ P) P.ResidueField (algebraMap k (R ⧸ P) x))
      (_ : ∀ r : R, algebraMap (R ⧸ P) P.ResidueField (Ideal.Quotient.mk P r) =
        residue (Localization.AtPrime P) (algebraMap R _ r))
      (eW : ResidueField (Localization.AtPrime P) ≃ₐ[k] FractionRing A),
      ∀ r : R, eW (residue (Localization.AtPrime P) (algebraMap R _ r)) =
        algebraMap A (FractionRing A) (e (Ideal.Quotient.mk P r)) := by
  letI algW : Algebra k (ResidueField (Localization.AtPrime P)) :=
    ((algebraMap (R ⧸ P) P.ResidueField).comp (algebraMap k (R ⧸ P))).toAlgebra
  haveI : IsScalarTower k (R ⧸ P) P.ResidueField := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmk : ∀ r : R, algebraMap (R ⧸ P) P.ResidueField (Ideal.Quotient.mk P r) =
      residue (Localization.AtPrime P) (algebraMap R _ r) := by
    intro r
    rw [Ideal.algebraMap_quotient_residueField_mk,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime P) P.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq]
  refine ⟨algW, fun _ => rfl, hmk, IsFractionRing.algEquivOfAlgEquiv e, fun r => ?_⟩
  rw [← hmk, IsFractionRing.algEquivOfAlgEquiv_algebraMap]

end B34Assembly

theorem solution
    (q : ℕ) [Fact q.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (GaloisField q 2) (ResidueField O)]
    [IsAlgClosed (ResidueField O)] [IsDomain (CoordRing q (ResidueField O))]
    (π : O) (hπ : maximalIdeal O = Ideal.span {π})
    (ϖ : O) (hϖ : ϖ ∈ maximalIdeal O) (hϖ0 : ϖ ≠ 0)
    (pr : ChartPresentation q O ϖ)
    (hnzd : Ideal.Quotient.mk (Ideal.span {pr.rel}) (C ϖ) ∈ nonZeroDivisors pr.Ring) :
    let S := pr.Ring
    let mkS : MvPowerSeries (Fin 2) O →+* S := Ideal.Quotient.mk _
    let L := Localization.Away (mkS (C ϖ))
    let ι₀ : O →+* L := (algebraMap S L).comp (mkS.comp (C (σ := Fin 2) (R := O)))
    let x₀ : L := algebraMap S L (mkS (X 0)) * IsLocalization.Away.invSelf (S := L) (mkS (C ϖ))
    let x₁ : L := algebraMap S L (mkS (X 1)) * IsLocalization.Away.invSelf (S := L) (mkS (C ϖ))
    let R : Subring L := Subring.closure (Set.range (algebraMap S L) ∪ {x₀, x₁})
    ∃ (hι₀ : ∀ o : O, ι₀ o ∈ R) (hx₀ : x₀ ∈ R) (hx₁ : x₁ ∈ R)
      (P : Ideal ↥R) (_ : P = Ideal.span {(⟨ι₀ π, hι₀ π⟩ : ↥R)})
      (_ : IsNoetherianRing ↥R) (hP : P.IsPrime)
      (algR : Algebra (ResidueField O) (↥R ⧸ P))
      (_ : ∀ a : O, algebraMap (ResidueField O) (↥R ⧸ P) (residue O a) = Ideal.Quotient.mk P ⟨ι₀ a, hι₀ a⟩)
      (eR : (↥R ⧸ P) ≃ₐ[ResidueField O] CoordRing q (ResidueField O))
      (c : ResidueField O),

      (∀ s : S, (∃ a ∈ maximalIdeal O, ∃ g₀ g₁ : MvPowerSeries (Fin 2) O, s = mkS (C a + X 0 * g₀ + X 1 * g₁)) →
        ∃ h : algebraMap S L s ∈ R, (⟨_, h⟩ : ↥R) ∈ P) ∧

      c ≠ 0 ∧
      c ^ (q + 1) * residue O (MvPowerSeries.constantCoeff pr.u) = residue O (MvPowerSeries.constantCoeff pr.v) ∧
      eR (Ideal.Quotient.mk P ⟨x₀, hx₀⟩) =
        algebraMap (ResidueField O) (CoordRing q (ResidueField O)) c * x q (ResidueField O) ∧
      eR (Ideal.Quotient.mk P ⟨x₁, hx₁⟩) =
        algebraMap (ResidueField O) (CoordRing q (ResidueField O)) c * y q (ResidueField O) ∧

      (letI := hP
       ∃ (_ : IsDomain (Localization.AtPrime P)),
       IsDiscreteValuationRing (Localization.AtPrime P) ∧
       maximalIdeal (Localization.AtPrime P) =
         Ideal.span {algebraMap (↥R) (Localization.AtPrime P) ⟨ι₀ π, hι₀ π⟩} ∧
       ∃ (algW : Algebra (ResidueField O) (ResidueField (Localization.AtPrime P)))
         (_ : ∀ a : O, algebraMap (ResidueField O) (ResidueField (Localization.AtPrime P)) (residue O a) =
           residue (Localization.AtPrime P) (algebraMap (↥R) _ ⟨ι₀ a, hι₀ a⟩))
         (eW : ResidueField (Localization.AtPrime P) ≃ₐ[ResidueField O] drinfeldFunctionField q (ResidueField O)),
         ∀ r : ↥R, eW (residue (Localization.AtPrime P) (algebraMap (↥R) _ r)) =
           algebraMap (CoordRing q (ResidueField O)) (drinfeldFunctionField q (ResidueField O)) (eR (Ideal.Quotient.mk P r))) := by
  intro S mkS L ι₀ x₀ x₁ R
  obtain ⟨hι₀, hx₀, hx₁, P, hPeq, hN, hP, algR, halgR, eR, c, hcen, hc0, hcpow, heR₀, heR₁⟩ :=
    DrinfeldCurve.LocalChart.exists_isPrime_algEquiv_coordRing_blowupChart_quotient_of_mem_maximalIdeal
      q O π hπ ϖ hϖ hϖ0 pr hnzd
  refine ⟨hι₀, hx₀, hx₁, P, hPeq, hN, hP, algR, halgR, eR, c, hcen, hc0, hcpow, heR₀, heR₁, ?_⟩
  haveI := hP
  haveI : IsNoetherianRing ↥R := hN

  have hunitϖ : IsUnit (ι₀ ϖ) := IsLocalization.Away.algebraMap_isUnit (S := L) (mkS (C ϖ))
  have hunitπ : IsUnit (ι₀ π) := by
    have hmem : ϖ ∈ Ideal.span {π} := hπ ▸ hϖ
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
    have : ι₀ ϖ = ι₀ a * ι₀ π := by rw [← map_mul, ha]
    exact isUnit_of_mul_isUnit_right (this ▸ hunitϖ)
  have hτ : (⟨ι₀ π, hι₀ π⟩ : ↥R) ∈ nonZeroDivisors ↥R := by
    refine mem_nonZeroDivisors_iff_right.mpr fun z hz => ?_
    have hzL : (z : L) * ι₀ π = 0 := by
      have := congrArg (fun w : ↥R => (w : L)) hz
      simpa using this
    have hz0 : (z : L) = 0 := (hunitπ.mul_left_eq_zero).mp hzL
    exact Subtype.ext hz0
  have hkey₁ := B34Assembly.dvr_of_span_singleton_nonZeroDivisor (⟨ι₀ π, hι₀ π⟩ : ↥R) P hPeq hτ
  obtain ⟨hdom, hdvr, hmax⟩ := hkey₁
  have hkey₂ := B34Assembly.residueField_atPrime (k := ResidueField O) P eR
  obtain ⟨algW, halgW, hmk, eW, heW⟩ := hkey₂
  exact ⟨hdom, hdvr, hmax, algW,
    fun a => (halgW (residue O a)).trans ((congrArg _ (halgR a)).trans (hmk ⟨ι₀ a, hι₀ a⟩)), eW, heW⟩

end
end S_DrinfeldCurve_LocalChart_exists_algEquiv_coordRing_and_isDiscreteValuationRing_blowupChart_of_mem_maximalIdeal
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_exists_algEquiv_coordRing_and_isDiscreteValuationRing_blowupChart_of_mem_maximalIdeal (solution)
