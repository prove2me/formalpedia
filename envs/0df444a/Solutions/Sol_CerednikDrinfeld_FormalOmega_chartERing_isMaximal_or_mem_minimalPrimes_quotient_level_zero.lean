-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.chartERing.isMaximal_or_mem_minimalPrimes_quotient_level_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/988e5e24-bdd4-569e-b548-7caaffc97129

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_isMaximal_or_mem_minimalPrimes_quotient_level_zero

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace DimOne29

open MvPolynomial

theorem ringKrullDim_le_of_isLocalization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] : ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    (Monotone.strictMono_of_injective (fun _ _ h => Ideal.comap_mono h)
      (PrimeSpectrum.localization_comap_injective S M))

section

variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ)

noncomputable abbrev πQ : edgeQuot 𝒪 π := algebraMap 𝒪 (edgeQuot 𝒪 π) π

abbrev Q₁ : Type := edgeQuot 𝒪 π ⧸ Ideal.span {πQ 𝒪 π}

noncomputable def ψ : MvPolynomial (Fin 2) (𝒪 ⧸ Ideal.span ({π} : Set 𝒪)) →+* Q₁ 𝒪 π :=
  MvPolynomial.eval₂Hom
    (Ideal.quotientMap (Ideal.span {πQ 𝒪 π}) (algebraMap 𝒪 (edgeQuot 𝒪 π))
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.subset_span rfl))))
    (fun i => Ideal.Quotient.mk _ (edgeQuot.mk 𝒪 π (MvPolynomial.X i)))

theorem ψ_comp_map :
    (ψ 𝒪 π).comp (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span ({π} : Set 𝒪)))) =
      (Ideal.Quotient.mk (Ideal.span {πQ 𝒪 π})).comp (edgeQuot.mk 𝒪 π).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    show ψ 𝒪 π (MvPolynomial.map _ (MvPolynomial.C a)) =
      Ideal.Quotient.mk (Ideal.span {πQ 𝒪 π}) (edgeQuot.mk 𝒪 π (MvPolynomial.C a))
    rw [MvPolynomial.map_C, ψ, MvPolynomial.eval₂Hom_C, Ideal.quotientMap_mk, ← MvPolynomial.algebraMap_eq,
      AlgHom.commutes]
  · intro i
    show ψ 𝒪 π (MvPolynomial.map _ (MvPolynomial.X i)) =
      Ideal.Quotient.mk (Ideal.span {πQ 𝒪 π}) (edgeQuot.mk 𝒪 π (MvPolynomial.X i))
    rw [MvPolynomial.map_X, ψ, MvPolynomial.eval₂Hom_X']

theorem ψ_surjective : Function.Surjective (ψ 𝒪 π) := by
  have h : Function.Surjective ((ψ 𝒪 π).comp (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span ({π} : Set 𝒪))))) := by
    rw [ψ_comp_map]
    exact Ideal.Quotient.mk_surjective.comp (Ideal.Quotient.mkₐ_surjective 𝒪 _)
  exact Function.Surjective.of_comp h

theorem ψ_X (i : Fin 2) :
    ψ 𝒪 π (MvPolynomial.X i) = Ideal.Quotient.mk (Ideal.span {πQ 𝒪 π}) (edgeQuot.mk 𝒪 π (MvPolynomial.X i)) := by
  rw [ψ, MvPolynomial.eval₂Hom_X']

theorem ψ_X_mul_X : ψ 𝒪 π (MvPolynomial.X 0 * MvPolynomial.X 1) = 0 := by
  have hrel : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) 𝒪) = edgeRel 𝒪 π + MvPolynomial.C π :=
    (sub_add_cancel _ _).symm
  have h1 : ψ 𝒪 π (MvPolynomial.X 0 * MvPolynomial.X 1) =
      Ideal.Quotient.mk (Ideal.span {πQ 𝒪 π}) (edgeQuot.mk 𝒪 π (MvPolynomial.X 0 * MvPolynomial.X 1)) := by
    rw [map_mul, ψ_X, ψ_X, map_mul, map_mul]
  rw [h1, hrel, map_add, edgeQuot.mk_edgeRel, zero_add, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

theorem ringKrullDim_Q₁_le (hπ : (Ideal.span ({π} : Set 𝒪)).IsMaximal) : ringKrullDim (Q₁ 𝒪 π) ≤ 1 := by
  letI : Field (𝒪 ⧸ Ideal.span ({π} : Set 𝒪)) := Ideal.Quotient.field _
  have hnzd : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) (𝒪 ⧸ Ideal.span ({π} : Set 𝒪))) ∈
      nonZeroDivisors _ :=
    mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _))
  have h := ringKrullDim_succ_le_of_surjective (ψ 𝒪 π) (ψ_surjective 𝒪 π) hnzd (ψ_X_mul_X 𝒪 π)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
  have h2 : (0 : WithBot ℕ∞) + (Nat.card (Fin 2) : ℕ) = 1 + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  rw [h2] at h
  exact ENat.WithBot.add_le_add_one_right_iff.mp h

end

end DimOne29

open DimOne29

theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ) (hπ : (Ideal.span ({π} : Set 𝒪)).IsMaximal)
    (p : Ideal ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}))) (hp : p.IsPrime) :
    p.IsMaximal ∨ p ∈ minimalPrimes ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) := by

  have hI : Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)} =
      (Ideal.span {πQ 𝒪 π}).map (algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) := by
    rw [zero_add, pow_one, Ideal.map_span, Set.image_singleton, πQ, ← IsScalarTower.algebraMap_apply]

  have hdim : ringKrullDim ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hI)]
    exact (ringKrullDim_le_of_isLocalization
      (Algebra.algebraMapSubmonoid (Q₁ 𝒪 π) (Submonoid.powers (edgeQuot.discr 𝒪 π r)))).trans
      (ringKrullDim_Q₁_le 𝒪 π hπ)
  haveI : Ring.KrullDimLE 1 ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) :=
    Ring.krullDimLE_iff.mpr hdim
  exact ((Ring.krullDimLE_one_iff.mp this) p hp).symm

end S_CerednikDrinfeld_FormalOmega_chartERing_isMaximal_or_mem_minimalPrimes_quotient_level_zero
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_isMaximal_or_mem_minimalPrimes_quotient_level_zero (solution)
