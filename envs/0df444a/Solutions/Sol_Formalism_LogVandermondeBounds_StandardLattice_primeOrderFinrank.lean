-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.primeOrderFinrank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:27.59903+00:00
-- url     : https://prove2.me/submissions/d0d55af9-db56-465e-9c32-d71d1ac34d10

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_PrimePowerSubgroupTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Polynomial
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution : PrimeOrderFinrank := by
  intro K _ _ n g A hg hA hA1
  haveI := Fact.mk hg
  let f : (Fin n → K) →ₗ[ℚ] (Fin n → K) := (Matrix.toLin' A).restrictScalars ℚ
  have hpow : ∀ v : Fin n → K, (f ^ g) v = v := by
    intro v
    rw [Module.End.pow_apply]
    show (⇑(Matrix.toLin' A))^[g] v = v
    rw [← Module.End.pow_apply, ← Matrix.toLin'_pow, hA, Matrix.toLin'_one, LinearMap.id_apply]
  have hfg : f ^ g = 1 := LinearMap.ext hpow
  have hint : IsIntegral ℚ f := IsIntegral.of_finite ℚ f
  have hm0 : minpoly ℚ f ≠ 0 := minpoly.ne_zero hint
  have hdvd : minpoly ℚ f ∣ Polynomial.cyclotomic g ℚ * (Polynomial.X - 1) := by
    rw [Polynomial.cyclotomic_prime_mul_X_sub_one]
    apply minpoly.dvd
    simp [hfg]
  have hirr := Polynomial.cyclotomic.irreducible_rat hg.pos
  have hdeg : (Polynomial.cyclotomic g ℚ).natDegree = g - 1 := by
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hg]
  have hle : (minpoly ℚ f).natDegree ≤ Module.finrank ℚ K * n := by
    have h1 := Polynomial.natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly f) (LinearMap.charpoly_monic f).ne_zero
    rw [LinearMap.charpoly_natDegree] at h1
    have h2 : Module.finrank ℚ (Fin n → K) = Module.finrank ℚ K * n := by
      rw [Module.finrank_pi_fintype]
      simp [mul_comm]
    omega
  by_cases hc : Polynomial.cyclotomic g ℚ ∣ minpoly ℚ f
  · have := Polynomial.natDegree_le_of_dvd hc hm0
    omega
  · exfalso
    apply hA1
    have hcop : IsCoprime (minpoly ℚ f) (Polynomial.cyclotomic g ℚ) :=
      ((hirr.coprime_iff_not_dvd).2 hc).symm
    have h1 : minpoly ℚ f ∣ Polynomial.X - 1 := by
      first
        | exact hcop.dvd_of_dvd_mul_left hdvd
        | exact hcop.dvd_of_dvd_mul_right hdvd
        | exact hcop.dvd_of_dvd_mul_left (by rwa [mul_comm] at hdvd)
        | exact hcop.dvd_of_dvd_mul_right (by rwa [mul_comm] at hdvd)
    have h2 : Polynomial.aeval f (Polynomial.X - 1 : Polynomial ℚ) = 0 := by
      obtain ⟨q, hq⟩ := h1
      rw [hq, map_mul, minpoly.aeval, zero_mul]
    have hf1 : f = 1 := by
      simpa [sub_eq_zero] using h2
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_one]
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun hf1 v
    simpa [f] using this
end Formalism.LogVandermondeBounds.StandardLattice
