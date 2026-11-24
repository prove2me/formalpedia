-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.minpoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:46.968954+00:00
-- url     : https://prove2.me/submissions/8ae87237-f8a7-4a36-b8c1-1fe3898227c8

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_star_algebraMap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_coe_algebraMap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_exists_int_of_star_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
theorem _root_.solution (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (θ t : 𝓞 K)
    (ht : algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K θ)) (hne : θ ≠ t) :
    aeval θ (derivative (minpoly (𝓞 F) θ)) = θ - t := by
  have ht' : star (algebraMap (𝓞 K) K t) = algebraMap (𝓞 K) K θ := by rw [ht, star_star]
  obtain ⟨s, hs⟩ := exists_int_of_star_eq hF (θ + t) (by rw [map_add, star_add, ht', ← ht, add_comm])
  obtain ⟨p, hp⟩ := exists_int_of_star_eq hF (θ * t) (by rw [map_mul, star_mul', ht', ← ht, mul_comm])
  obtain ⟨q, hq⟩ : ∃ q : Polynomial (𝓞 F), q = X ^ 2 - C s * X + C p := ⟨_, rfl⟩
  have hqdeg : q.natDegree = 2 := by rw [hq]; compute_degree!
  have hqm : q.Monic := by rw [hq]; monicity!
  have hroot : aeval θ q = 0 := by
    rw [hq]
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, hs, hp]
    ring
  have hint : IsIntegral (𝓞 F) θ := by
    first
      | exact Algebra.IsIntegral.isIntegral θ
      | exact IsIntegral.tower_top (A := 𝓞 F) (RingOfIntegers.isIntegral θ)
      | exact (Algebra.IsIntegral.isIntegral (R := ℤ) θ).tower_top
  have hdvd : minpoly (𝓞 F) θ ∣ q := minpoly.isIntegrallyClosed_dvd hint hroot
  have hdeg2 : 2 ≤ (minpoly (𝓞 F) θ).natDegree := by
    by_contra hlt
    push_neg at hlt
    have h1 : (minpoly (𝓞 F) θ).natDegree = 1 := by
      have := minpoly.natDegree_pos hint
      omega
    have hd1 : (minpoly (𝓞 F) θ).degree = 1 := by
      rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hint), h1]
      rfl
    have hr : θ ∈ (algebraMap (𝓞 F) (𝓞 K)).range := by
      first
        | exact minpoly.mem_range_of_degree_eq_one (𝓞 F) θ hd1
        | exact minpoly.mem_range_of_degree_eq_one hd1
        | exact minpoly.mem_range_of_degree_eq_one (𝓞 F) hd1
    obtain ⟨z, hz⟩ := hr
    apply hne
    apply RingOfIntegers.ext
    have hfx : star (algebraMap (𝓞 K) K θ) = algebraMap (𝓞 K) K θ := by
      rw [← hz, coe_algebraMap]
      exact star_algebraMap hF _
    exact (ht.trans hfx).symm
  have heq : q = minpoly (𝓞 F) θ :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hqm hdvd (by rw [hqdeg]; exact hdeg2)
  rw [← heq, hq]
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_X_pow, derivative_C,
    derivative_X, zero_mul, mul_one, zero_add, add_zero, map_add, map_sub, map_mul, map_pow,
    aeval_X, aeval_C, map_natCast, hs]
  first
    | ring
    | (norm_num; ring)
    | norm_num
    | (push_cast; ring)
end Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
