-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.covA_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:40:07.554671+00:00
-- url     : https://prove2.me/submissions/7351693f-e48d-4e4b-a917-a50a2104b76e

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_LatITopBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Polynomial Matrix Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime] (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2) :
    ∃ ω : 𝓞 K, (ω : K) = (1 + x) / 2 ∧
      ∀ y : 𝓞 K, ∃ m n : ℤ, y = (m : 𝓞 K) + (n : 𝓞 K) * ω := by
  have hd : d.Prime := Fact.out
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd.pos
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d = 4 * k + 3 := ⟨d / 4, by omega⟩
  have hxr : ∀ q : ℚ, (q : K) ≠ x := by
    intro q hq
    have h2 : ((q ^ 2 : ℚ) : K) = ((-(d : ℚ) : ℚ) : K) := by
      push_cast
      rw [hq, hx]
    have h3 : q ^ 2 = -(d : ℚ) := Rat.cast_injective h2
    nlinarith [sq_nonneg q]
  have hωint : IsIntegral ℤ ((1 + x) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((k : ℤ) + 1), by monicity!, ?_⟩
    have hx' : x ^ 2 = -(4 * (k : K) + 3) := by
      rw [hx, hk]
      push_cast
      ring
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    push_cast
    linear_combination (1 / 4 : K) * hx'
  refine ⟨⟨(1 + x) / 2, hωint⟩, rfl, ?_⟩
  intro y
  have hli : LinearIndependent ℚ ![(1 : K), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hxr (-(s / t))
      have htK : (t : K) ≠ 0 := by exact_mod_cast ht
      rw [Rat.smul_def, Rat.smul_def, mul_one] at hst
      push_cast
      rw [neg_eq_iff_eq_neg, div_eq_iff htK]
      linear_combination hst
  obtain ⟨a, b, hab⟩ : ∃ a b : ℚ, (y : K) = (a : K) + (b : K) * x := by
    set bs := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hK]) with hbs
    refine ⟨bs.repr y 0, bs.repr y 1, ?_⟩
    conv_lhs => rw [← bs.sum_repr (y : K)]
    simp [Fin.sum_univ_two, hbs, coe_basisOfLinearIndependentOfCardEqFinrank, Rat.smul_def]
  have hyint : IsIntegral ℤ (y : K) := RingOfIntegers.isIntegral_coe y
  obtain ⟨A, hA, N, hN⟩ : ∃ A : ℤ, (A : ℚ) = 2 * a ∧ ∃ N : ℤ, (N : ℚ) = a ^ 2 + d * b ^ 2 := by
    by_cases hb : b = 0
    · subst hb
      have h1 : (y : K) = algebraMap ℚ K a := by
        rw [hab]
        simp
      have h2 : IsIntegral ℤ a := by
        rw [← isIntegral_algebraMap_iff (algebraMap ℚ K).injective, ← h1]
        exact hyint
      obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
      refine ⟨2 * z, by simp [← hz], z ^ 2, by simp [← hz]⟩
    · set q : Polynomial ℚ := Polynomial.X ^ 2 - Polynomial.C (2 * a) * Polynomial.X +
        Polynomial.C (a ^ 2 + d * b ^ 2) with hq
      have hqm : q.Monic := by
        rw [hq]
        monicity!
      have hqd : q.natDegree = 2 := by
        rw [hq]
        compute_degree!
      have hqy : Polynomial.aeval (y : K) q = 0 := by
        rw [hq]
        simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
          eq_ratCast]
        rw [hab]
        push_cast
        linear_combination (b : K) ^ 2 * hx
      have hnr : (y : K) ∉ (algebraMap ℚ K).range := by
        rintro ⟨r, hr⟩
        apply hxr ((r - a) / b)
        have hbK : (b : K) ≠ 0 := by exact_mod_cast hb
        rw [eq_ratCast] at hr
        push_cast
        rw [div_eq_iff hbK, hr, hab]
        ring
      have hmin : q = minpoly ℚ (y : K) := by
        refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic
          (Algebra.IsIntegral.isIntegral _)) hqm (minpoly.dvd ℚ _ hqy) ?_
        have h1 : (minpoly ℚ (y : K)).natDegree ≠ 1 := fun h =>
          hnr (minpoly.natDegree_eq_one_iff.mp h)
        have h0 : 0 < (minpoly ℚ (y : K)).natDegree :=
          minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral _)
        omega
      have hZ := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hyint
      have c1 := congrArg (fun p => Polynomial.coeff p 1) (hmin.trans hZ)
      have c0 := congrArg (fun p => Polynomial.coeff p 0) (hmin.trans hZ)
      simp only [hq, Polynomial.coeff_map, Polynomial.coeff_add, Polynomial.coeff_sub,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
        eq_intCast] at c1 c0
      refine ⟨-(minpoly ℤ (y : K)).coeff 1, ?_, (minpoly ℤ (y : K)).coeff 0, ?_⟩
      · push_cast
        rw [← c1]
        norm_num
      · rw [← c0]
        norm_num
  have sqint : ∀ r : ℚ, ∀ M : ℤ, (d : ℚ) * r ^ 2 = M → ∃ B : ℤ, (B : ℚ) = r := by
    intro r M hr
    have hden : r.den = 1 := by
      have e : (d : ℚ) * (r.num : ℚ) ^ 2 = M * (r.den : ℚ) ^ 2 := by
        have h := hr
        rw [← Rat.num_div_den r, div_pow, mul_div_assoc', div_eq_iff (by positivity)] at h
        exact h
      have e' : (d : ℤ) * r.num ^ 2 = M * (r.den : ℤ) ^ 2 := by exact_mod_cast e
      have hcop : IsCoprime ((r.den : ℤ) ^ 2) (r.num ^ 2) := by
        have h0 : IsCoprime (r.den : ℤ) r.num := by
          rw [Int.isCoprime_iff_gcd_eq_one]
          exact r.reduced.symm
        exact h0.pow
      have hdvd : ((r.den : ℤ) ^ 2) ∣ (d : ℤ) := by
        have h1 : ((r.den : ℤ) ^ 2) ∣ (d : ℤ) * r.num ^ 2 := ⟨M, by rw [e']; ring⟩
        exact hcop.dvd_of_dvd_mul_right h1
      have h2 : r.den ^ 2 ∣ d := by exact_mod_cast hdvd
      have h3 : r.den ∣ d := (dvd_pow_self _ two_ne_zero).trans h2
      rcases (Nat.dvd_prime hd).mp h3 with h | h
      · exact h
      · exfalso
        rw [h] at h2
        have h4 := Nat.le_of_dvd hd.pos h2
        nlinarith [hd.two_le]
    exact ⟨r.num, Rat.coe_int_num_of_den_eq_one hden⟩
  obtain ⟨B, hB⟩ := sqint (2 * b) (4 * N - A ^ 2) (by push_cast; rw [hN, hA]; ring)
  have e4 : 4 * N = A ^ 2 + (4 * (k : ℤ) + 3) * B ^ 2 := by
    have : (4 * N : ℚ) = A ^ 2 + d * B ^ 2 := by
      rw [hN, hA, hB]
      ring
    have h' : (4 * N : ℤ) = A ^ 2 + d * B ^ 2 := by exact_mod_cast this
    rw [h', hk]
    push_cast
    ring
  obtain ⟨m, hm⟩ : ∃ m : ℤ, A - B = 2 * m := by
    rcases Int.even_or_odd A with ⟨u, hu⟩ | ⟨u, hu⟩ <;>
      rcases Int.even_or_odd B with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact ⟨u - v, by rw [hu, hv]; ring⟩
    · exfalso
      rw [hu, hv] at e4
      have h5 : 4 * (N - u ^ 2 - (4 * k + 3) * (v ^ 2 + v) - k) = 3 := by linear_combination e4
      generalize N - u ^ 2 - (4 * k + 3) * (v ^ 2 + v) - k = X at h5
      omega
    · exfalso
      rw [hu, hv] at e4
      have h5 : 4 * (N - u ^ 2 - u - (4 * k + 3) * v ^ 2) = 1 := by linear_combination e4
      generalize N - u ^ 2 - u - (4 * k + 3) * v ^ 2 = X at h5
      omega
    · exact ⟨u - v, by rw [hu, hv]; ring⟩
  refine ⟨m, B, ?_⟩
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  simp only [map_add, map_mul, map_intCast]
  change (y : K) = (m : K) + (B : K) * ((1 + x) / 2)
  rw [hab]
  have ha2 : (2 : K) * a = A := by exact_mod_cast hA.symm
  have hb2 : (2 : K) * b = B := by exact_mod_cast hB.symm
  have hm2 : (A : K) - B = 2 * m := by exact_mod_cast hm
  linear_combination (1 / 2 : K) * ha2 + (x / 2) * hb2 + (1 / 2 : K) * hm2
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
