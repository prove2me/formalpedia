-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.localizerVanishes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:00:10.408799+00:00
-- url     : https://prove2.me/submissions/0d27b45c-a411-4a75-9609-0cf0b4b498ee

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ExistsNonzeroExchangedMinorHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_DetMulEqSumAdjugate
import Theorems.Thm_Formalism_CountingSumsFrames_Top_locTelescope
import Theorems.Thm_Formalism_CountingSumsFrames_Top_graphMinor
import Theorems.Thm_Formalism_CountingSumsFrames_piMinor_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Top
namespace Formalism.CountingSumsFrames.Top
theorem _root_.solution : Formalism.CountingSumsFrames.LocalizerVanishes := by
  intro p _ F _ _ _ n' r k J h hcard z hz hzJ pos hpos H hH A _ _ t
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  have hp1 : ∀ m, 1 ≤ p ^ m := fun m => Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hJ : 0 < J := by
    by_contra hJ0
    have hJ' : J = 0 := by omega
    subst hJ'
    have hn : n' = 0 := by omega
    rw [hn, pow_zero] at hcard
    have h1 := Fintype.one_lt_card (α := F)
    omega
  have hsum : ∑ j ∈ Finset.range J, p ^ z j * (p ^ (z (j + 1) - z j) - 1) = p ^ z 0 * (p ^ n' - 1) := by
    have h1 := (locTelescope p J n' z hz hzJ).1
    have h2 : ((∑ j ∈ Finset.range J, p ^ z j * (p ^ (z (j + 1) - z j) - 1) : ℕ) : ℤ) =
        ((p ^ z 0 * (p ^ n' - 1) : ℕ) : ℤ) := by
      rw [Nat.cast_sum, Finset.sum_congr rfl fun j _ => by
        rw [Nat.cast_mul, Nat.cast_sub (hp1 _), Nat.cast_pow, Nat.cast_pow, Nat.cast_one]]
      rw [Nat.cast_mul, Nat.cast_sub (hp1 _), Nat.cast_pow, Nat.cast_pow, Nat.cast_one]
      exact h1
    exact_mod_cast h2
  have hexp : ∀ x : F, x ≠ 0 →
      ∏ j ∈ Finset.range J, (x ^ p ^ z j) ^ (p ^ (z (j + 1) - z j) - 1) = 1 := by
    intro x hx
    simp only [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum, hsum, pow_mul, ← hcard]
    exact FiniteField.pow_card_sub_one_eq_one _ (pow_ne_zero _ hx)
  have hfac : ∀ cols : Fin r → Fin k,
      ∏ j ∈ Finset.range J, piMinor p r k (H.map (algebraMap F A)) (pos j) (t j) (z j) cols ^
        (p ^ (z (j + 1) - z j) - 1) =
      (∏ j ∈ Finset.range J, (Matrix.of fun l m => t j l m ^ p ^ (z j - pos j l)).det ^
        (p ^ (z (j + 1) - z j) - 1)) *
      algebraMap F A (∏ j ∈ Finset.range J, ((H.submatrix id cols).det ^ p ^ z j) ^
        (p ^ (z (j + 1) - z j) - 1)) := by
    intro cols
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [piMinor_map H (pos j) (t j) (z j) cols (hpos j (Finset.mem_range.mp hj)), mul_pow]
    simp only [map_pow]
  unfold localizer
  rw [piMinor_map H (pos 0) (t 0) (z 0) _ (hpos 0 hJ)]
  by_cases h0 : (H.submatrix id (Fin.castLE h)).det = 0
  · rw [h0, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), map_zero, mul_zero, zero_mul]
  · obtain ⟨i, c, hc, hI⟩ := graphMinor F r k h H h0 hH
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ ((i, ⟨c, hc⟩) : IIdx r k))
    rw [hfac, hfac, ← mul_sub, ← map_sub, hexp _ h0, hexp _ hI, sub_self, map_zero, mul_zero]
end Formalism.CountingSumsFrames.Top
