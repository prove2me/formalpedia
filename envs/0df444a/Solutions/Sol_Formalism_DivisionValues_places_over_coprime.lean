-- Prove2me | solution 1 for Formalism.DivisionValues.places_over_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:01.122146+00:00
-- url     : https://prove2.me/submissions/9a69b796-f577-4d38-a814-50f9689efafe

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_plOver_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open PlaceSumConjugation
namespace Formalism.DivisionValues
theorem _root_.solution : PlOverCoprime := by
  unfold PlOverCoprime
  intro K _ _ g g' hcop w ⟨h1, h2⟩
  have hpos : ∀ n : ℕ, PlOver n w → 0 < n := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      unfold PlOver vw at hn
      first | simp [FractionalIdeal.count_zero] at hn | (unfold FractionalIdeal.count at hn; simp at hn)
    · exact h0
  have m1 := plOver_mem (hpos g h1) w h1
  have m2 := plOver_mem (hpos g' h2) w h2
  have hab : (Nat.gcdA g g') * (g : ℤ) + (Nat.gcdB g g') * (g' : ℤ) = 1 := by
    have := Nat.gcd_eq_gcd_ab g g'
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    push_cast at this
    linarith
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have e : (1 : 𝓞 K) = ((Nat.gcdA g g' : ℤ) : 𝓞 K) * (g : 𝓞 K) + ((Nat.gcdB g g' : ℤ) : 𝓞 K) * (g' : 𝓞 K) := by
    exact_mod_cast hab.symm
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ m1) (Ideal.mul_mem_left _ _ m2)
end Formalism.DivisionValues
