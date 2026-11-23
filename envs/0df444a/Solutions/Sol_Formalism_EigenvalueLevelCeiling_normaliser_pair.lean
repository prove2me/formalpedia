-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.normaliser_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:26.663782+00:00
-- url     : https://prove2.me/submissions/a41c17fe-ae78-4845-b626-b539b91852b0

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric
import Theorems.Thm_Formalism_DivisionValues_valuation_basic_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.EigenvalueLevelCeiling
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : NormaliserPair := by
  unfold NormaliserPair
  intro K _ _ _ w π hπ Dp Dm
  have hV := Formalism.DivisionValues.valuation_basic_properties K w
  have hsπ : star π ≠ 0 := star_ne_zero.mpr hπ
  have hpow : ∀ x : K, x ≠ 0 → ∀ n : ℕ, Formalism.DivisionValues.vw w (x ^ n) = (n : ℤ) * Formalism.DivisionValues.vw w x := by
    intro x hx n
    induction n with
    | zero => simp [hV.2.2.2.2.1]
    | succ n ih =>
      rw [pow_succ, hV.1 _ _ (pow_ne_zero _ hx) hx, ih]
      push_cast
      ring
  rw [← hV.2.1, star_mul, star_pow, star_pow, star_star,
    hV.1 (star π ^ Dp) (π ^ Dm) (pow_ne_zero _ hsπ) (pow_ne_zero _ hπ),
    hV.1 (star π ^ Dm) (π ^ Dp) (pow_ne_zero _ hsπ) (pow_ne_zero _ hπ),
    hV.1 π (star π) hπ hsπ, hpow _ hsπ Dp, hpow _ hπ Dm, hpow _ hsπ Dm, hpow _ hπ Dp]
  ring
end Formalism.EigenvalueLevelCeiling
