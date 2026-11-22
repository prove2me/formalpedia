-- Prove2me | solution 1 for Formalism.DivisionValues.PlaceSumConjugation.lw_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:58.283997+00:00
-- url     : https://prove2.me/submissions/69f1dfd9-6d5d-477e-b855-cf2658668d78

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds

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
open Formalism.DivisionValues.PlaceSumConjugation
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.DivisionValues.PlaceSumConjugation
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) : 0 < lw w := by
  unfold lw
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
  have h2 : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by
    exact_mod_cast (by omega : 1 < Ideal.absNorm w.asIdeal)
  apply div_pos (Real.log_pos h2)
  exact_mod_cast Module.finrank_pos
end Formalism.DivisionValues.PlaceSumConjugation
