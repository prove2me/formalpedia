-- Prove2me | solution 1 for Formalism.DivisionValues.shift_sum_above_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:41.560945+00:00
-- url     : https://prove2.me/submissions/69a7fb9f-fdba-49ea-90a3-746ae0e3cd09

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TwistedLatticeNaturality
import Theorems.Thm_Formalism_DivisionValues_shift_lw_pos
import Theorems.Thm_Formalism_DivisionValues_shift_above_iff
import Theorems.Thm_Formalism_DivisionValues_shift_sum_e_finset
import Theorems.Thm_Formalism_DivisionValues_shift_sum_above

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable [IsTotallyComplex K]
namespace Formalism.DivisionValues
theorem _root_.solution (p : ℕ) (hp : p.Prime) :
    ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : Above p w), lw w ≤ Real.log p := by
  rw [shift_sum_above (K := K) p hp, ← shift_sum_e_finset (K := K) p hp]
  apply Finset.sum_le_sum
  intro w hw
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, shift_above_iff p hp] at hw
  have h0 : (1 : ℤ) ≤ vw w (p : K) := by omega
  have h1 : (1 : ℝ) ≤ (vw w (p : K) : ℝ) := by exact_mod_cast h0
  have h2 := shift_lw_pos w
  nlinarith
end Formalism.DivisionValues
