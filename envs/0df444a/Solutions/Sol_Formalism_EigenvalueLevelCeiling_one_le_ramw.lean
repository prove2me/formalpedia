-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.one_le_ramw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:53.446673+00:00
-- url     : https://prove2.me/submissions/9c0285dc-9b8c-4ad7-87e1-05cccdee7116

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_plc_prime
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_plc_mem
import Theorems.Thm_P2M_Formalism_EigenvalueLevelCeiling_intValuation_eq_exp__a0f6a2bc12ef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) : 1 ≤ ramw w := by
  have hm := plc_mem w
  have hne : ((plc w : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast (plc_prime w).ne_zero
  have h1 := (w.intValuation_lt_one_iff_mem _).mpr hm
  rw [intValuation_eq_exp' w _ hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  unfold ramw
  push_cast at h1
  omega
end Formalism.EigenvalueLevelCeiling
