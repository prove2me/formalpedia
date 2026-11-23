-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ramw_conjPl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:09.068806+00:00
-- url     : https://prove2.me/submissions/18afd774-6642-4685-9432-3eb39072b1f3

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_plc_conjPl
import Theorems.Thm_Formalism_DivisionValues_valuation_basic_properties


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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) : ramw (conjPl w) = ramw w := by
  unfold ramw
  rw [plc_conjPl, ← (valuation_basic_properties K w).2.1 ((plc w : ℕ) : K), star_natCast]
end Formalism.EigenvalueLevelCeiling
