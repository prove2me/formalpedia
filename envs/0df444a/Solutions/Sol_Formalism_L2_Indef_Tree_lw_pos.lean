-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.lw_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:52:23.90721+00:00
-- url     : https://prove2.me/submissions/7f8fe08e-46f3-4389-92a5-97d0fd83d6a6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsWeightedConditional
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditions
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ErrSum
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditionsOfExact
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive

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
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (K)
variable {K} (v0 : InfinitePlace K) (Tw0 : Finset (HeightOneSpectrum (𝓞 K)))
variable (h3 : ∀ w ∈ Tw0, plc w = 3)
include h3
omit h3
namespace Formalism.L2.Indef.Tree
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) : 0 < lw w := by
  unfold lw
  have h1 : Ideal.absNorm w.asIdeal ≠ 1 := fun h => w.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h2 : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by
    have h3 : 1 < Ideal.absNorm w.asIdeal := by omega
    exact_mod_cast h3
  apply div_pos (Real.log_pos h2)
  have h4 : 0 < finrank ℚ K := Module.finrank_pos
  exact_mod_cast h4
end Formalism.L2.Indef.Tree
