-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemTwo.embDomain_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:47.3006+00:00
-- url     : https://prove2.me/submissions/b839aa80-4d77-4376-8ee0-a56624f5dc12

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LemTwo
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.LemTwo
theorem _root_.solution (e : Fin 2 →₀ ℕ) : Finsupp.embDomain Fin.castSuccEmb e (2 : Fin 3) = 0 := by
  rw [Finsupp.embDomain_notin_range]
  rintro ⟨i, hi⟩
  have h1 := congrArg Fin.val hi
  have h2 := i.isLt
  simp at h1
  omega
end Formalism.InvariantFactorPaths.G7.LemTwo
