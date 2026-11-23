-- Prove2me | solution 1 for Formalism.FG.FormalGroupCoefficients.inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:39.58587+00:00
-- url     : https://prove2.me/submissions/879a5bef-89b8-4d55-b414-0dbab69a9f17

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV
import Theorems.Thm_Formalism_FG_subst_injective_vector


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open Formalism Formalism.FG Formalism.FG.FormalGroupCoefficients
open MvPowerSeries Formalism.G Formalism.LT
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
namespace Formalism.FG.FormalGroupCoefficients
theorem _root_.solution {f : ι → MvPowerSeries ι R} (hf : IsIdMod2 f) {τ : Type v} [Finite τ]
    {a b : ι → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (h : ∀ j, subst a (f j) = subst b (f j)) : a = b :=
  Formalism.FG.subst_injective_vector.{u, v, v} R ι τ f a b hf ha hb h
end Formalism.FG.FormalGroupCoefficients
