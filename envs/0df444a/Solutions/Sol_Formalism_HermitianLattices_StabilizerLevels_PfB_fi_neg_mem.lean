-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.fi_neg_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:16:25.145738+00:00
-- url     : https://prove2.me/submissions/01b84380-0027-41bc-8deb-23c92c2d814f

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IntermediateField Ideal IsDedekindDomain nonZeroDivisors
open scoped Pointwise
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution {I : FractionalIdeal (𝓞 E)⁰ E} {x : E} (h : x ∈ I) : -x ∈ I := by
  rw [← FractionalIdeal.mem_coe] at h ⊢
  exact neg_mem h
end Formalism.HermitianLattices.StabilizerLevels.PfB
