-- Prove2me | solution 1 for Formalism.NG.ker_map_uncurry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:34:05.05743+00:00
-- url     : https://prove2.me/submissions/c9cf3741-628d-461b-a40d-49041e7a10c4

import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Theorems.Thm_Formalism_NG_uncurry_relMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module IsDiscreteValuationRing Matrix
noncomputable section
open Formalism Formalism.NG
variable {R : Type*} [Ring R] {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {g d : Type} [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
  (ρ : R →+* Matrix d d O)
variable [SMulCommClass R O (LatQ O d ρ)]
namespace Formalism.NG
theorem _root_.solution (Θ : Matrix g g R) :
    (LinearMap.ker (relMap O (LatQ O d ρ) Θ)).map (uncurryEquiv (g := g) ρ).toLinearMap =
      LinearMap.ker (matQ O (bigMat ρ Θ)) := by
  ext w
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker,
    ← (uncurryEquiv (g := g) ρ).map_eq_zero_iff, uncurry_relMap, LinearEquiv.apply_symm_apply]
end Formalism.NG
