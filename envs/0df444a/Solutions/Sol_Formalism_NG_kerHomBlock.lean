-- Prove2me | solution 1 for Formalism.NG.kerHomBlock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:18:27.693534+00:00
-- url     : https://prove2.me/submissions/4cd676c8-776a-47cf-b73e-94b645a66e56

import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Theorems.Thm_Formalism_NG_ker_map_uncurry
import Theorems.Thm_Formalism_NG_homCoker


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
namespace Formalism.NG
theorem _root_.solution : StatKerHomBlock := by
  intro R O _ _ _ _ g d _ _ _ _ ρ _ Θ
  obtain ⟨e⟩ := homCoker R O (LatQ O d ρ) g g Θ
  rw [e.length_eq, ← ker_map_uncurry ρ Θ]
  exact (Submodule.equivMapOfInjective _ (uncurryEquiv (g := g) ρ).injective _).length_eq.symm
end Formalism.NG
