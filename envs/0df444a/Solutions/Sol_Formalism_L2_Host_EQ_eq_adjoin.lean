-- Prove2me | solution 1 for Formalism.L2.Host.EQ_eq_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:41:27.223587+00:00
-- url     : https://prove2.me/submissions/91e095c5-46bf-43cd-97ad-9970c27b4165

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_Lemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.L2.Host
theorem _root_.solution (e q d : ℕ) : EQ e q d =
    adjoin ℚ ((sqrts (-(q : ℤ)) ∪ sqrts (-(d : ℤ))) ∪ (fun z => z + z⁻¹) '' mus (2 ^ (e + 2))) := by
  show sqQ (-(q : ℤ)) ⊔ sqQ (-(d : ℤ)) ⊔ cycQplus (2 ^ (e + 2)) = _
  rw [sqQ, sqQ, cycQplus, ← IntermediateField.gc.l_sup, ← IntermediateField.gc.l_sup]
  rfl
end Formalism.L2.Host
