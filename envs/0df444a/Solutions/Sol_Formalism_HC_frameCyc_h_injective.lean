-- Prove2me | solution 1 for Formalism.HC.frameCyc_h_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:53:51.954825+00:00
-- url     : https://prove2.me/submissions/dc2c98d2-4b22-4bba-b42e-19c31671a436

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable (e : ℕ) (a' : ZMod (2 ^ e))
namespace Formalism.HC
theorem _root_.solution : Function.Injective (frameCyc e a').h := by
  intro x y hxy
  have h1 : ∀ t, (frameCyc e a').h t = cycHom e (frameCycIso e a' t) := fun t => rfl
  rw [h1, h1] at hxy
  exact (frameCycIso e a').injective ((cycHom_bijective e).1 hxy)
end Formalism.HC
