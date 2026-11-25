-- Prove2me | solution 1 for Formalism.HC.D7.artinMap_second_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:58:41.752877+00:00
-- url     : https://prove2.me/submissions/1bb2306d-7d2e-43f6-adcc-0086e1af9321

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Theorems.Thm_Formalism_HC_D7_artinMap_second_eq_jacobiSym

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open Formalism.HC.D7
variable (φ : Frame) (hinj : Function.Injective φ.h)
variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)
namespace Formalism.HC.D7
theorem _root_.solution (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) (hu : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD d]) :
    (art0 e hH u).1.2 = 1 := by
  apply Units.ext
  rw [artinMap_second_eq_jacobiSym, jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast Int.natCast_modEq_iff.mpr hu), jacobiSym.one_left]
  rfl
end Formalism.HC.D7
