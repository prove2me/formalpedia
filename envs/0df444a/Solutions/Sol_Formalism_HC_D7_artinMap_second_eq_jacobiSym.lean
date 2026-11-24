-- Prove2me | solution 1 for Formalism.HC.D7.artinMap_second_eq_jacobiSym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:13:33.190045+00:00
-- url     : https://prove2.me/submissions/14880743-7ada-433f-9d04-94fbd76e7d52

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym

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
theorem _root_.solution (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) :
    (((art0 e hH u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod (2 ^ (e + 2) * q * d)).val : ℕ) : ℤ) d :=
  haveI := neZeroN e hH
  sgnN_val hH.2.1 (d_dvd e q d) u
end Formalism.HC.D7
