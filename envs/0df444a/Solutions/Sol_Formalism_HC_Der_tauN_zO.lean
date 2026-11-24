-- Prove2me | solution 1 for Formalism.HC.Der.tauN_zO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:31:29.92305+00:00
-- url     : https://prove2.me/submissions/c7e9f1b8-71b1-4249-8a3e-af8b573f0daa

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_z_spec
import Theorems.Thm_Formalism_HC_Der_tauN_root


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable (N : ℕ) [NeZero N]
namespace Formalism.HC.Der
theorem _root_.solution (u : (ZMod N)ˣ) : tauN N u • zO N = zO N ^ (u : ZMod N).val := by
  apply RingOfIntegers.ext
  show (tauN N u) ((zO N : 𝓞 (Cond.Cyc N)) : Cond.Cyc N) =
    (((zO N) ^ (u : ZMod N).val : 𝓞 (Cond.Cyc N)) : Cond.Cyc N)
  push_cast
  exact tauN_root N u _ (Cond.z_spec N).pow_eq_one
end Formalism.HC.Der
