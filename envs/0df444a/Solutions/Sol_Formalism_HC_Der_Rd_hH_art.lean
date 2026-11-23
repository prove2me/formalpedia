-- Prove2me | solution 1 for Formalism.HC.Der.Rd.hH_art
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:46.057784+00:00
-- url     : https://prove2.me/submissions/abe36f9e-e167-4e34-8842-925a6961271a

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia

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
open Formalism.FrobeniusOrbits
open Formalism.HC.Der.Rd
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der.Rd
theorem _root_.solution (u : (ZMod H.condN)ˣ) : φ.hH (H.art u).2 = hcl φ.e (ZMod.unitsMap (two_dvd H) u) := by
  apply H.art_h
  show (ZMod.castHom (two_dvd H) (ZMod (2 ^ (φ.e + 2)))) (u : ZMod H.condN) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
end Formalism.HC.Der.Rd
