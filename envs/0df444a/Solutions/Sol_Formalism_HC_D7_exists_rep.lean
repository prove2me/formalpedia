-- Prove2me | solution 1 for Formalism.HC.D7.exists_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:43:29.708676+00:00
-- url     : https://prove2.me/submissions/a2d65cac-9a45-4a7c-a8e9-527cb640e108

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.D7
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)
include hH
omit hH
namespace Formalism.HC.D7
theorem _root_.solution (t : HGrp e) : ∃ (x : ℕ) (v : (ZMod (2 ^ (e + 2)))ˣ),
    (v : ZMod (2 ^ (e + 2))) = (x : ZMod (2 ^ (e + 2))) ∧ t = hcl e v := by
  haveI : NeZero (2 ^ (e + 2)) := ⟨by positivity⟩
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective t
  exact ⟨(v : ZMod (2 ^ (e + 2))).val, v, (ZMod.natCast_zmod_val _).symm, rfl⟩
end Formalism.HC.D7
