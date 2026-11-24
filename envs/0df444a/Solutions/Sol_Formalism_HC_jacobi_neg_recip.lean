-- Prove2me | solution 1 for Formalism.HC.jacobi_neg_recip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:15:34.392335+00:00
-- url     : https://prove2.me/submissions/bfebac89-8c6f-48af-9673-8217e6d912ee

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts

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
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
namespace Formalism.HC
theorem _root_.solution {r p : ℕ} (hr : r % 4 = 3) (hp : p % 2 = 1) :
    jacobiSym (-(r : ℤ)) p = jacobiSym (p : ℤ) r := by
  have hpo : Odd p := Nat.odd_iff.2 hp
  have hro : Odd r := Nat.odd_iff.2 (by omega)
  rw [jacobiSym.neg _ hpo]
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four' hro h]
  · rw [ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four hr h]
    ring
end Formalism.HC
