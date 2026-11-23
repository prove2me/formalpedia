-- Prove2me | solution 1 for Formalism.HC.An.induces_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:05:59.130158+00:00
-- url     : https://prove2.me/submissions/23c15283-ee65-4ab6-9a34-eef8407352fd

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic

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
open Formalism.HC.An
namespace Formalism.HC.An
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Induces (PChar.of χ).χ (fun a => χ (a : ZMod N)) N := by
  refine ⟨DirichletCharacter.primitiveCharacter_isPrimitive χ, fun a ha => ?_⟩
  show χ.primitiveCharacter (a : ZMod χ.conductor) = χ (a : ZMod N)
  have hu : ((ZMod.unitOfCoprime a ha : (ZMod N)ˣ) : ZMod N) = (a : ZMod N) :=
    ZMod.coe_unitOfCoprime a ha
  conv_rhs => rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, ← hu,
    DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
    ZMod.cast_natCast (DirichletCharacter.conductor_dvd_level χ)]
end Formalism.HC.An
