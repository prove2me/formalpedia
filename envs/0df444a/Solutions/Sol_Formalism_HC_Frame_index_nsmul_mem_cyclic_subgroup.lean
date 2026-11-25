-- Prove2me | solution 1 for Formalism.HC.Frame.index_nsmul_mem_cyclic_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:05:27.395685+00:00
-- url     : https://prove2.me/submissions/3d77fb08-acf3-49ee-ba60-f811d6d4d0a1

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_index_A0_eq_o
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
private theorem o_smul_mem_A0 (t : φ.A) : φ.o • t ∈ φ.A0 := by
  rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, ← φ.index_A0_eq_o,
    AddSubgroup.index_eq_card]
  exact card_nsmul_eq_zero'
end Formalism.HC.Frame
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
namespace Formalism.HC.Frame
theorem _root_.solution (t : φ.A) : φ.o • t ∈ φ.A0 := o_smul_mem_A0 φ t
end Formalism.HC.Frame
