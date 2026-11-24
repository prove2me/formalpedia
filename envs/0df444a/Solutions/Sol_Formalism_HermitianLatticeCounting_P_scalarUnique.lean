-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.scalarUnique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:52.129546+00:00
-- url     : https://prove2.me/submissions/e5b1d94a-f43f-458d-81a5-6550257f7c13

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lastVectorNotMemSup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.NFCUnique := by
  intro K V _ _ _ _ H r F F' c₁ c₂ h₁ h₂
  by_contra hne
  have h3 : (c₂ - c₁) • F.z ∈ F.X ⊔ F'.X := by
    have := Submodule.sub_mem _ h₁ h₂
    convert this using 1
    rw [sub_smul]
    abel
  exact lastVectorNotMemSup K V H r F F' ((Submodule.smul_mem_iff _ (sub_ne_zero.2 (Ne.symm hne))).1 h3)
end Formalism.HermitianLatticeCounting.P
