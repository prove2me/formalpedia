-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.lifting_anisotropic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:33.876492+00:00
-- url     : https://prove2.me/submissions/7fac7bbe-4139-478a-92b8-7d08fbc97bca

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_CellDecomposition_flag_vector_mem_base_lattice
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_CellDecomposition_hermFlag_secondFrame_mem_frameSpan

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
open CellDecomposition
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.LiftAniso := by
  intro K V _ _ _ _ H r F F' Wt hA hA' hL w hw hww
  have h1 : w ∈ F.X := hA w (fun a => hL.1 w hw _ (flag_vector_mem_base_lattice F F' a)) hww
  have h2 : w ∈ F'.X := hA' w (fun a => hL.1 w hw _ (hermFlag_secondFrame_mem_frameSpan F F' a)) hww
  have : w ∈ Wt ⊓ II F F' := ⟨hw, h1, h2⟩
  rw [hL.2.1] at this
  exact (Submodule.mem_bot K).1 this
end Formalism.HermitianLatticeCounting.P
