-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.lifting_fixes_base_vector
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:34.360813+00:00
-- url     : https://prove2.me/submissions/b9740d1e-88de-4b8b-9d77-02c80afdbe0c

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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.LiftUnitaryFixesBase := by
  intro K V _ _ _ _ H r F F' Wt g hL hg
  have h0 : ∀ y ∈ V0 F F', g y = y := fun y hy => hg.2 y (fun w hw => hL.1 w hw y hy)
  exact ⟨h0, fun a => h0 _ (flag_vector_mem_base_lattice F F' a), fun a => h0 _ (hermFlag_secondFrame_mem_frameSpan F F' a)⟩
end Formalism.HermitianLatticeCounting.P
