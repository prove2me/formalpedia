-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.exampleZ_len_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:53.526596+00:00
-- url     : https://prove2.me/submissions/eec63aab-32f6-44d9-b23b-fdf788e6a461

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ExampleZ
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_len_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (p : Ideal ℤ) [p.IsPrime] (B : Submodule ℤ ℚ) :
    locLen p B B = 0 := by
  unfold locLen
  exact exampleZ_len_top _ (Submodule.comap_subtype_self _)
end Formalism.HermitianLatticesTheory
