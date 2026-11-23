-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.exampleZ_len_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:03.522789+00:00
-- url     : https://prove2.me/submissions/62691d73-83f9-4616-bdce-e1f7b5eb5258

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ExampleZ

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
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℤ M] (N : Submodule ℤ M)
    (hN : N = ⊤) : (Module.length ℤ (M ⧸ N)).toNat = 0 := by
  subst hN
  rw [Module.length_eq_zero_iff.mpr inferInstance]
  rfl
end Formalism.HermitianLatticesTheory
