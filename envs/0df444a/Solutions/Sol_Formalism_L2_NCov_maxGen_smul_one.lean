-- Prove2me | solution 1 for Formalism.L2.NCov.maxGen_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:46:28.662593+00:00
-- url     : https://prove2.me/submissions/67074fb1-73c7-4514-a79f-315afc363844

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.NCov
open Module Module.End
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
namespace Formalism.L2.NCov
theorem _root_.solution (c : K) : (c • (1 : End K V)).maxGenEigenspace c = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [mem_maxGenEigenspace]
  exact ⟨1, by simp⟩
end Formalism.L2.NCov
