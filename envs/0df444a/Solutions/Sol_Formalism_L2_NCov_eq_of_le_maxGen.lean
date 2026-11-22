-- Prove2me | solution 1 for Formalism.L2.NCov.eq_of_le_maxGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:37:10.000976+00:00
-- url     : https://prove2.me/submissions/c33c938c-2282-4a4e-93aa-57c19b304c21

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
theorem _root_.solution {W : Submodule K V} (hW : W ≠ ⊥) {f : End K V} {a b : K}
    (ha : W ≤ f.maxGenEigenspace a) (hb : W ≤ f.maxGenEigenspace b) : a = b := by
  by_contra hab
  exact hW (disjoint_self.1 ((f.disjoint_genEigenspace hab ⊤ ⊤).mono ha hb))
end Formalism.L2.NCov
