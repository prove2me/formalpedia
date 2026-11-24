-- Prove2me | solution 1 for Formalism.L2.NCov.commute_sub_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:04.279823+00:00
-- url     : https://prove2.me/submissions/b77a8639-1d2b-44f6-8249-e864e59d97ff

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
theorem _root_.solution {A B : End K V} (h : Commute A B) (a b : K) :
    Commute (A - a • 1) (B - b • 1) :=
  Commute.sub_left (Commute.sub_right h ((Commute.one_right A).smul_right b))
    ((Commute.one_left _).smul_left a)
end Formalism.L2.NCov
