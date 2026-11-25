-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLDA.length_self_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:41:39.566965+00:00
-- url     : https://prove2.me/submissions/65e84499-8cfa-44bc-8893-6c152e3b90c6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.TieLDA
open TensorProduct Module
namespace Formalism.L2.Pj.QAt.TieLDA
theorem _root_.solution (T : Type*) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] :
    Module.length T T = ⊤ := by
  by_contra h
  have hfin := Module.length_ne_top_iff.mp h
  have hart : IsArtinianRing T := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  exact IsDiscreteValuationRing.not_isField T (IsArtinianRing.isField_of_isDomain T)
end Formalism.L2.Pj.QAt.TieLDA
