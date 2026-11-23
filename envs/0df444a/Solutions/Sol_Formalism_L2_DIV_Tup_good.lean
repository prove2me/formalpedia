-- Prove2me | solution 1 for Formalism.L2.DIV.Tup.good
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:36.11229+00:00
-- url     : https://prove2.me/submissions/3e5e180e-b9b1-42f0-bb85-19baaa8cd511

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Theorems.Thm_Formalism_L2_DIV_mem_tupGrp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism Formalism.L2 Formalism.L2.DIV
namespace Formalism.L2.DIV
namespace Tup
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
    {S : Set ℕ} (ξ : Tup F E L S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ Qprime (ξ : Chr F E L)) : GoodPl E S v := by
  by_contra hg
  exact hv (((mem_tupGrp (ξ : Chr F E L)).mp ξ.2).2.2.2 v hg)
end Tup
end Formalism.L2.DIV
