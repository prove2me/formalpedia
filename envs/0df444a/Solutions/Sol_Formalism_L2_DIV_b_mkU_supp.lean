-- Prove2me | solution 1 for Formalism.L2.DIV.b_mkU_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:56:11.587939+00:00
-- url     : https://prove2.me/submissions/c7994dc0-ab37-4301-95ca-cfd5804a991d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_mem_suppAt
import Theorems.Thm_Formalism_UG_P_afsplit_prV_eps_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.DIV
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (b : 𝓞 E) (u : (RInt F E)ˣ)
    (hu : (u : RInt F E) = toRInt F E b * bEps E v + (1 - bEps E v)) :
    Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v := by
  rw [b_mem_suppAt]
  intro v' hv'
  show prV (E := E) v' ((u : RInt F E) : AfE F E) = 1
  rw [hu]
  show prV (E := E) v' (((toRInt F E b : RInt F E) : AfE F E) * afsplitEps E v + (1 - afsplitEps E v)) = 1
  rw [map_add, map_mul, map_sub, afsplit_prV_eps_ne v v' hv', mul_zero, map_one, sub_zero, zero_add]
end Formalism.L2.DIV
