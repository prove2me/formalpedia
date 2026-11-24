-- Prove2me | solution 1 for Formalism.L2.DIV.b_eps_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:56:10.8704+00:00
-- url     : https://prove2.me/submissions/565f005b-857c-4158-952b-cd6b963c3035

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_mem_suppAt
import Theorems.Thm_Formalism_L2_DIV_b_eps_mul

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (u : (RInt F E)ˣ)
    (hu : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v) :
    bEps E v * ((u : RInt F E) - 1) = (u : RInt F E) - 1 := by
  apply Subtype.ext
  apply b_eps_mul v
  intro v' hv'
  have := (b_mem_suppAt v _).mp hu v' hv'
  show prV (E := E) v' (((u : RInt F E) : AfE F E) - 1) = 0
  rw [map_sub, map_one, sub_eq_zero]
  exact this
end Formalism.L2.DIV
