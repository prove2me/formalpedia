-- Prove2me | solution 1 for Formalism.UG.P.afsplitI_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:47.120883+00:00
-- url     : https://prove2.me/submissions/fda4d584-4ac3-44fc-b3bc-c9dc247db178

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitA
import Theorems.Thm_Formalism_UG_P_afsplitI_self
import Theorems.Thm_Formalism_UG_P_afsplitI_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
namespace Formalism.UG.P
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (a : 𝔸) :
    afsplitI v (a v) = afsplitI v 1 * a := by
  ext w
  by_cases h : w = v
  · subst h; simp only [afsplit_mul_apply, afsplitI_self, one_mul]
  · simp only [afsplit_mul_apply, afsplitI_ne v w h, zero_mul]
end Formalism.UG.P
