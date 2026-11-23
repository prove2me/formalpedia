-- Prove2me | solution 1 for Formalism.UG.P.cartan_mem_Ov
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:14.036862+00:00
-- url     : https://prove2.me/submissions/df42e7a4-daef-447b-9ec5-56cf69f0a1ae

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open IsDedekindDomain NumberField
namespace Formalism.UG.P
theorem _root_.solution (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) : x ∈ Ov F v ↔ Valued.v x ≤ 1 := by
  first
  | exact Iff.rfl
  | exact HeightOneSpectrum.mem_adicCompletionIntegers F v
end Formalism.UG.P
