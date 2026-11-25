-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Br.latLocGlob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:11:17.735913+00:00
-- url     : https://prove2.me/submissions/6eba7746-d3ee-4986-be0e-1f4f253a48a2

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_BlockActions_LatSOfMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_BlockActions_FiniteAdeleRingNontrivial
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Br_latLocGlob_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Br
namespace Formalism.L2.GlobalTheoryTheory.Br
theorem _root_.solution : LatLocGlob := by
  intro F E _ _ _ _ _ n Λ hfin x hx
  exact latLocGlob_main Λ hfin x hx
end Formalism.L2.GlobalTheoryTheory.Br
