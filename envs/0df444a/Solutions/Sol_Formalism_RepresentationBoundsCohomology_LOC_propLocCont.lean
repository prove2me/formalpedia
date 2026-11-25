-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.propLocCont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:22:25.601388+00:00
-- url     : https://prove2.me/submissions/e8f9d842-36e1-4df5-88e0-b6ce71cc7714

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_PropLoc
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ConnTors
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_HOneTorsionFree
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ExistsPowSmulIntegral
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ExistsBasisOfLattice
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_PropLocContOfLattices
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_propLocCont_of_lattices
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_dualLattice
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_quotEmbeds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution : StatPropLocCont.{u} := propLocCont_of_lattices quotEmbeds dualLattice
end Formalism.RepresentationBoundsCohomology.LOC
