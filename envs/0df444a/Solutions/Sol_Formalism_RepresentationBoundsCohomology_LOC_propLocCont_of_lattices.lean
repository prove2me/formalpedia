-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.propLocCont_of_lattices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:53:16.906192+00:00
-- url     : https://prove2.me/submissions/5333b6cb-7ddc-46c0-9724-23f4d6320199

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_PropLoc
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ConnTors
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_HOneTorsionFree
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ExistsPowSmulIntegral
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ExistsBasisOfLattice
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_PropLocContOfLattices
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_connTors
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_propLocCont_of


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
theorem _root_.solution (hEmb : StatQuotEmbeds.{u}) (hDual : StatDualLattice.{u}) :
    StatPropLocCont.{u} := propLocCont_of connTors hEmb hDual
end Formalism.RepresentationBoundsCohomology.LOC
