-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovol_loc_eq_of_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:57.181455+00:00
-- url     : https://prove2.me/submissions/7990160d-4a90-402a-b40e-1e5f805dc29a

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_locS_mono
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_locS_idem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (S : Submonoid R) {X Z : Submodule R W} (h1 : X ≤ Z)
    (h2 : Z ≤ locS S X) : locS S Z = locS S X :=
  le_antisymm ((genusCovol_locS_mono S h2).trans (genusCovol_locS_idem S X))
    (genusCovol_locS_mono S h1)
end Formalism.HermitianLatticesTheory
