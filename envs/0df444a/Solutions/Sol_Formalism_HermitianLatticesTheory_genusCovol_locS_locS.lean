-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovol_locS_locS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:56.875208+00:00
-- url     : https://prove2.me/submissions/61daffab-441d-485b-b0f7-fe27d5603b7f

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_le_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_locS_mono
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_locS_idem
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_le_of_le


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
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    {S T : Submonoid R} (hST : S ≤ T) (Z : Submodule R W) : locS T (locS S Z) = locS T Z :=
  le_antisymm ((genusCovol_locS_mono T (locBasic_locS_le_of_le hST Z)).trans
    (genusCovol_locS_idem T Z)) (genusCovol_locS_mono T (genusCovol_le_locS S Z))
end Formalism.HermitianLatticesTheory
