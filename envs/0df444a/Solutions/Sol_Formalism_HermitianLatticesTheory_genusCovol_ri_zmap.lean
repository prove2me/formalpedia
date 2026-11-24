-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovol_ri_zmap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:49.516257+00:00
-- url     : https://prove2.me/submissions/a98e3037-47e2-4b91-85ce-379e1622eaee

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol

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
theorem _root_.solution (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)) (hinj : Function.Injective ι)
    (A B : Submodule (𝓞 K) V) :
    (zmap ι A).toAddSubgroup.relIndex (zmap ι B).toAddSubgroup =
      A.toAddSubgroup.relIndex B.toAddSubgroup := by
  unfold zmap
  rw [AddSubgroup.toIntSubmodule_toAddSubgroup, AddSubgroup.toIntSubmodule_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
end Formalism.HermitianLatticesTheory
