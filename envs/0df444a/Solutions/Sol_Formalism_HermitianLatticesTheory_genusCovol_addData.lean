-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovol_addData
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:46.226599+00:00
-- url     : https://prove2.me/submissions/35b85ccb-3de4-48e7-8614-a9077cb42220

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
theorem _root_.solution (g : V ≃ₗ[K] V) (X Y : Submodule (𝓞 K) V) (hXY : gmap g X = Y) :
    X.toAddSubgroup.map (((g : V →ₗ[K] V).restrictScalars (𝓞 K) : V →ₗ[𝓞 K] V) : V →+ V) =
      Y.toAddSubgroup := by
  rw [← hXY]
  rfl
end Formalism.HermitianLatticesTheory
