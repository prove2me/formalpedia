-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovol_gmap_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:48.126406+00:00
-- url     : https://prove2.me/submissions/b8d5eecd-e672-4a11-a498-ef34d8bcca24

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_gmap


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
theorem _root_.solution (g : V ≃ₗ[K] V) (A B : Submodule (𝓞 K) V) :
    gmap g (A ⊓ B) = gmap g A ⊓ gmap g B := by
  ext x
  simp only [isomAct_mem_gmap, Submodule.mem_inf]
end Formalism.HermitianLatticesTheory
