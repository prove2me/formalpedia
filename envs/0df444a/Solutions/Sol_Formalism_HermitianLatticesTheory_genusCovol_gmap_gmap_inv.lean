-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovol_gmap_gmap_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:56.133409+00:00
-- url     : https://prove2.me/submissions/eb6ed74e-8b1a-43ad-946a-21c503848fc9

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_gmap_inv


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
theorem _root_.solution (g : V ≃ₗ[K] V) (Z : Submodule (𝓞 K) V) :
    gmap g (gmap g⁻¹ Z) = Z := by
  have := genusBasic_gmap_inv g⁻¹ Z
  rwa [inv_inv] at this
end Formalism.HermitianLatticesTheory
