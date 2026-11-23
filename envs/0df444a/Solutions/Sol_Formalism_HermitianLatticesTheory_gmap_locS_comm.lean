-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.gmap_locS_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:43.634291+00:00
-- url     : https://prove2.me/submissions/8923d9a4-d508-4656-b139-a8e009bd8a15

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
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_smul


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
theorem _root_.solution (g : V ≃ₗ[K] V) (S : Submonoid (𝓞 K)) (Z : Submodule (𝓞 K) V) :
    gmap g (locS S Z) = locS S (gmap g Z) := by
  ext x
  rw [isomAct_mem_gmap, isomAct_mem_locS, isomAct_mem_locS]
  simp only [isomAct_mem_gmap]
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [isomAct_smul]; exact hx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← isomAct_smul]; exact hx⟩
end Formalism.HermitianLatticesTheory
