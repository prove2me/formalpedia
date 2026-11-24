-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovol_zmap_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:57.721639+00:00
-- url     : https://prove2.me/submissions/35ab27f3-6e8c-4306-ba2d-304810173ed1

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_mem_zmap


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
theorem _root_.solution (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)) {A B : Submodule (𝓞 K) V}
    (hAB : A ≤ B) : zmap ι A ≤ zmap ι B := by
  intro v hv
  obtain ⟨x, hx, rfl⟩ := (genusCovolBound_mem_zmap N ι A v).mp hv
  exact (genusCovolBound_mem_zmap N ι B _).mpr ⟨x, hAB hx, rfl⟩
end Formalism.HermitianLatticesTheory
