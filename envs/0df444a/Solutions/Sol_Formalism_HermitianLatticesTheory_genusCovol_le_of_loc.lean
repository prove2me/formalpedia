-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovol_le_of_loc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:56.5404+00:00
-- url     : https://prove2.me/submissions/c12b249e-bd96-4d56-afce-cfa15354b839

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
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {Y X : Submodule R W}
    (h : ∀ (P : Ideal R) [P.IsMaximal], Y ≤ locS P.primeCompl X) : Y ≤ X := by
  intro y hy
  let I : Ideal R := X.comap (LinearMap.toSpanSingleton R W y)
  by_cases hI : I = ⊤
  · have : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    simpa [I] using this
  · obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨s, hs, hsy⟩ := h P hy
    exact absurd (hIP (show s ∈ I by simpa [I] using hsy)) hs
end Formalism.HermitianLatticesTheory
