-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetFinite_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:10:58.86489+00:00
-- url     : https://prove2.me/submissions/9252484b-0314-4dfd-a6d5-02563babb711

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetFinite_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (hA : TraceReal) (hB : GenusCovolBound) (hC : ShortVectors)
    (hD : GenusScale) (hE : FinIntermediate) (hF : IsomOfTrace) : ClassSetFinite := by
  unfold ClassSetFinite
  unfold TraceReal at hA
  unfold GenusCovolBound at hB
  unfold GenusScale at hD
  intro K V _ _ _ _ _ _ _ _ h hsymm hpos L hL
  obtain ⟨N, ι, hι, hmul, hlat⟩ := hA K V h hsymm hpos
  obtain ⟨C, hCb⟩ := hB K V h hsymm hpos N ι hι L hL
  obtain ⟨d, hd, hdM⟩ := hD K V h hsymm L hL
  exact classSetFinite_core hC hE hF h hpos N ι hι hmul d hd C
    (genus h L) hdM (fun M hM => hlat M hM.1) hCb
end Formalism.HermitianLatticesTheory
