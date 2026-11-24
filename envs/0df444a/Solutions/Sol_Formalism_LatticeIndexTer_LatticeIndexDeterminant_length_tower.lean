-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexDeterminant.length_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:35:12.285055+00:00
-- url     : https://prove2.me/submissions/917b5d42-84ed-4561-805a-0eb77fad2c5a

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Theorems.Thm_Bl_DiscreteValuationQuotients_goal1
import Theorems.Thm_P2M_Bl_general_b_fact_second____goal1_4dd01fbd6af8


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.LatticeIndexTer Formalism.LatticeIndexTer.LatticeIndexDeterminant
namespace Formalism.LatticeIndexTer.LatticeIndexDeterminant
theorem _root_.solution {O Y : Type*} [CommRing O] [AddCommGroup Y] [Module O Y]
    (R S D E : Submodule O Y) (hD : ∀ y, y ∈ D ↔ y ∈ R ∧ y ∈ S) (hE : E ≤ D) :
    Module.length O (R ⧸ E.comap R.subtype) =
      Module.length O (R ⧸ S.comap R.subtype) + Module.length O (D ⧸ E.comap D.subtype) := by
  first | exact Bl.general_b_fact_second'''.goal1 .. | (apply Bl.general_b_fact_second'''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second'''.goal1 <;> assumption)
end Formalism.LatticeIndexTer.LatticeIndexDeterminant
