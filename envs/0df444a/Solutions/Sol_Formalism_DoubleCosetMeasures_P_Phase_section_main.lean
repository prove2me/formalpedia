-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.section_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:37.08134+00:00
-- url     : https://prove2.me/submissions/2ca88f9b-1197-4567-93e6-a1f4d66d2530

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_section_exists
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_section_unique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
open Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K]
namespace Formalism.DoubleCosetMeasures.P.Phase
theorem _root_.solution : SectionBij := by
  unfold SectionBij
  intro K _ s t x y hx hy
  obtain ⟨v, u, h, hv, hh, hvw, hu, heq⟩ := section_exists s t hx hy
  refine ⟨(v, u), ⟨⟨hv, h, hh, hvw⟩, hu, heq⟩, ?_⟩
  rintro ⟨v', u'⟩ ⟨⟨hv', h', hh', hvw'⟩, hu', heq'⟩
  obtain ⟨e1, e2⟩ := section_unique s t hh hh' hu hu' hvw hvw' (heq'.trans heq.symm)
  simp only [Prod.mk.injEq]
  exact ⟨e1, e2⟩
end Formalism.DoubleCosetMeasures.P.Phase
