-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.SplitEmbedding.swap_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:51:04.381677+00:00
-- url     : https://prove2.me/submissions/6a03ec0e-4e85-4967-b75b-7b3f4395d1d4

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdBisForm_Imports
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_SwapMp
import Theorems.Thm_Bl_general_b_fact_third_bis_form_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasurableSpace Set
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding
namespace Formalism.L2.SG.NGCut.SplitEmbedding
theorem _root_.solution {ι P β : Type} [Fintype ι] [Fintype P] [MeasurableSpace β] (μ0 : Measure β) [SigmaFinite μ0] :
    MeasurePreserving (fun (x : ι → P → β) (p : P) (v : ι) => x v p)
      (Measure.pi fun _ : ι => Measure.pi fun _ : P => μ0) (Measure.pi fun _ : P => Measure.pi fun _ : ι => μ0) := by
  first | exact Bl.general_b_fact_third_bis_form.goal1 .. | (apply Bl.general_b_fact_third_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_bis_form.goal1 <;> assumption)
end Formalism.L2.SG.NGCut.SplitEmbedding
