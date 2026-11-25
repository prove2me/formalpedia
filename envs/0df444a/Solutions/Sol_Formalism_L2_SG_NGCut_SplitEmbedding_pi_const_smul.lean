-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.SplitEmbedding.pi_const_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:56:06.65479+00:00
-- url     : https://prove2.me/submissions/1851de91-9b8d-4b58-a3f0-e89cc2c1ecec

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_BoxFundT
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_SwapMp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MeasurablePhiInv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_EmbSInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding
namespace Formalism.L2.SG.NGCut.SplitEmbedding
theorem _root_.solution {ι : Type} [Fintype ι] (x : ℝ) :
    Measure.pi (fun _ : ι => ENNReal.ofReal x • (volume : Measure ℂ)) =
      ENNReal.ofReal x ^ Fintype.card ι • (volume : Measure (ι → ℂ)) := by
  have hsf : SigmaFinite (ENNReal.ofReal x • (volume : Measure ℂ)) :=
    (inferInstance : SigmaFinite (x.toNNReal • (volume : Measure ℂ)))
  refine Measure.pi_eq (fun t _ => ?_)
  rw [Measure.smul_apply, volume_pi, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]
end Formalism.L2.SG.NGCut.SplitEmbedding
