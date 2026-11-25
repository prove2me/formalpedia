-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RealCovolume.volume_boxC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:21:09.453383+00:00
-- url     : https://prove2.me/submissions/d799e60c-c0ba-4271-852a-59dab98f0bb2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_RealCovolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RealCovolume
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
namespace Formalism.L2.SG.Pf.RealCovolume
theorem _root_.solution : volume boxC = 1 := by
  have h : boxC = Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z
    first
    | exact Iff.rfl
    | simp [boxC, Complex.measurableEquivRealProd, Complex.equivRealProdCLM]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ico]
  simp
end Formalism.L2.SG.Pf.RealCovolume
