-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RealCovolume.Qf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:17:11.934918+00:00
-- url     : https://prove2.me/submissions/102a5792-d065-4f8f-88de-829fbe8b7857

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_RealCovolume
import Theorems.Thm_Formalism_L2_SG_Pf_RealCovolume_reCo_apply

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
theorem _root_.solution (g : κ → ℝ) (a b : ι → κ → ℂ) :
    Qf g a b = ∑ p : ι × κ × Fin 2, reCo a p * reCo b p * g p.2.1 := by
  simp only [Qf, Fintype.sum_prod_type, Fin.sum_univ_two, reCo_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
  simp [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im] <;> ring
end Formalism.L2.SG.Pf.RealCovolume
