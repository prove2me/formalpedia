-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BlockStartPoints.diag_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:22.335853+00:00
-- url     : https://prove2.me/submissions/b9e01d9e-a836-4e72-9f4b-f47f5c81ce1e

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockStartPoints
import Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_psd_sum_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_psd_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BlockStartPoints
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
open Classical
noncomputable section
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.BlockStartPoints
theorem _root_.solution (D : Data E W) (hG : D.GramPSD) (hK : D.KernelPSD) (hW : D.WordsPos) (ε : ℝ)
    (hε : 0 < ε) (i s : ℕ) (w : W) (Y : Finset (Pt E)) (t : E) :
    0 ≤ (D.Nst ε i s w Y (blk (D.Kr i) s t t) t t).re := by
  unfold Data.Nst
  rw [Complex.div_ofReal_re]
  refine div_nonneg ?_ (hW w).le
  exact psd_sum_nonneg Y _ (fun h h' => D.gram ε i w (join h s t) (join h' s t))
    (psd_comp Y (Y.image fun h => join h s t) (fun h => join h s t)
      (fun a ha => mem_image_of_mem _ ha) _ (hK.1 i _))
    (psd_comp Y (Y.image fun h => join h s t) (fun h => join h s t)
      (fun a ha => mem_image_of_mem _ ha) _ (hG ε hε i w _))
end Formalism.FourierDecayAlt.P.BlockStartPoints
