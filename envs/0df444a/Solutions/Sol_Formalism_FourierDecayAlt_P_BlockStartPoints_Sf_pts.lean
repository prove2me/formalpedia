-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BlockStartPoints.Sf_pts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:22.249798+00:00
-- url     : https://prove2.me/submissions/36f84165-c96a-4cc1-a628-7093164070e3

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockStartPoints
import Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_sum_pts

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
theorem _root_.solution (D : Data E W) (ε : ℝ) (i s : ℕ) (w : W) (Y : Finset (Pt E)) (S : Finset E) :
    D.Sf ε i w (pts Y s S) / D.wt w =
      ∑ t ∈ S, ∑ t' ∈ S, (D.Nst ε i s w Y (blk (D.Kr i) s t t') t t').re := by
  unfold Data.Sf Data.Nst
  rw [sum_pts]
  simp_rw [sum_pts, Complex.div_ofReal_re, Complex.re_sum, blk]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm, Finset.sum_div]
end Formalism.FourierDecayAlt.P.BlockStartPoints
