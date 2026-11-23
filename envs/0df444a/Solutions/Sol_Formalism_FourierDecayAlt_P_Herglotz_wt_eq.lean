-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Herglotz.wt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:58.292498+00:00
-- url     : https://prove2.me/submissions/cee25e2b-9936-4ae9-85e8-3555ec4b464d

import Definitions.Def_Formalism_HermitianCurvature_StatementH
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_count_box

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Herglotz
open Real Filter Topology Finset
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.Herglotz
theorem _root_.solution (N : ℕ) (hN : N ≠ 0) (τ : Fin d → ℤ) :
    (((N : ℝ) ^ d)⁻¹ * (((box d N ×ˢ box d N).filter (fun p => p.1 - p.2 = τ)).card : ℝ))
      = wt N τ := by
  rw [count_box]
  unfold wt fac
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rw [inv_mul_eq_div]
end Formalism.FourierDecayAlt.P.Herglotz
