-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ThresholdBounds.v_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:49.381955+00:00
-- url     : https://prove2.me/submissions/c555a9cc-da0a-4759-86e1-f87ae1369cb9

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ThresholdBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace Formalism.L2.SG.Pf.ThresholdBounds
open Formalism.FourierDecayAlt
variable (c : Sz.Cfg)
private theorem v_eq_vlast_add_four_mul_Del (i : ℕ) : c.v i = c.vlast + 4 * c.Del * ((c.k : ℝ) - 1 - (i : ℝ)) := rfl
end Formalism.L2.SG.Pf.ThresholdBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ThresholdBounds
open Formalism.FourierDecayAlt
variable (c : Sz.Cfg)
namespace Formalism.L2.SG.Pf.ThresholdBounds
theorem _root_.solution (i j : ℕ) : c.v i - c.v j = 4 * c.Del * ((j : ℝ) - (i : ℝ)) := by
  rw [v_eq_vlast_add_four_mul_Del c i, v_eq_vlast_add_four_mul_Del c j]; ring
end Formalism.L2.SG.Pf.ThresholdBounds
