-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.summable_dif
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:21.4262+00:00
-- url     : https://prove2.me/submissions/26eea8e5-dabc-4bf7-bedb-d34e0558486b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_summable_prod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_abs_div_nrm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_sum_dif_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {ι : Type*}
variable {q : ι → ℝ}
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (hq : ∀ i, 2 ≤ q i) (hsum : Summable fun i => (q i ^ 2)⁻¹) {R : ι → ℕ → ℝ}
    (hRb : ∀ i j, |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i) :
    Summable fun v : ι →₀ ℕ => |v.prod (dif R)| / nrm q v := by
  have h := summable_prod (u := fun i e => |dif R i e| / q i ^ e) (fun i => by simp [dif])
    (fun i j => div_nonneg (abs_nonneg _) (pow_nonneg (by linarith [hq i]) _))
    (hsum.mul_left cGeom) (fun i J => sum_dif_le hq hRb i J)
  exact h.congr fun v => (abs_div_nrm (dif R) v).symm
end Formalism.HermitianLattices.Ext.L3.A5
