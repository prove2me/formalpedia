-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.prod_eq_sum_dif
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:32.889743+00:00
-- url     : https://prove2.me/submissions/667bf361-8296-4a38-accf-3014a231bfda

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_sum_ebox
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_sum_dif

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
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (R : ι → ℕ → ℝ) (hR : ∀ i, R i 0 = 1) (w : ι →₀ ℕ) :
    w.prod R = ∑ v ∈ ebox w.support w, v.prod (dif R) := by
  rw [sum_ebox (dif R) (fun i => rfl) w.support w, Finsupp.prod]
  exact Finset.prod_congr rfl fun i _ => (sum_dif R hR i (w i)).symm
end Formalism.HermitianLattices.Ext.L3.A5
