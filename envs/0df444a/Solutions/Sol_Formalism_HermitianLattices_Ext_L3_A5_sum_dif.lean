-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.sum_dif
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:38.222241+00:00
-- url     : https://prove2.me/submissions/4d37c0a7-7373-444e-b289-b681778e5089

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom

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
theorem _root_.solution (R : ι → ℕ → ℝ) (hR : ∀ i, R i 0 = 1) (i : ι) (J : ℕ) :
    ∑ j ∈ range (J + 1), dif R i j = R i J := by
  induction J with
  | zero => simp [dif, hR]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    simp [dif]
end Formalism.HermitianLattices.Ext.L3.A5
