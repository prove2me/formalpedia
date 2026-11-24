-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.nrm_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:03.180739+00:00
-- url     : https://prove2.me/submissions/39962423-643f-4425-b2fe-46f404461ec4

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
variable {q : ι → ℝ}
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (hq : ∀ i, 2 ≤ q i) (v : ι →₀ ℕ) : 0 < nrm q v := by
  unfold nrm Finsupp.prod
  exact Finset.prod_pos fun i _ => pow_pos (by linarith [hq i]) _
end Formalism.HermitianLattices.Ext.L3.A5
