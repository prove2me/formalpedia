-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.abs_div_nrm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:52.263287+00:00
-- url     : https://prove2.me/submissions/fc9edd28-4dfb-410c-87f2-e8cf11b5a3fc

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
theorem _root_.solution (f : ι → ℕ → ℝ) (v : ι →₀ ℕ) :
    |v.prod f| / nrm q v = v.prod fun i e => |f i e| / q i ^ e := by
  unfold nrm Finsupp.prod
  rw [Finset.abs_prod, ← Finset.prod_div_distrib]
end Formalism.HermitianLattices.Ext.L3.A5
