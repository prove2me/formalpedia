-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.mem_ebox
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:36.842387+00:00
-- url     : https://prove2.me/submissions/00b26520-cf30-4f64-b226-31cbfdbf85c6

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
theorem _root_.solution {s : Finset ι} {J : ι → ℕ} {v : ι →₀ ℕ} :
    v ∈ ebox s J ↔ v.support ⊆ s ∧ ∀ i ∈ s, v i ≤ J i := by
  classical
  simp [ebox, Finset.mem_finsupp_iff, Nat.lt_succ_iff]
end Formalism.HermitianLattices.Ext.L3.A5
