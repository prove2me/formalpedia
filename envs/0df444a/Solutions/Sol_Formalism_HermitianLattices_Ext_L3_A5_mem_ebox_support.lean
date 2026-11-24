-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.mem_ebox_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:53.131795+00:00
-- url     : https://prove2.me/submissions/1fe59bdf-d426-4494-824c-933bce12b148

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_mem_ebox

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
theorem _root_.solution {v w : ι →₀ ℕ} : v ∈ ebox w.support w ↔ v ≤ w := by
  rw [mem_ebox, Finsupp.le_def]
  constructor
  · rintro ⟨hs, hle⟩ i
    by_cases hi : i ∈ w.support
    · exact hle i hi
    · have h0 : v i = 0 := by
        by_contra h
        exact hi (hs (Finsupp.mem_support_iff.mpr h))
      rw [h0]
      exact Nat.zero_le _
  · intro h
    refine ⟨fun i hi => ?_, fun i _ => h i⟩
    rw [Finsupp.mem_support_iff] at hi ⊢
    have := h i
    omega
end Formalism.HermitianLattices.Ext.L3.A5
