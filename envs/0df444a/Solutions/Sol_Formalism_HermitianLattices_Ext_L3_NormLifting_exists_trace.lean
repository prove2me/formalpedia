-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormLifting.exists_trace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:15.866672+00:00
-- url     : https://prove2.me/submissions/f550e40a-b6e6-4e50-86df-84a1c9716ee7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_mem_fixSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_map_inv_eq_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormLifting
variable {A : Type*} [CommRing A] (σ : A →+* A) (I : Ideal A)
variable {σ I}
namespace Formalism.HermitianLattices.Ext.L3.NormLifting
theorem _root_.solution (hσ : ∀ a, σ (σ a) = a) {θ e : A} (he : (θ - σ θ) * e = 1) {w : A}
    (hw : w ∈ fixSub σ I) : ∃ v ∈ I, v + σ v = w := by

  have hw' := (mem_fixSub σ I).mp hw
  refine ⟨w * (θ * e), I.mul_mem_right _ hw'.1, ?_⟩
  rw [map_mul, map_mul, hw'.2, map_inv_eq_neg hσ he]
  linear_combination w * he
end Formalism.HermitianLattices.Ext.L3.NormLifting
