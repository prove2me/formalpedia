-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.sum_ebox
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:37.065092+00:00
-- url     : https://prove2.me/submissions/2e5f115a-8435-47c3-ad73-8068b49920f7

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
theorem _root_.solution (f : ι → ℕ → ℝ) (hf : ∀ i, f i 0 = 1) (s : Finset ι) (J : ι → ℕ) :
    ∑ v ∈ ebox s J, v.prod f = ∏ i ∈ s, ∑ j ∈ range (J i + 1), f i j := by
  classical
  rw [Finset.prod_sum, ebox, Finset.finsupp, Finset.sum_map]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Finsupp.prod_of_support_subset _ (Finsupp.support_indicator_subset s g) _ (fun i _ => hf i),
    ← Finset.prod_attach s]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finsupp.indicator_apply, dif_pos i.2]
end Formalism.HermitianLattices.Ext.L3.A5
