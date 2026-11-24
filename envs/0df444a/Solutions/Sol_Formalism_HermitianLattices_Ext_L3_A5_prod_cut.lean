-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.prod_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:35.972662+00:00
-- url     : https://prove2.me/submissions/7fa2efe1-8d7f-49f1-9f98-1c4ef750c85a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoWeightedTprod

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
variable {ι X : Type*} {q : ι → ℝ}
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution {ρ : ι → ℕ → ℝ} (hρ0 : ∀ i, ρ i 0 = 1) (S' : Finset ι) (w : ι →₀ ℕ) :
    w.prod (cut ρ S') = ∏ i ∈ S', ρ i (w i) := by
  classical
  have hg : ∀ i ∈ w.support ∪ S', cut ρ S' i 0 = 1 := fun i _ => by simp [cut, hρ0]
  rw [Finsupp.prod_of_support_subset w (s := w.support ∪ S') Finset.subset_union_left
    (cut ρ S') hg]
  symm
  calc ∏ i ∈ S', ρ i (w i) = ∏ i ∈ S', cut ρ S' i (w i) :=
        Finset.prod_congr rfl fun i hi => by simp [cut, hi]
    _ = ∏ i ∈ w.support ∪ S', cut ρ S' i (w i) :=
        Finset.prod_subset Finset.subset_union_right fun i _ hiS => by simp [cut, hiS]
end Formalism.HermitianLattices.Ext.L3.A5
