-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.prod_dif_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:36.428539+00:00
-- url     : https://prove2.me/submissions/bf296036-894d-4dc8-b64c-8c29a21cbefa

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
open scoped Classical
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (ρ : ι → ℕ → ℝ) (S' : Finset ι) (v : ι →₀ ℕ) :
    v.prod (dif (cut ρ S')) = if v.support ⊆ S' then v.prod (dif ρ) else 0 := by
  split_ifs with h
  · unfold Finsupp.prod
    refine Finset.prod_congr rfl fun i hi => ?_
    have hiS : i ∈ S' := h hi
    cases v i with
    | zero => rfl
    | succ k =>
      show cut ρ S' i (k + 1) - cut ρ S' i k = ρ i (k + 1) - ρ i k
      simp [cut, hiS]
  · obtain ⟨i, hi, hiS⟩ := Finset.not_subset.mp h
    unfold Finsupp.prod
    refine Finset.prod_eq_zero hi ?_
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    rw [hk]
    show cut ρ S' i (k + 1) - cut ρ S' i k = 0
    simp [cut, hiS]
end Formalism.HermitianLattices.Ext.L3.A5
