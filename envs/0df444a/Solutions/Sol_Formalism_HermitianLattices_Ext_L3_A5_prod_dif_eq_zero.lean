-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.prod_dif_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:38.103799+00:00
-- url     : https://prove2.me/submissions/077c4441-7c8b-47fc-97b2-192b029a8a81

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
theorem _root_.solution {R : ι → ℕ → ℝ} {v : ι →₀ ℕ} {i : ι} (hi : i ∈ v.support)
    (hR : ∀ j, R i j = 1) : v.prod (dif R) = 0 := by
  unfold Finsupp.prod
  refine Finset.prod_eq_zero hi ?_
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  rw [hk]
  show R i (k + 1) - R i k = 0
  rw [hR, hR, sub_self]
end Formalism.HermitianLattices.Ext.L3.A5
