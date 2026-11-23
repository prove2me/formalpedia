-- Prove2me | solution 1 for Formalism.CyclotomicNorms.repr_diag_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:12.861712+00:00
-- url     : https://prove2.me/submissions/2fa93d26-e86c-424c-9900-3dbfb294914f

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PowerPCycle
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_RestrictionOfBlocksAndJordan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open Formalism Formalism.CyclotomicNorms
variable {G k V : Type} [Group G] [Field k] [AddCommGroup V] [Module k V] {N : ℕ}
namespace Formalism.CyclotomicNorms
theorem _root_.solution (ρ : Representation k G V) (e : Module.Basis (Fin N) k V)
    (χ : Fin N → G → k) (y : G) (hy : ∀ i, ρ y (e i) = χ i y • e i) (v : V) (m : Fin N) :
    e.repr (ρ y v) m = χ m y * e.repr v m := by
  have h : ρ y v = ∑ i, (e.repr v i * χ i y) • e i := by
    conv_lhs => rw [← e.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hy, smul_smul]
  rw [h, e.repr_sum_self]
  exact mul_comm _ _
end Formalism.CyclotomicNorms
