-- Prove2me | solution 1 for Formalism.G0.AllButLESmithP.pow_succ_dvd_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:21.904058+00:00
-- url     : https://prove2.me/submissions/7745cb0e-3477-4048-98b5-ae516d638ce4

import Definitions.Def_Formalism_SubspaceCounting_StatementD
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_AllButLESmith

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.G0
open Formalism.G0.AllButLESmithP
variable {O M ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [AddCommGroup M] [Module O M] [Fintype ι]
namespace Formalism.G0.AllButLESmithP
theorem _root_.solution {π : O} (hπ : Irreducible π) {a : O} {E : ℕ}
    (h : ¬ a ∣ π ^ E) : π ^ (E + 1) ∣ a := by
  by_cases ha : a = 0
  · simp [ha]
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  by_contra hc
  apply h
  have hk : k ≤ E := by
    by_contra hk
    apply hc
    rw [hu]
    exact Dvd.dvd.mul_left (pow_dvd_pow π (not_le.mp hk)) _
  rw [hu]
  exact (Units.mul_left_dvd).mpr (pow_dvd_pow π hk)
end Formalism.G0.AllButLESmithP
